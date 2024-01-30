/*@
function (pointer) copy_alloc_id(u64 x, pointer p) {
    array_shift<char>(p, x - (u64) p)
}

function (u64) pfn_buddy (u64 x, u8 sz)
function (boolean) order_aligned (u64 x, u8 sz)
function (u64) order_align (u64 x, u8 sz)
function (boolean) page_aligned (u64 x, u8 sz)
function (u64) page_size_of_order (u8 sz)

function (u64) page_size () { 4096u64 }
function (u8) max_order () { 11u8 }
function (u8) hyp_no_order () { 255u8 }

function (u64) cn_hyp_page_to_pfn(pointer hypvmemmap, pointer p) {
  ((u64) p - (u64) hypvmemmap) / (u64) (sizeof<struct hyp_page>)
}

// copied and adjusted from the corresponding macro definition in memory.h 
function (u64) cn__hyp_pa(i64 physvirtoffset, pointer virt) {
  (u64) ((i64) virt + physvirtoffset)
}



// copied and adjusted from the corresponding macro definition in memory.h 
function (u64) cn_hyp_phys_to_pfn(u64 phys) {
  phys / page_size()
}

// copied and adjusted from the corresponding macro definition in memory.h 
function (u64) cn_hyp_virt_to_pfn (i64 physvirtoffset, pointer virt) {
  cn_hyp_phys_to_pfn(cn__hyp_pa(physvirtoffset, virt))
}


function (u64) cn_hyp_pfn_to_phys(u64 pfn) {
  pfn*page_size()
}

// copied and adjusted from the corresponding macro definition in memory.h 
function (u64) cn_hyp_page_to_phys(pointer hypvmemmap, pointer page) {
  cn_hyp_pfn_to_phys((cn_hyp_page_to_pfn(hypvmemmap, page)))
}

// copied and adjusted from the corresponding macro definition in memory.h 
function (pointer) cn__hyp_va(pointer virt_ptr, i64 physvirtoffset, u64 phys) {
  copy_alloc_id((u64) ((i64) phys - physvirtoffset), virt_ptr)
}

// copied and adjusted from the corresponding macro definition in memory.h 
function (pointer) cn_hyp_page_to_virt(pointer virt_ptr, i64 physvirtoffset,
                                       pointer hypvmemmap, pointer page) {
  cn__hyp_va(virt_ptr, physvirtoffset, cn_hyp_page_to_phys(hypvmemmap, page))
}


type_synonym excludes = {boolean any, boolean do_ex1, u64 ex1, boolean do_ex2, u64 ex2}

function (boolean) excluded (excludes ex, u64 i)
{
  ex.any && (
      (ex.do_ex1 && (i == ex.ex1))
      || (ex.do_ex2 && (i == ex.ex2))
  )
}

function (excludes) exclude_none ()
{
  {any: 0 < 0, do_ex1: 0 < 0, ex1: 0u64, do_ex2: 0 < 0, ex2: 0u64}
}

function (excludes) exclude_one (u64 ex1)
{
  {any: 0 < 1, do_ex1: 0 < 1, ex1: ex1, do_ex2: 0 < 0, ex2: 0u64}
}

function (excludes) exclude_two (u64 ex1, u64 ex2)
{
  {any: 0 < 1, do_ex1: 0 < 1, ex1: ex1, do_ex2: 0 < 1, ex2: ex2}
}


// Check a pointer (to the struct list_head embedded in a free page) is a valid
// pointer, which includes knowing that its matching vmemmap entry has the
// refcount/order settings that indicate that the struct is present. 
function (boolean) vmemmap_good_pointer (i64 physvirt_offset, pointer p,
        map <u64, struct hyp_page> vmemmap,
        u64 range_start, u64 range_end, excludes ex)
{
  let pa = cn__hyp_pa(physvirt_offset, p);
  let pfn = cn_hyp_phys_to_pfn(pa);
    (mod(pa, page_size ()) == 0u64)
    && (range_start <= pa)
    && (pa < range_end)
    && (vmemmap[pfn].refcount == 0u16)
    && (vmemmap[pfn].order != (hyp_no_order ()))
    && (not (excluded (ex, pfn)))
}


function (boolean) page_group_ok (u64 page_index,
        map <u64, struct hyp_page> vmemmap, struct hyp_pool pool)
{
  let page = vmemmap[page_index];
  let start_i = (pool.range_start) / (page_size ());
  ((page.order == hyp_no_order())
    || (each (u8 i: 1, 10; (not (
        (order_align(page_index, i) < page_index)
        && (start_i <= order_align(page_index, i))
        && (i <= (vmemmap[(order_align(page_index, i))]).order)
        && ((vmemmap[(order_align(page_index, i))]).order != hyp_no_order())
    )))))
}

// There are no `AllocatorPage`s outputs to pass as arguments in `hyp_pool_init`
// Also a different invariant handles checking prev/next
function (boolean) init_vmemmap_page (u64 page_index,
        map <u64, struct hyp_page> vmemmap,
        pointer pool_pointer, struct hyp_pool pool)
{
  let page = vmemmap[page_index];
    (page.order == 0u8)
    && (page.refcount == 1u16)
    && (order_aligned(page_index, 0u8))
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
}

function (boolean) vmemmap_normal_order_wf (u64 page_index, struct hyp_page page, struct hyp_pool pool) {
    (0u8 <= page.order && ((page.order < pool.max_order) && (page.order < max_order())))
    && order_aligned(page_index, page.order)
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
}


function (boolean) vmemmap_wf (u64 page_index,
        map <u64, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  let page = vmemmap[page_index];
    ((page.order == (hyp_no_order ())) || vmemmap_normal_order_wf(page_index, page, pool))
    && ((page.order != hyp_no_order()) || (page.refcount == 0u16))
    && (page_group_ok(page_index, vmemmap, pool))
}

function (boolean) vmemmap_l_wf (u64 page_index, i64 physvirt_offset,
        pointer virt_ptr,
        map <u64, struct hyp_page> vmemmap, map <i64, struct list_head> APs,
        pointer pool_pointer, struct hyp_pool pool, excludes ex)
{
  let page = vmemmap[page_index];
  let self_node_pointer = cn__hyp_va(virt_ptr, physvirt_offset, cn_hyp_pfn_to_phys(page_index));
  let pool_free_area_arr_pointer = member_shift<hyp_pool>(pool_pointer, free_area);
  let pool_free_area_pointer = array_shift<struct list_head>(pool_free_area_arr_pointer, page.order);
  let prev = (APs[page_index]).prev;
  let next = (APs[page_index]).next;
  let free_area_entry = pool.free_area[(u64) page.order];
  let prev_page_pointer = prev;
  let prev_page_index = cn_hyp_virt_to_pfn(physvirt_offset, prev_page_pointer);
  let prev_page = vmemmap[prev_page_index];
  let next_page_pointer = next;
  let next_page_index = cn_hyp_virt_to_pfn(physvirt_offset, next_page_pointer);
  let next_page = vmemmap[next_page_index];
  let prov = (alloc_id) virt_ptr;
  let prev_clause =
    ((prev == pool_free_area_pointer) && (free_area_entry.next == self_node_pointer))
    || (vmemmap_good_pointer (physvirt_offset, prev_page_pointer, vmemmap, pool.range_start, pool.range_end, ex)
        && (prov == (alloc_id) prev)
        && ((APs[prev_page_index]).next == self_node_pointer)
        && (prev_page.order == page.order)
        && (prev_page.refcount == 0u16));
  let next_clause =
    ((next == pool_free_area_pointer) && (free_area_entry.prev == self_node_pointer))
    || (vmemmap_good_pointer (physvirt_offset, next_page_pointer, vmemmap, pool.range_start, pool.range_end, ex)
        && (prov == (alloc_id) next)
        && ((APs[next_page_index]).prev == self_node_pointer)
        && (next_page.order == page.order)
        && (next_page.refcount == 0u16));
  // there is no self-loop case for this node type, as it is cleared unless it is
  // present in the per-order free list - TODO delete?
  let nonempty_clause = (prev != self_node_pointer) && (next != self_node_pointer);
  (prev_clause && next_clause)
}



function (boolean) freeArea_cell_wf (u8 cell_index, i64 physvirt_offset,
        pointer virt_ptr,
        map <u64, struct hyp_page> vmemmap, map <i64, struct list_head> APs,
        pointer pool_pointer, struct hyp_pool pool, excludes ex)
{
  let cell = pool.free_area[(u64) cell_index];
  let pool_free_area_arr_pointer = member_shift<hyp_pool>(pool_pointer, free_area);
  let cell_pointer = array_shift<struct list_head>(pool_free_area_arr_pointer, cell_index);
  let prev = cell.prev;
  let next = cell.next;
  let prev_page_pointer = prev;
  let prev_page_index = cn_hyp_virt_to_pfn(physvirt_offset, prev_page_pointer);
  let prev_page = vmemmap[prev_page_index];
  let next_page_pointer = next;
  let next_page_index = cn_hyp_virt_to_pfn(physvirt_offset, next_page_pointer);
  let next_page = vmemmap[next_page_index];
    ((prev == cell_pointer) == (next == cell_pointer))
    && ((prev == cell_pointer) || (
        ((alloc_id) prev == (alloc_id) virt_ptr)
        && (vmemmap_good_pointer (physvirt_offset, prev_page_pointer, vmemmap, pool.range_start, pool.range_end, ex))
        && (prev_page.order == cell_index)
        && (prev_page.refcount == 0u16)
        && ((APs[prev_page_index]).next == cell_pointer)
        && ((alloc_id) next == (alloc_id) virt_ptr)
        && (ptr_eq(next, cell_pointer) || !addr_eq(next, cell_pointer))
        && (vmemmap_good_pointer (physvirt_offset, next_page_pointer, vmemmap, pool.range_start, pool.range_end, ex))
        && (next_page.order == cell_index)
        && (next_page.refcount == 0u16)
        && ((APs[next_page_index]).prev == cell_pointer)
    ))
}

function (boolean) hyp_pool_wf (pointer pool_pointer, struct hyp_pool pool,
        pointer vmemmap_pointer, i64 physvirt_offset)
{
  let range_start = pool.range_start;
  let range_end = pool.range_end;
  let start_i = range_start / (page_size ());
  let end_i = range_end / (page_size ());
  let hp_sz = sizeof <struct hyp_page>;
  let pool_sz = sizeof <struct hyp_pool>;
  let vmemmap_start_pointer = array_shift<struct hyp_page>(vmemmap_pointer,  start_i);
  let vmemmap_boundary_pointer = array_shift<struct hyp_page>(vmemmap_pointer, end_i);
  let range_start_virt = (u64) (((i64) range_start) - physvirt_offset);
  let range_end_virt = (u64) (((i64) range_end) - physvirt_offset);
    (range_start < range_end)
    && (range_end < power(2u64, 52u64))
    && (physvirt_offset < (i64) range_start) // use '<='
    && (mod((u64) physvirt_offset, (page_size ())) == 0u64)
    && (((range_start / (page_size ())) * (page_size ())) == range_start)
    && (((range_end / (page_size ())) * (page_size ())) == range_end)
    && (pool.max_order <= (max_order ()))
    && (mod(((u64) vmemmap_pointer), hp_sz) == 0u64)
    && (((((u64) pool_pointer) + pool_sz) <= ((u64) vmemmap_start_pointer))
        || (((u64) vmemmap_boundary_pointer) <= ((u64) pool_pointer)))
    && (((((u64) pool_pointer) + pool_sz) <= range_start_virt)
        || (range_end_virt <= ((u64) pool_pointer)))
}

function (integer) get_order_uf (integer size)

function (pointer) virt (pointer phys, i64 physvirt_offset) {
  array_shift<char>(phys, (0i64 - physvirt_offset))
}


predicate void Byte (pointer virt)
{
  take B = Owned<char>(virt);
  return;
}

predicate void ByteV (pointer virt, u8 the_value)
{
  take B = Owned<char>(virt);
  assert (B == the_value);
  return;
}

predicate void Page (pointer vbase, integer guard, u8 order)
{
  if (guard == 0) {
    return;
  }
  else {
    let length = page_size_of_order(order);
    let vbaseI = (u64) vbase;
    take Bytes = each (u64 i; (vbaseI <= i) && (i < (vbaseI + length)))
         {Byte(array_shift<char>(NULL, i))};
    return;
  }
}

predicate void ZeroPage (pointer vbase, integer guard, u8 order)
{
  if (guard == 0) {
    return;
  }
  else {
    let length = page_size_of_order(order);
    let vbaseI = ((u64) vbase);
    take Bytes = each (u64 i; (vbaseI <= i) && (i < (vbaseI + length)))
         {ByteV(array_shift<char>(NULL, i), 0u8)};
    return;
  }
}

predicate void AllocatorPageZeroPart (pointer zero_start, u8 order)
{
  let start = (u64) zero_start;
  let region_length = page_size_of_order(order);
  let length = region_length - sizeof<struct list_head>;
  take Bytes = each (u64 i; (start <= i) && (i < (start + length)))
       {ByteV(array_shift<char>(NULL, i), 0u8)};
  return;
}

function (struct list_head) todo_default_list_head ()

predicate struct list_head AllocatorPage
    (pointer vbase, integer guard, u8 order)
{
  if (guard == 0) {
    return (todo_default_list_head ());
  }
  else {
    let zero_start = array_shift<struct list_head>(vbase, 1u8);
    take ZeroPart = AllocatorPageZeroPart (zero_start, order);
    take Node = Owned<struct list_head>(vbase);
    return Node;
  }
}


predicate {
    struct hyp_pool pool
    , map <u64, struct hyp_page> vmemmap
    , map <i64, struct list_head> APs
}
Hyp_pool_ex1 (
    pointer pool_l
    , pointer vmemmap_l
    , pointer virt_ptr
    , i64 physvirt_offset
    , u64 ex1
)
{
  let ex = exclude_one (ex1);
  take pool = Owned<struct hyp_pool>(pool_l);
  let start_i = pool.range_start / page_size();
  let end_i = pool.range_end / page_size();
  assert (hyp_pool_wf (pool_l, pool, vmemmap_l, physvirt_offset));
  take V = each(u64 i; (start_i <= i) && (i < end_i))
               {Owned(array_shift<struct hyp_page>(vmemmap_l, i))};
  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);
  take APs = each(u64 i; (start_i <= i) && (i < end_i)
                  && ((V[i]).refcount == 0u16)
                  && ((V[i]).order != (hyp_no_order ()))
                  && ((not (excluded (ex, i)))))
                 {AllocatorPage(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), 1, (V[i]).order)};
  assert (each (u64 i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V, pool_l, pool)});
  assert (each (u64 i; (start_i <= i) && (i < end_i)
            && ((V[i]).refcount == 0u16)
            && ((V[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex)});
  assert (each(u8 i; i < pool.max_order)
              {freeArea_cell_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex)});
  return {pool: pool, vmemmap: V, APs: APs};
}

predicate {
    struct hyp_pool pool
    , map <u64, struct hyp_page> vmemmap
    , map <i64, struct list_head> APs
}
Hyp_pool_ex2 (
    pointer pool_l
    , pointer vmemmap_l
    , pointer virt_ptr
    , i64 physvirt_offset
    , u64 ex1
    , u64 ex2
)
{
  let ex = exclude_two (ex1, ex2);
  take pool = Owned<struct hyp_pool>(pool_l);
  let start_i = pool.range_start / page_size();
  let end_i = pool.range_end / page_size();
  assert (hyp_pool_wf (pool_l, pool, vmemmap_l, physvirt_offset));
  take V = each(u64 i; (start_i <= i) && (i < end_i))
              {Owned(array_shift<struct hyp_page>(vmemmap_l,  i))};
  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);
  take APs = each(u64 i; (start_i <= i) && (i < end_i)
                  && ((V[i]).refcount == 0u16)
                  && ((V[i]).order != (hyp_no_order ()))
                  && ((not (excluded (ex, i)))))
                 {AllocatorPage(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), 1, (V[i]).order)};
  assert (each (u64 i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V, pool_l, pool)});
  assert (each (u64 i; (start_i <= i) && (i < end_i)
            && ((V[i]).refcount == 0u16)
            && ((V[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex)});
  assert (each(u8 i; i < pool.max_order)
              {freeArea_cell_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, pool, ex)});
  return {pool: pool, vmemmap: V, APs: APs};
}

predicate {
    struct hyp_pool pool
    , map <u64, struct hyp_page> vmemmap
    , map <i64, struct list_head> APs
}
Hyp_pool (
    pointer pool_l
    , pointer vmemmap_l
    , pointer virt_ptr
    , i64 physvirt_offset
)
{
  let ex = exclude_none ();
  take P = Owned<struct hyp_pool>(pool_l);
  let start_i = P.range_start / page_size();
  let end_i = P.range_end / page_size();
  take V = each(u64 i; (start_i <= i) && (i < end_i))
              {Owned(array_shift<struct hyp_page>(vmemmap_l, i))};
  assert (hyp_pool_wf (pool_l, P, vmemmap_l, physvirt_offset));
  let ptr_phys_0 = cn__hyp_va(virt_ptr, physvirt_offset, 0u64);
  take APs = each(u64 i; (start_i <= i) && (i < end_i)
                  && ((V[i]).refcount == 0u16)
                  && ((V[i]).order != (hyp_no_order ()))
                  && ((not (excluded (ex, i)))))
                 {AllocatorPage(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), 1, (V[i]).order)};
  assert (each (u64 i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V, pool_l, P)});
  assert (each (u64 i; (start_i <= i) && (i < end_i)
            && ((V[i]).refcount == 0u16)
            && ((V[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, P, ex)});
  assert (each(u8 i; i < P.max_order)
              {freeArea_cell_wf (i, physvirt_offset, virt_ptr, V, APs, pool_l, P, ex)});
  return {pool: P, vmemmap: V, APs: APs};
}




predicate (struct list_head) O_struct_list_head(pointer p, boolean condition) 
{
  if (condition) {
    take v = Owned<struct list_head>(p);
    return v;
  }
  else {
    return todo_default_list_head ();
  }
}
@*/
