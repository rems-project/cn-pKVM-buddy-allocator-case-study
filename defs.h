function (integer) pfn_buddy (integer x, integer sz)
function (boolean) order_aligned (integer x, integer sz)
function (integer) order_align (integer x, integer sz)
function (boolean) page_aligned (integer x, integer sz)
function (integer) page_size_of_order (integer sz)

function (integer) page_size () { return 4096; }
function (integer) max_order () { return 11; }
function (integer) hyp_no_order () { return 255; }
function (integer) sizeof_struct_hyp_page(){ return sizeof <struct hyp_page>; }
function (integer) sizeof_struct_list_head() { return sizeof <struct list_head>; }

function (integer) cn_hyp_page_to_pfn(integer hypvmemmap, pointer p) {
  return (((integer) p) - hypvmemmap) / sizeof<struct hyp_page>;
}

/* copied and adjusted from the corresponding macro definition in memory.h */
function (integer) cn__hyp_pa(integer physvirtoffset, pointer virt) {
  return (((integer)(virt)) + physvirtoffset);
}



/* copied and adjusted from the corresponding macro definition in memory.h */
function (integer) cn_hyp_phys_to_pfn(integer phys) {
  return phys / 4096;
}

/* copied and adjusted from the corresponding macro definition in memory.h */
function (integer) cn_hyp_virt_to_pfn (integer physvirtoffset, pointer virt) {
  return cn_hyp_phys_to_pfn(cn__hyp_pa(physvirtoffset, virt));
}


function (integer) cn_hyp_pfn_to_phys(integer pfn) {
  return pfn*4096;
}

/* copied and adjusted from the corresponding macro definition in memory.h */
function (integer) cn_hyp_page_to_phys(integer hypvmemmap, pointer page) {
  return cn_hyp_pfn_to_phys((cn_hyp_page_to_pfn(hypvmemmap, page)));
}

/* copied and adjusted from the corresponding macro definition in memory.h */
function (pointer) cn__hyp_va(integer physvirtoffset, integer phys) {
  return ((pointer) (phys - physvirtoffset));
}

/* copied and adjusted from the corresponding macro definition in memory.h */
function (pointer) cn_hyp_page_to_virt(integer physvirtoffset, 
                                       integer hypvmemmap, pointer page) {
  return cn__hyp_va(physvirtoffset, cn_hyp_page_to_phys(hypvmemmap, page));
}


datatype excludes {
  Exclude {boolean any, boolean do_ex1, integer ex1, boolean do_ex2, integer ex2}
}

function (boolean) excluded (datatype excludes ex, integer i)
{
  return (
    (ex.any && (
      (ex.do_ex1 && (i == ex.ex1))
      || (ex.do_ex2 && (i == ex.ex2))
  )));
}

function (datatype excludes) exclude_none ()
{
  return Exclude {any = 0 < 0, do_ex1 = 0 < 0, ex1 = 0, do_ex2 = 0 < 0, ex2 = 0};
}

function (datatype excludes) exclude_one (integer ex1)
{
  return Exclude {any = 0 < 1, do_ex1 = 0 < 1, ex1 = ex1, do_ex2 = 0 < 0, ex2 = 0};
}

function (datatype excludes) exclude_two (integer ex1, integer ex2)
{
  return Exclude {any = 0 < 1, do_ex1 = 0 < 1, ex1 = ex1, do_ex2 = 0 < 1, ex2 = ex2};
}


/* Check a pointer (to the struct list_head embedded in a free page) is a valid
   pointer, which includes knowing that its matching vmemmap entry has the
   refcount/order settings that indicate that the struct is present. */
function (boolean) vmemmap_good_pointer (integer physvirt_offset, pointer p,
        map <integer, struct hyp_page> vmemmap,
        integer range_start, integer range_end, datatype excludes ex)
{
  // let hp_sz = (sizeof <struct hyp_page>);
  let start_i = range_start / (page_size ());
  let end_i = range_end / (page_size ());
  let offs = ((integer) p) + physvirt_offset;
  // let idx = offs / hp_sz;
  let idx = offs / (page_size ());
  return (
    (((offs / (page_size ())) * (page_size ())) == offs)
    && (start_i <= idx)
    && (idx < end_i)
    && (vmemmap[idx].refcount == 0)
    && (vmemmap[idx].order != (hyp_no_order ()))
    && (not (excluded (ex, idx)))
  );
}


function (boolean) page_group_ok (integer page_index,
        map <integer, struct hyp_page> vmemmap, struct hyp_pool pool)
{
  let page = vmemmap[page_index];
  let start_i = (pool.range_start) / (page_size ());
  return ((page.order == (hyp_no_order ()))
    || (each (i: 1, 10; (not (
        ((order_align(page_index, i)) < page_index)
        && (start_i <= (order_align(page_index, i)))
        && (i <= ((vmemmap[(order_align(page_index, i))]).order))
        && (((vmemmap[(order_align(page_index, i))]).order) != (hyp_no_order ()))
    )))));
}

// There are no `AllocatorPage`s outputs to pass as arguments in `hyp_pool_init`
// Also a different invariant handles checking prev/next
function (boolean) init_vmemmap_page (integer page_index,
        map <integer, struct hyp_page> vmemmap,
        pointer pool_pointer, struct hyp_pool pool)
{
  // let hp_sz = (sizeof <struct hyp_page>);
  // let page_pointer = ((pointer) (
  //   ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let page = vmemmap[page_index];
  // let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
  return (
    (page.order == 0)
    && (page.refcount == 1)
    // && (page.pool == pool_pointer)
    // && (page.node.next == self_node_pointer)
    // && (page.node.prev == self_node_pointer)
    && (order_aligned(page_index, 0))
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
  );
}

function (boolean) vmemmap_normal_order_wf (integer page_index, struct hyp_page page, struct hyp_pool pool) {
  return (
    (0 <= page.order && ((page.order < pool.max_order) && (page.order < (max_order()))))
    && order_aligned(page_index, page.order)
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
  );
}


function (boolean) vmemmap_wf (integer page_index,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  // let hp_sz = (sizeof <struct hyp_page>);
  // let page_pointer = ((pointer) (
  //   ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let page = vmemmap[page_index];
  // let prev = page.node.prev;
  // let next = page.node.next;
  return (
    /* representable as an unsigned short */
    (0 <= page.refcount) && (page.refcount < (power(2, 16)))
    // && (page.pool == pool_pointer)
    && ((page.order == (hyp_no_order ())) || vmemmap_normal_order_wf(page_index, page, pool))
    && ((page.order != (hyp_no_order ())) || (page.refcount == 0))
    // && ((next == self_node_pointer)
    //     || ((page.refcount == 0) && ((page.order != (hyp_no_order ())))))
    && (page_group_ok(page_index, vmemmap, pool))
  );
}

function (boolean) vmemmap_l_wf (integer page_index, integer physvirt_offset,
        map <integer, struct hyp_page> vmemmap, map <integer, pointer> prevs,
        map <integer, pointer> nexts, pointer pool_pointer, struct hyp_pool pool,
        datatype excludes ex)
{
  // let hp_sz = (sizeof <struct hyp_page>);
  // let page_pointer = ((pointer) (
  //   ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let page = vmemmap[page_index];
  let self_node_pointer = (pointer)((page_index * (page_size ())) - physvirt_offset);
  let pool_free_area_arr_pointer = (pointer)(((integer)pool_pointer) +
    (offsetof (hyp_pool, free_area)));
  let l_sz = sizeof <struct list_head>;
  let pool_free_area_pointer = ((pointer) (
    ((integer)pool_free_area_arr_pointer) + (page.order * l_sz)));
  let off_i = physvirt_offset / (page_size());
  // let prev = page.node.prev;
  let prev = prevs[page_index - off_i];
  // let next = page.node.next;
  let next = nexts[page_index - off_i];
  let free_area_entry = ((pool.free_area)[page.order]);
  // let prev_page_pointer = (pointer)(((integer)prev) - (offsetof (hyp_page, node)));
  let prev_page_pointer = prev;
  let prev_page_index = (((integer) prev_page_pointer) + physvirt_offset) / (page_size ());
  let prev_page = vmemmap[prev_page_index];
  // let next_page_pointer = (pointer)(((integer)next) - (offsetof (hyp_page, node)));
  let next_page_pointer = next;
  let next_page_index = (((integer) next_page_pointer) + physvirt_offset) / (page_size ());
  let next_page = vmemmap[next_page_index];
  let prev_clause =
    ((prev == pool_free_area_pointer) && (free_area_entry.next == self_node_pointer))
    || (vmemmap_good_pointer (physvirt_offset, prev_page_pointer, vmemmap, pool.range_start, pool.range_end, ex)
        && (nexts[prev_page_index - off_i] == self_node_pointer)
        && (prev_page.order == page.order)
        && (prev_page.refcount == 0));
  let next_clause =
    ((next == pool_free_area_pointer) && (free_area_entry.prev == self_node_pointer))
    || (vmemmap_good_pointer (physvirt_offset, next_page_pointer, vmemmap, pool.range_start, pool.range_end, ex)
        && (prevs[next_page_index - off_i] == self_node_pointer)
        && (next_page.order == page.order)
        && (next_page.refcount == 0));
  /* there is no self-loop case for this node type, as it is cleared unless it is
     present in the per-order free list */
  let nonempty_clause = (prev != self_node_pointer) && (next != self_node_pointer);
  return (prev_clause && next_clause);
}

/*
function (boolean) vmemmap_b_wf (integer page_index, integer physvirt_offset,
        map <integer, struct hyp_page> vmemmap, map <integer, pointer> prevs,
        map <integer, pointer> nexts, pointer pool_pointer, struct hyp_pool pool)
{
  return (vmemmap_wf (page_index, physvirt_offset, vmemmap, prevs, nexts, pool_pointer, pool)
    && vmemmap_l_wf (page_index, physvirt_offset, vmemmap, prevs, nexts, pool_pointer, pool)
  );
}
*/

// hyp_virt_to_page(virt)
// hyp_phys_to_page(__hy_pa(virt))
// hyp_phys_to_page(virt + hyp_physvirt_offset)
// &hyp_vmemmap[hyp_phys_to_pfn(virt + hyp_physvirt_offset)]
// &hyp_vmemmap[(virt + hyp_physvirt_offset) >> PAGE_SHIFT]
// &hyp_vmemmap[(virt + offset) / 4096]

/* Note prevs & nexts are indexed by (virtual-address / page-size), whereas
   the vmemmap is indexed by (physical-address / page-size), this is to do with
   the way they're constructed by iterating conjunction in Hyp_pool. */
function (boolean) freeArea_cell_wf (integer cell_index, integer physvirt_offset,
        map <integer, struct hyp_page> vmemmap, map <integer, pointer> prevs,
        map <integer, pointer> nexts, pointer pool_pointer, struct hyp_pool pool,
        datatype excludes ex)
{
  let cell = (pool.free_area)[cell_index];
  let pool_free_area_arr_pointer = (pointer)(((integer)pool_pointer) +
    (offsetof (hyp_pool, free_area)));
  let l_sz = sizeof <struct list_head>;
  // let hp_sz = (sizeof <struct hyp_page>);
  let cell_pointer = ((pointer) (((integer)pool_free_area_arr_pointer) + (cell_index * l_sz)));
  let prev = cell.prev;
  let next = cell.next;
  // let prev_page_pointer = (pointer)(((integer)prev) - (offsetof (hyp_page, node)));
  let prev_page_pointer = prev;
  // let prev_page_index = (((integer) prev_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  // hyp_virt_to_page
  let prev_page_index = (((integer) prev_page_pointer) + physvirt_offset) / (page_size ());
  let prev_page = vmemmap[prev_page_index];
  // let next_page_pointer = (pointer)(((integer)next) - (offsetof (hyp_page, node)));
  let next_page_pointer = next;
  // let next_page_index = (((integer) next_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  let next_page_index = (((integer) next_page_pointer) + physvirt_offset) / (page_size ());
  let next_page = vmemmap[next_page_index];
  let off_i = physvirt_offset / (page_size());
  return (
    ((prev == cell_pointer) == (next == cell_pointer))
    && ((prev == cell_pointer) || (
        (vmemmap_good_pointer (physvirt_offset, prev_page_pointer, vmemmap, pool.range_start, pool.range_end, ex))
        && (prev_page.order == cell_index)
        && (prev_page.refcount == 0)
        // && (prev_page.node.next == cell_pointer)
        && (nexts[prev_page_index - off_i] == cell_pointer)
        && (vmemmap_good_pointer (physvirt_offset, next_page_pointer, vmemmap, pool.range_start, pool.range_end, ex))
        && (next_page.order == cell_index)
        && (next_page.refcount == 0)
        // && (next_page.node.prev == cell_pointer)
        && (prevs[next_page_index - off_i] == cell_pointer)
    ))
  );
}

function (boolean) hyp_pool_wf (pointer pool_pointer, struct hyp_pool pool,
        pointer vmemmap_pointer, integer physvirt_offset)
{
  let range_start = pool.range_start;
  let range_end = pool.range_end;
  let start_i = range_start / (page_size ());
  let end_i = range_end / (page_size ());
  let hp_sz = (sizeof <struct hyp_page>);
  let pool_sz = (sizeof <struct hyp_pool>);
  let vmemmap_start_pointer = ((pointer) (
    ((integer)vmemmap_pointer) + (hp_sz * start_i)));
  let vmemmap_boundary_pointer = ((pointer) (
    ((integer)vmemmap_pointer) + (hp_sz * end_i)));
  let range_start_virt = range_start - physvirt_offset;
  let range_end_virt = range_end - physvirt_offset;
  return (
    (0 <= range_start)
    && (range_start < range_end)
    && (range_end < (power(2, 52)))
    && (0 <= physvirt_offset)
    && (physvirt_offset < range_start) /* use '<=' */
    && (mod(physvirt_offset, (page_size ())) == 0)
    && (((range_start / (page_size ())) * (page_size ())) == range_start)
    && (((range_end / (page_size ())) * (page_size ())) == range_end)
    && (0 <= ((integer) vmemmap_boundary_pointer))
    && (((integer) vmemmap_boundary_pointer) < (power(2, 64)))
    && (0 <= pool.max_order)
    && (pool.max_order <= (max_order ()))
    && (mod(((integer) vmemmap_pointer), hp_sz) == 0)
    && (((((integer) pool_pointer) + pool_sz) <= ((integer) vmemmap_start_pointer))
        || (((integer) vmemmap_boundary_pointer) <= ((integer) pool_pointer)))
    && (((((integer) pool_pointer) + pool_sz) <= range_start_virt)
        || (range_end_virt <= ((integer) pool_pointer)))
  );
}

function (integer) get_order_uf (integer size)

function (pointer) virt (pointer phys, integer physvirt_offset) {
  return (pointer) (((integer) phys) - physvirt_offset);
}


predicate {} Byte (pointer virt)
{
  take B = Owned<char>(virt);
  return {};
}

predicate {} ByteV (pointer virt, integer the_value)
{
  take B = Owned<char>(virt);
  assert (B.value == the_value);
  return {};
}

predicate {} Page (pointer vbase, integer guard, integer order)
{
  if (guard == 0) {
    return {};
  }
  else {
    assert(((integer) vbase) >= 0);
    let length = (page_size_of_order(order));
    let vbaseI = ((integer) vbase);
    take Bytes = each (integer i; (vbaseI <= i) && (i < (vbaseI + length)))
         {Byte((pointer)(((integer)((pointer) 0)) + (i * 1)))};
    return {};
  }
}

predicate {} ZeroPage (pointer vbase, integer guard, integer order)
{
  if (guard == 0) {
    return {};
  }
  else {
    assert(((integer) vbase) >= 0);
    let length = (page_size_of_order(order));
    let vbaseI = ((integer) vbase);
    take Bytes = each (integer i; (vbaseI <= i) && (i < (vbaseI + length)))
         {ByteV((pointer)(((integer)((pointer) 0)) + (i * 1)), 0)};
    return {};
  }
}

predicate {} AllocatorPageZeroPart (pointer zero_start, integer order)
{
  let start = (integer) zero_start;
  assert (start >= 0);
  let region_length = (page_size_of_order(order));
  let length = (region_length - (sizeof <struct list_head>));
  take Bytes = each (integer i; (start <= i) && (i < (start + length)))
       {ByteV((pointer)(((integer)((pointer) 0)) + (i * 1)), 0)};
  return {};
}

predicate {pointer prev, pointer next} AllocatorPage
    (pointer vbase, integer guard, integer order)
{
  if (guard == 0) {
    return {prev = (pointer) 0, next = (pointer) 0};
  }
  else {
    assert(((integer) vbase) > 0);
    let vbaseI = (((integer) vbase) + (sizeof <struct list_head>));
    take ZeroPart = AllocatorPageZeroPart ((pointer) vbaseI, order);
    take Node = Owned<struct list_head>(vbase);
    return {prev = Node.value.prev, next = Node.value.next};
  }
}


predicate {struct hyp_pool pool, map <integer, struct hyp_page> vmemmap,
        map <integer, pointer> prev, map <integer, pointer> next}
    Hyp_pool_ex1 (pointer pool_l, pointer vmemmap_l,
        integer physvirt_offset, integer ex1)
{
  let ex = exclude_one (ex1);
  take P = Owned<struct hyp_pool>(pool_l);
  let pool = P.value;
  let start_i = pool.range_start / 4096;
  let end_i = pool.range_end / 4096;
  let off_i = physvirt_offset / 4096;
  assert (hyp_pool_wf (pool_l, pool, vmemmap_l, physvirt_offset));
  take V = each(integer i; (start_i <= i) && (i < end_i))
               {Owned<struct hyp_page>(vmemmap_l + i*(sizeof <struct hyp_page>))};
  take APs = each(integer i; (start_i <= i + off_i) && (i + off_i < end_i)
                  && (((V.value)[i+off_i]).refcount == 0)
                  && (((V.value)[i+off_i]).order != (hyp_no_order ()))
                  && ((not (excluded (ex, i + off_i)))))
                 {AllocatorPage(((pointer) 0) + i*4096, 1, ((V.value)[i+off_i]).order)};
  assert (each (integer i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V.value, pool_l, pool)});
  assert (each (integer i; (start_i <= i) && (i < end_i)
            && (((V.value)[i]).refcount == 0)
            && (((V.value)[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, pool, ex)});
  assert (each(integer i; (0 <= i) && (i < pool.max_order))
              {freeArea_cell_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, pool, ex)});
  return {pool = pool, vmemmap = V.value, prev = APs.prev, next = APs.next};
}

predicate {struct hyp_pool pool, map <integer, struct hyp_page> vmemmap,
        map <integer, pointer> prev, map <integer, pointer> next}
    Hyp_pool_ex2 (pointer pool_l, pointer vmemmap_l,
        integer physvirt_offset, integer ex1, integer ex2)
{
  let ex = exclude_two (ex1, ex2);
  take P = Owned<struct hyp_pool>(pool_l);
  let pool = P.value;
  let start_i = pool.range_start / 4096;
  let end_i = pool.range_end / 4096;
  let off_i = physvirt_offset / 4096;
  assert (hyp_pool_wf (pool_l, pool, vmemmap_l, physvirt_offset));
  take V = each(integer i; (start_i <= i) && (i < end_i))
              {Owned<struct hyp_page>(vmemmap_l + i*(sizeof <struct hyp_page>))};
  take APs = each(integer i; (start_i <= i + off_i) && (i + off_i < end_i)
                && (((V.value)[i+off_i]).refcount == 0)
                && (((V.value)[i+off_i]).order != (hyp_no_order ()))
                && ((not (excluded (ex, i + off_i)))))
              {AllocatorPage(((pointer) 0) + i*4096, 1, ((V.value)[i+off_i]).order)};
  assert (each (integer i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V.value, pool_l, pool)});
  assert (each (integer i; (start_i <= i) && (i < end_i)
            && (((V.value)[i]).refcount == 0)
            && (((V.value)[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, pool, ex)});
  assert (each(integer i; (0 <= i) && (i < pool.max_order))
              {freeArea_cell_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, pool, ex)});
  return {pool = pool, vmemmap = V.value, prev = APs.prev, next = APs.next};
}

predicate {struct hyp_pool pool, map <integer, struct hyp_page> vmemmap,
        map <integer, pointer> prev, map <integer, pointer> next}
    Hyp_pool (pointer pool_l, pointer vmemmap_l, integer physvirt_offset)
{
  let ex = exclude_none ();
  take P = Owned<struct hyp_pool>(pool_l);
  let start_i = P.value.range_start / 4096;
  let end_i = P.value.range_end / 4096;
  let off_i = physvirt_offset / 4096;
  take V = each(integer i; (start_i <= i) && (i < end_i))
              {Owned<struct hyp_page>(vmemmap_l + i*(sizeof <struct hyp_page>))};
  assert (hyp_pool_wf (pool_l, P.value, vmemmap_l, physvirt_offset));
  take APs = each(integer i; (start_i <= i + off_i) && (i + off_i < end_i)
                && (((V.value)[i+off_i]).refcount == 0)
                && (((V.value)[i+off_i]).order != (hyp_no_order ()))
                && ((not (excluded (ex, i + off_i)))))
              {AllocatorPage(((pointer) 0) + i*4096, 1, ((V.value)[i+off_i]).order)};
  assert (each (integer i; (start_i <= i) && (i < end_i))
    {vmemmap_wf (i, V.value, pool_l, P.value)});
  assert (each (integer i; (start_i <= i) && (i < end_i)
            && (((V.value)[i]).refcount == 0)
            && (((V.value)[i]).order != (hyp_no_order ()))
            && ((not (excluded (ex, i)))))
    {vmemmap_l_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, P.value, ex)});
  assert (each(integer i; (0 <= i) && (i < P.value.max_order))
              {freeArea_cell_wf (i, physvirt_offset, V.value, APs.prev, APs.next, pool_l, P.value, ex)});
  return {pool = P.value, vmemmap = V.value, prev = APs.prev, next = APs.next};
}


