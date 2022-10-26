function (integer) pfn_buddy (integer x, integer sz)
function (boolean) order_aligned (integer x, integer sz)
function (integer) order_align (integer x, integer sz)
function (boolean) page_aligned (integer x, integer sz)
function (integer) page_size_of_order (integer sz)

function (integer) page_size ()

static int _cn_page_size (void) /*@ cn_function page_size @*/ { return PAGE_SIZE; }

function (integer) max_order ()
static int _cn_max_order (void) /*@ cn_function max_order @*/ { return MAX_ORDER; }

function (integer) hyp_no_order ()
static u64 _cn_hyp_no_order (void) /*@ cn_function hyp_no_order @*/ { return HYP_NO_ORDER; }

function (boolean) vmemmap_good_pointer (pointer vmemmap_pointer, pointer p,
        integer range_start, integer range_end)
{
  let hp_sz = (sizeof <struct hyp_page>);
  let start_i = range_start / (page_size ());
  let end_i = range_end / (page_size ());
  let offs = ((integer) p) - ((integer) vmemmap_pointer);
  let idx = offs / hp_sz;
  return (
    (((offs / hp_sz) * hp_sz) == offs)
    && (start_i <= idx)
    && (idx < end_i)
  );
}


function (boolean) page_group_ok (integer page_index, pointer vmemmap_pointer,
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

function (boolean) init_vmemmap_page (integer page_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  let hp_sz = (sizeof <struct hyp_page>);
  let page_pointer = ((pointer) (
    ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let page = vmemmap[page_index];
  let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
  return (
    (page.order == 0)
    && (page.refcount == 1)
    && (page.pool == pool_pointer)
    && (page.node.next == self_node_pointer)
    && (page.node.prev == self_node_pointer)
    && (order_aligned(page_index, 0))
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
  );
}



function (boolean) vmemmap_normal_order_wf (integer page_index, struct hyp_page page, struct hyp_pool pool) {
  let max_ORDER = 11;
  return (
    (0 <= page.order && ((page.order < pool.max_order) && (page.order < max_ORDER)))
    && order_aligned(page_index, page.order)
    && (((page_index * (page_size ())) + page_size_of_order(page.order)) <= pool.range_end)
  );
}


function (boolean) vmemmap_wf (integer page_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  let hp_sz = (sizeof <struct hyp_page>);
  let page_pointer = ((pointer) (
    ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
  let page = vmemmap[page_index];
  let prev = page.node.prev;
  let next = page.node.next;
  return (
    /* representable as a signed int */
    (0 <= page.refcount) && (page.refcount < (power(2, 31)))
    && (page.pool == pool_pointer)
    && ((page.order == (hyp_no_order ())) || vmemmap_normal_order_wf(page_index, page, pool))
    && ((page.order != (hyp_no_order ())) || (page.refcount == 0))
    && ((next == self_node_pointer) == (prev == self_node_pointer))
    && ((next == self_node_pointer)
        || ((page.refcount == 0) && ((page.order != (hyp_no_order ())))))
    && (page_group_ok(page_index, vmemmap_pointer, vmemmap, pool))
  );
}


function (boolean) vmemmap_l_wf (integer page_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  let hp_sz = (sizeof <struct hyp_page>);
  let page_pointer = ((pointer) (
    ((integer)vmemmap_pointer) + (hp_sz * page_index)));
  let page = vmemmap[page_index];
  let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
  let pool_free_area_arr_pointer = (pointer)(((integer)pool_pointer) +
    (offsetof (hyp_pool, free_area)));
  let l_sz = sizeof <struct list_head>;
  let pool_free_area_pointer = ((pointer) (
    ((integer)pool_free_area_arr_pointer) + (page.order * l_sz)));
  let prev = page.node.prev;
  let next = page.node.next;
  let free_area_entry = ((pool.free_area)[page.order]);
  let prev_page_pointer = (pointer)(((integer)prev) - (offsetof (hyp_page, node)));
  let prev_page_index = (((integer) prev_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  let prev_page = vmemmap[prev_page_index];
  let next_page_pointer = (pointer)(((integer)next) - (offsetof (hyp_page, node)));
  let next_page_index = (((integer) next_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  let next_page = vmemmap[next_page_index];
  let prev_clause = (prev == self_node_pointer)
    || ((prev == pool_free_area_pointer) && (free_area_entry.next == self_node_pointer))
    || (vmemmap_good_pointer (vmemmap_pointer, prev_page_pointer, pool.range_start, pool.range_end)
        && (prev_page.node.next == self_node_pointer)
        && (prev_page.order == page.order));
  let next_clause = (next == self_node_pointer)
    || ((next == pool_free_area_pointer) && (free_area_entry.prev == self_node_pointer))
    || (vmemmap_good_pointer (vmemmap_pointer, next_page_pointer, pool.range_start, pool.range_end)
        && (next_page.node.prev == self_node_pointer)
        && (next_page.order == page.order));
  return (prev_clause && next_clause);
}

function (boolean) vmemmap_b_wf (integer page_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  return (vmemmap_wf (page_index, vmemmap_pointer, vmemmap, pool_pointer, pool)
    && vmemmap_l_wf (page_index, vmemmap_pointer, vmemmap, pool_pointer, pool)
  );
}

function (boolean) freeArea_cell_wf (integer cell_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  let cell = (pool.free_area)[cell_index];
  let pool_free_area_arr_pointer = (pointer)(((integer)pool_pointer) +
    (offsetof (hyp_pool, free_area)));
  let l_sz = sizeof <struct list_head>;
  let hp_sz = (sizeof <struct hyp_page>);
  let cell_pointer = ((pointer) (((integer)pool_free_area_arr_pointer) + (cell_index * l_sz)));
  let prev = cell.prev;
  let next = cell.next;
  let prev_page_pointer = (pointer)(((integer)prev) - (offsetof (hyp_page, node)));
  let prev_page_index = (((integer) prev_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  let prev_page = vmemmap[prev_page_index];
  let next_page_pointer = (pointer)(((integer)next) - (offsetof (hyp_page, node)));
  let next_page_index = (((integer) next_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  let next_page = vmemmap[next_page_index];
  return (
    ((prev == cell_pointer) == (next == cell_pointer))
    && ((prev == cell_pointer) || (
        (vmemmap_good_pointer (vmemmap_pointer, prev_page_pointer, pool.range_start, pool.range_end))
        && (prev_page.order == cell_index)
        && (prev_page.refcount == 0)
        && (prev_page.node.next == cell_pointer)
        && (vmemmap_good_pointer (vmemmap_pointer, next_page_pointer, pool.range_start, pool.range_end))
        && (next_page.order == cell_index)
        && (next_page.refcount == 0)
        && (next_page.node.prev == cell_pointer)
    ))
  );
}

function (boolean) hyp_pool_wf (pointer pool_pointer, struct hyp_pool pool,
        pointer vmemmap_pointer, integer hyp_physvirt_offset)
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
  return (
    (0 <= range_start)
    && (range_start < range_end)
    && (range_end < (power(2, 52)))
    && (0 <= hyp_physvirt_offset)
    && (hyp_physvirt_offset < range_start) /* use '<=' */
    && (mod(hyp_physvirt_offset, (page_size ())) == 0)
    && (((range_start / (page_size ())) * (page_size ())) == range_start)
    && (((range_end / (page_size ())) * (page_size ())) == range_end)
    && (0 <= ((integer) vmemmap_boundary_pointer))
    && (((integer) vmemmap_boundary_pointer) < (power(2, 64)))
    && (0 <= pool.max_order)
    && (pool.max_order <= (max_order ()))
    && (((((integer) vmemmap_pointer) / hp_sz) * hp_sz) == ((integer) vmemmap_pointer))
    && (((((integer) pool_pointer) + pool_sz) <= ((integer) vmemmap_start_pointer))
        || (((integer) vmemmap_boundary_pointer) <= ((integer) pool_pointer)))
  );
}



/* define intptr_t a hacky way, for lemmas */
/*CN*/ typedef u64 intptr_t;


void lemma_order_dec_inv (phys_addr_t pool_range_end,
                          u64 pfn,
                          unsigned int order1,
                          unsigned int order2) 
/*@ trusted @*/
/*@ requires order_aligned(pfn, order1) @*/
/*@ requires (pfn*4096) + (page_size_of_order(order1)) <= pool_range_end @*/
/*@ requires 0 <= order2; order2 <= order1 @*/
/*@ ensures order_aligned(pfn, order2) @*/
/*@ ensures (pfn * 4096) + (page_size_of_order(order2)) <= pool_range_end @*/
{}

void lemma_order_dec_inv_ (phys_addr_t pool_range_end,
                          u64 pfn,
                          unsigned int order1) 
/*@ requires order_aligned(pfn, order1) @*/
/*@ requires (pfn*4096) + (page_size_of_order(order1)) <= pool_range_end @*/
/*@ requires let order2 = order1 - 1 @*/
/*@ requires 0 <= order2; order2 <= order1 @*/
/*@ ensures order_aligned(pfn, order2) @*/
/*@ ensures (pfn * 4096) + (page_size_of_order(order2)) <= pool_range_end @*/
{
  u64 order2 = order1 - 1;
  lemma_order_dec_inv(pool_range_end, pfn, order1, order2);
}




void lemma2 (intptr_t p_i, unsigned int order)
/*@ trusted @*/
/*@ requires order >= 0 @*/
/*@ requires let p_phys = p_i * 4096 @*/
/*@ requires let buddy_i = pfn_buddy(p_i, order) @*/
/*@ requires let buddy_phys = buddy_i * 4096 @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires order_aligned(buddy_i, order) @*/
/*@ ensures let min_i = (p_i < buddy_i) ? p_i : buddy_i @*/
/*@ ensures let min_i_phys = min_i * 4096 @*/
/*@ ensures order_aligned(min_i, order+1) @*/
/*@ ensures page_aligned(min_i_phys, order+1) @*/
/*@ ensures (p_phys + (page_size_of_order(order)) == buddy_phys) || (p_phys - (page_size_of_order(order)) == buddy_phys) @*/
{}


void lemma_extract (intptr_t p_i, unsigned int order)
/*@ trusted @*/
/*@ requires order >= 0 @*/
/*@ requires let p_phys = p_i * 4096 @*/
/*@ requires let buddy_i = pfn_buddy(p_i, order) @*/
/*@ requires let buddy_phys = buddy_i * 4096 @*/
/*@ requires order_aligned(p_i, order + 1) @*/
/*@ ensures p_phys + (page_size_of_order(order)) == buddy_phys @*/
/*@ ensures page_aligned(p_phys, order) @*/
/*@ ensures page_aligned(buddy_phys, order) @*/
{}



void lemma_page_size_of_order_inc (unsigned int order) 
/*@ trusted @*/
/*@ requires order >= 0 @*/
/*@ ensures (page_size_of_order(order+1)) == 2*(page_size_of_order(order)) @*/
{}







void lemma4 (intptr_t p_i, unsigned int order)
/*@ trusted @*/
/*@ requires order >= 1 @*/
/*@ requires let p_phys = p_i * 4096 @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order - 1) @*/
/*@ ensures let buddy_phys = buddy_i * 4096 @*/
/*@ ensures !(order_aligned(buddy_i, order)) @*/
/*@ ensures buddy_phys == p_phys + (page_size_of_order(order - 1)) @*/
/*@ ensures 0 < (page_size_of_order(order)) @*/
/*@ ensures 0 < (page_size_of_order(order - 1)) @*/
/*@ ensures (page_size_of_order(order - 1)) * 2 == (page_size_of_order(order)) @*/
/*@ ensures (order_align(buddy_i, order)) == p_i @*/
{}




void lemma_order_align_inv_loop (struct hyp_pool pool,
                                 struct hyp_page* p) 
/*@ trusted @*/
/*@ accesses __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires let start_i = (pool).range_start / 4096 @*/
/*@ requires let end_i = (pool).range_end / 4096 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32))} @*/
/*@ requires let p_order = (V.value[p_i]).order @*/
/*@ requires p_order >= 1; p_order < 11 @*/
/*@ requires order_aligned(p_i, p_order) @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires let buddy_i = pfn_buddy(p_i, p_order - 1) @*/
/*@ requires each(integer i; start_i <= i && i < end_i) { page_group_ok(i, hyp_vmemmap, V.value, pool) } @*/
/*@ ensures let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32))} @*/
/*@ ensures V.value == {V.value}@start @*/
/*@ ensures let p_new_page = (V.value[p_i]){.order = (p_order - 1)} @*/
/*@ ensures let buddy_new_page = (V.value[buddy_i]){.order = (p_order - 1)} @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, hyp_vmemmap, (V.value[p_i = p_new_page])[buddy_i = buddy_new_page], pool) } @*/
/*@ ensures {__hyp_vmemmap} unchanged @*/
{}


void lemma_page_group_ok_easy (struct hyp_pool pool) 
/*@ trusted @*/
/*@ accesses __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let start_i = (pool).range_start / 4096 @*/
/*@ requires let end_i = (pool).range_end / 4096 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ requires each (integer i; start_i <= i && i < end_i) { (V.value[i]).order == 0 } @*/
/*@ ensures let V = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ ensures V.value == {V.value}@start @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, hyp_vmemmap, V.value, pool) } @*/
/*@ ensures {__hyp_vmemmap} unchanged @*/
{}

void lemma_order_aligned_init (unsigned long i) 
/*@ trusted @*/
/*@ ensures order_aligned({i}@start, 0) @*/
{}

void lemma_page_size_of_order () 
/*@ trusted @*/
/*@ ensures (page_size_of_order(0)) == 4096 @*/
{}




void lemma_attach_inc_loop (struct hyp_pool pool,
                            struct hyp_page* p,
                            unsigned int order) 
/*@ trusted @*/
/*@ accesses __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let start_i = (pool).range_start / 4096 @*/
/*@ requires let end_i = (pool).range_end / 4096 @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires let buddy_i = pfn_buddy(p_i, order) @*/
/*@ requires let buddy_order = (V.value[buddy_i]).order @*/
/*@ requires start_i <= buddy_i; buddy_i < end_i @*/
/*@ requires 0 <= order; order + 1 < 11; buddy_order == order @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires order_aligned(buddy_i, order) @*/
/*@ requires (V.value[p_i]).order == 4294967295 @*/
/*@ requires let p_page_tweaked = (V.value[p_i]){.order = order} @*/
/*@ requires each(integer i; start_i <= i && i < end_i) { page_group_ok(i, hyp_vmemmap, V.value[p_i = p_page_tweaked], pool) } @*/
/*@ requires let min_i = (p_i < buddy_i) ? p_i : buddy_i @*/
/*@ requires let min_page = (V.value[min_i]){.order = (order + 1)} @*/
/*@ requires let buddy_page = (V.value[buddy_i]){.order = 4294967295} @*/
/*@ ensures let V2 = each(integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ ensures V2.value == {V.value}@start @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, hyp_vmemmap, (V2.value[buddy_i = buddy_page])[min_i = min_page], pool) } @*/
/*@ ensures {__hyp_vmemmap} unchanged @*/
{}


void find_buddy_xor_lemma(intptr_t addr_i, unsigned int order)
/*@ trusted @*/
/*@ requires order_aligned(addr_i, order) @*/
/*@ requires 0 <= order; order < 11 @*/
/*@ requires addr_i * 4096 < (power(2, 64)) @*/
/*@ ensures 0 < (power_uf(2, order)) @*/
/*@ ensures (power_uf(2, order)) < (power(2, 11)) @*/
/*@ ensures 0 <= (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) @*/
/*@ ensures (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) < (power(2, 64)) @*/
/*@ ensures let buddy_addr = (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) @*/
/*@ ensures let buddy_i = (buddy_addr / 4096) @*/
/*@ ensures buddy_i == (pfn_buddy (addr_i, order)) @*/
/*@ ensures (mod(buddy_addr, 4096)) == 0 @*/
/*@ ensures order_aligned(buddy_i, order) @*/
/*@ ensures addr_i != buddy_i @*/
{}



void page_size_of_order_lemma(unsigned int order)
/*@ trusted @*/
/*@ requires 0 <= order; order < 11 @*/
/*@ ensures 0 < (power_uf(2, order)) @*/
/*@ ensures (power_uf(2, order)) < (power(2, 11)) @*/
/*@ ensures let size = 4096 * (power_uf(2, order)) @*/
/*@ ensures size == (page_size_of_order(order)) @*/
{}


function (integer) get_order_uf (integer size)

function (pointer) virt (pointer phys, integer hyp_physvirt_offset) {
  return (pointer) (((integer) phys) - hyp_physvirt_offset);
}


predicate {} Byte (pointer virt)
{
  let B = Owned<char>(virt);
  return {};
}

predicate {} ByteV (pointer virt, integer the_value)
{
  let B = Owned<char>(virt);
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
    let Bytes = each (integer i; (vbaseI <= i) && (i < (vbaseI + length)))
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
    let Bytes = each (integer i; (vbaseI <= i) && (i < (vbaseI + length)))
        {ByteV((pointer)(((integer)((pointer) 0)) + (i * 1)), 0)};
    return {};
  }
}





predicate {struct hyp_pool pool, map <integer, struct hyp_page> vmemmap}
    Hyp_pool (pointer pool_l, pointer vmemmap_l, integer physvirt_offset)
{
  let P = Owned<struct hyp_pool>(pool_l);
  let start_i = P.value.range_start / 4096;
  let end_i = P.value.range_end / 4096;
  let off_i = physvirt_offset / 4096;
  let V = each(integer i; (start_i <= i) && (i < end_i))
              {Owned<struct hyp_page>(vmemmap_l + i*32)};
  assert (each(integer i; (start_i <= i) && (i < end_i))
              {vmemmap_b_wf (i, vmemmap_l, V.value, pool_l, P.value)});
  assert (each(integer i; (0 <= i) && (i < P.value.max_order))
              {freeArea_cell_wf (i, vmemmap_l, V.value, pool_l, P.value)});
  assert (hyp_pool_wf (pool_l, P.value, vmemmap_l, physvirt_offset));
  let R = each(integer i; (start_i <= i + off_i) && (i + off_i < end_i)
                && (((V.value)[i+off_i]).refcount == 0)
                && (((V.value)[i+off_i]).order != (hyp_no_order ())))
              {ZeroPage(((pointer) 0) + i*4096, 1, ((V.value)[i+off_i]).order)};
  return {pool = P.value, vmemmap = V.value};
}


