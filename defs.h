function (integer) pfn_buddy (integer x, integer sz)
function (boolean) order_aligned (integer x, integer sz)
function (integer) order_align (integer x, integer sz)
function (boolean) page_aligned (integer x, integer sz)
function (integer) page_size_of_order (integer sz)

function (integer) page_size () { return 4096; }
function (integer) max_order () { return 11; }
function (integer) hyp_no_order () { return 4294967295; }

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
  // let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
  let page = vmemmap[page_index];
  // let prev = page.node.prev;
  // let next = page.node.next;
  return (
    /* representable as a signed int */
    (0 <= page.refcount) && (page.refcount < (power(2, 31)))
    // && (page.pool == pool_pointer)
    && ((page.order == (hyp_no_order ())) || vmemmap_normal_order_wf(page_index, page, pool))
    && ((page.order != (hyp_no_order ())) || (page.refcount == 0))
    // && ((next == self_node_pointer) == (prev == self_node_pointer))
    // && ((next == self_node_pointer)
    //     || ((page.refcount == 0) && ((page.order != (hyp_no_order ())))))
    && ((page.refcount == 0) && ((page.order != (hyp_no_order ()))))
    && (page_group_ok(page_index, vmemmap_pointer, vmemmap, pool))
  );
}


// function (boolean) vmemmap_l_wf (integer page_index, pointer vmemmap_pointer,
//         map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
// {
//   let hp_sz = (sizeof <struct hyp_page>);
//   let page_pointer = ((pointer) (
//     ((integer)vmemmap_pointer) + (hp_sz * page_index)));
//   let page = vmemmap[page_index];
//   // let self_node_pointer = (pointer)(((integer)page_pointer) + (offsetof (hyp_page, node)));
//   let pool_free_area_arr_pointer = (pointer)(((integer)pool_pointer) +
//     (offsetof (hyp_pool, free_area)));
//   let l_sz = sizeof <struct list_head>;
//   let pool_free_area_pointer = ((pointer) (
//     ((integer)pool_free_area_arr_pointer) + (page.order * l_sz)));
//   // let prev = page.node.prev;
//   // let next = page.node.next;
//   let free_area_entry = ((pool.free_area)[page.order]);
//   // let prev_page_pointer = (pointer)(((integer)prev) - (offsetof (hyp_page, node)));
//   // let prev_page_index = (((integer) prev_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
//   // let prev_page = vmemmap[prev_page_index];
//   // let next_page_pointer = (pointer)(((integer)next) - (offsetof (hyp_page, node)));
//   // let next_page_index = (((integer) next_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
//   // let next_page = vmemmap[next_page_index];
//   // let prev_clause = (prev == self_node_pointer)
//   //   || ((prev == pool_free_area_pointer) && (free_area_entry.next == self_node_pointer))
//   //   || (vmemmap_good_pointer (vmemmap_pointer, prev_page_pointer, pool.range_start, pool.range_end)
//   //       && (prev_page.node.next == self_node_pointer)
//   //       && (prev_page.order == page.order));
//   let prev_clause =
//     vmemmap_good_pointer (vmemmap_pointer, (pointer) 0, pool.range_start, pool.range_end);
//   // let next_clause = (next == self_node_pointer)
//   //   || ((next == pool_free_area_pointer) && (free_area_entry.prev == self_node_pointer))
//   //   || (vmemmap_good_pointer (vmemmap_pointer, next_page_pointer, pool.range_start, pool.range_end)
//   //       && (next_page.node.prev == self_node_pointer)
//   //       && (next_page.order == page.order));
//   let next_clause =
//     vmemmap_good_pointer (vmemmap_pointer, (pointer) 0, pool.range_start, pool.range_end);
//   return (prev_clause && next_clause);
// }

function (boolean) vmemmap_b_wf (integer page_index, pointer vmemmap_pointer,
        map <integer, struct hyp_page> vmemmap, pointer pool_pointer, struct hyp_pool pool)
{
  return (vmemmap_wf (page_index, vmemmap_pointer, vmemmap, pool_pointer, pool)
    //&& vmemmap_l_wf (page_index, vmemmap_pointer, vmemmap, pool_pointer, pool)
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
  // let prev_page_pointer = (pointer)(((integer)prev)); // - (offsetof (hyp_page, node)));
  // let prev_page_index = (((integer) prev_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  // let prev_page = vmemmap[prev_page_index];
  // let next_page_pointer = (pointer)(((integer)next)); // - (offsetof (hyp_page, node)));
  // let next_page_index = (((integer) next_page_pointer) - ((integer) vmemmap_pointer)) / hp_sz;
  // let next_page = vmemmap[next_page_index];
  return (
    ((prev == cell_pointer) == (next == cell_pointer))
    && ((prev == cell_pointer)));
  //  && ((prev == cell_pointer) || (
  //      (vmemmap_good_pointer (vmemmap_pointer, prev_page_pointer, pool.range_start, pool.range_end))
  //      && (prev_page.order == cell_index)
  //      && (prev_page.refcount == 0)
  //      // && (prev_page.node.next == cell_pointer)
  //      && (vmemmap_good_pointer (vmemmap_pointer, next_page_pointer, pool.range_start, pool.range_end))
  //      && (next_page.order == cell_index)
  //      && (next_page.refcount == 0)
  //      // && (next_page.node.prev == cell_pointer)
  //  ))
  //);
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
              {Owned<struct hyp_page>(vmemmap_l + i*(sizeof <struct hyp_page>))};
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


