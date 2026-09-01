/* originally: arch/arm64/kvm/hyp/nvhe/page_alloc.c */

// SPDX-License-Identifier: GPL-2.0-only
/*
 * Copyright (C) 2020 Google LLC
 * Author: Quentin Perret <qperret@google.com>
 */


#include "posix_types.h"
#include "stddef.h"

#define bool _Bool
#define true 1

//#pragma clang diagnostic ignored "-Wunused-value"
void *copy_alloc_id(unsigned long long i, void *p) { 
    (unsigned long long) p;
    return (void*) i;
}


#define CN_COPY_ALLOC_ID(x,p) copy_alloc_id((x), (p))

#include "const.h"

/* CP: we fix a value for PAGE_SHIFT */
#define PAGE_SHIFT        12
#include "page-def.h"
#include "limits.h"
#include "mmzone.h"
#include "uapi-int-ll64.h"
#include "int-ll64.h"
#include "types.h"
#include "kernel.h"
#include "list.h"
#include "minmax.h"
#include "memory.h"
#include "gfp.h"
#include "defs.h"
#include "lemmas.h"


/* NOTE: we give memset a bogus empty body to overcome a limitation of
   the current CN frontend (function declarations without body loose
   the variable name information that we rely on in the
   specifications).) */
void *memset(void *b, int cc, unsigned long len);
/*@ spec memset(pointer b, i32 cc, u64 len);
    requires let b_i = (u64) b;
             let c = (u8) cc;
             take B = each (u64 i; b_i <= i && i < b_i+len){Byte(array_shift<char>(NULL, i))};
    ensures take BR = each (u64 i; b_i <= i && i < b_i+len){ByteV(array_shift<char>(NULL,i), c)}; @*/




struct hyp_page *__hyp_vmemmap;
/*CN*/ 
void *cn_virt_ptr;

/*
 * Index the hyp_vmemmap to find a potential buddy page, but make no assumption
 * about its current state.
 *
 * Example buddy-tree for a 4-pages physically contiguous pool:
 *
 *                 o : Page 3
 *                /
 *               o-o : Page 2
 *              /
 *             /   o : Page 1
 *            /   /
 *           o---o-o : Page 0
 *    Order  2   1 0
 *
 * Example of requests on this pool:
 *   __find_buddy_nocheck(pool, page 0, order 0) => page 1
 *   __find_buddy_nocheck(pool, page 0, order 1) => page 2
 *   __find_buddy_nocheck(pool, page 1, order 0) => page 0
 *   __find_buddy_nocheck(pool, page 2, order 0) => page 3
 */


static struct hyp_page *__find_buddy_nocheck(struct hyp_pool *pool,
                         struct hyp_page *p,
                         u8 order)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap; 
 requires take O = RW(pool); 
  hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); 
  let start_i = (*pool).range_start / page_size (); 
  let end_i = (*pool).range_end / page_size (); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  order_aligned(p_i, order); 
  order < (*pool).max_order; 
 ensures take OR = RW(pool); 
  hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); 
  {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; 
  {*pool} unchanged; 
  let buddy_i = pfn_buddy(p_i, order); 
  let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i); 
  let in_range_buddy = buddy_i >= start_i && buddy_i < end_i; 
  let good_buddy = in_range_buddy; 
  return == (good_buddy ? buddy : NULL); 
  is_null(return) ||
  (!addr_eq(return, NULL) && cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy); @*/
{
    phys_addr_t addr = hyp_page_to_phys(p);

    /*CN*/ 
    /*@ apply find_buddy_xor(cn_hyp_page_to_pfn(__hyp_vmemmap,p), order); @*/

    addr ^= (PAGE_SIZE << order);

    /*@ assert (addr == calc_buddy(cn_hyp_page_to_pfn(__hyp_vmemmap,p) * page_size(), order)); @*/

    /*
     * Don't return a page outside the pool range -- it belongs to
     * something else and may not be mapped in hyp_vmemmap.
     */
    if (addr < pool->range_start || addr >= pool->range_end)
        return NULL;

    return hyp_phys_to_page(addr);
}

/* Find a buddy page currently available for allocation */
static struct hyp_page *__find_buddy_avail(struct hyp_pool *pool,
                       struct hyp_page *p,
                       u8 order)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap; 
 requires take O1 = RW(pool); 
  hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); 
  let start_i = (*pool).range_start / page_size(); 
  let end_i = (*pool).range_end / page_size(); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  order_aligned(p_i, order); 
  order < (*pool).max_order; 
  take V = each (u64 i; start_i <= i && i < end_i){RW(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; 
 ensures take OR = RW(pool); 
  hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset); 
  take V2 = each (u64 i; start_i <= i && i < end_i){RW(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; 
  V2 == V; 
  {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; 
  {*pool} unchanged; 
  let buddy_i = pfn_buddy(p_i, order); 
  let same_order = V2[buddy_i].order == order; 
  let zero_refcount = V2[buddy_i].refcount == 0u16; 
  let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i); 
  let in_range_buddy = buddy_i >= start_i && buddy_i < end_i; 
  let good_buddy = in_range_buddy && same_order && zero_refcount; 
  return == (good_buddy ? buddy : NULL); 
  is_null(return) || !addr_eq(return, NULL) && (cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy); @*/
{
    struct hyp_page *buddy = __find_buddy_nocheck(pool, p, order);

    /*CN*/ /*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy);@*/
    /*CN*/ /*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy);@*/
    if (!buddy || buddy->order != order || buddy->refcount)
        return NULL;

    return buddy;

}

/*
 * Pages that are available for allocation are tracked in free-lists, so we use
 * the pages themselves to store the list nodes to avoid wasting space. As the
 * allocator always returns zeroed pages (which are zeroed on the hyp_put_page()
 * path to optimize allocation speed), we also need to clean-up the list node in
 * each page when we take it out of the list.
 */
static inline void page_remove_from_list(struct hyp_page *p)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  p_i <= max_pfn (); 
  let phys = p_i * page_size(); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  take OP = RW(p); 
  let order = (*p).order; 
  order < 11u8; 
  take AP = AllocatorPage(virt, true, order); 
  let prev = AP.prev; let next = AP.next; 
  take Node_prev = O_struct_list_head(prev, prev != virt); 
  take Node_next = O_struct_list_head(next, prev != next); 
  (prev != virt) || (next == virt); 
  0i64 <= hyp_physvirt_offset; 
  (u64) hyp_physvirt_offset <= phys; phys < shift_left(1u64, 63u64); 
  (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; 
 ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {cn_virt_ptr} unchanged; 
  take OP2 = RW(p); 
  {*p} unchanged; 
  take ZP = ZeroPage(virt, true, (*p).order); 
  take Node_prev2 = O_struct_list_head(prev, prev != virt); 
  take Node_next2 = O_struct_list_head(next, prev != next); 
  (prev == next) || (Node_next2.next == Node_next.next); 
  (prev == next) || (Node_prev2.prev == Node_prev.prev); 
  (prev == virt) || (Node_prev2.next == next); 
  (prev == next) || (Node_next2.prev == prev); 
  (prev != next) || ((prev == virt) || (Node_prev2.prev == prev)); @*/
{
    struct list_head *node = CN_COPY_ALLOC_ID(hyp_page_to_virt(p), cn_virt_ptr);

    /*@ split_case (*node).prev != node; @*/
    /*@ split_case (*node).prev != (*node).next; @*/
    __list_del_entry(node);
    /*CN*//*@ apply struct_list_head_to_bytes(node); @*/
    memset(node, 0, sizeof(*node));
    /*CN*//*@ apply page_size_of_order2((*p).order); @*/
}

/* for verification */
static inline void page_remove_from_list_pool(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires take HP = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  let phys = p_i * page_size(); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  let start_i = HP.pool.range_start / page_size(); 
  let end_i = HP.pool.range_end / page_size(); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  let order = HP.vmemmap[p_i].order; 
  order != hyp_no_order (); 
  HP.vmemmap[p_i].refcount == 0u16; 
 ensures take ZP = ZeroPage(virt, true, order); 
  take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); 
  {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  H2.vmemmap == HP.vmemmap; 
  H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; @*/
{
    /*CN*/struct list_head *node = CN_COPY_ALLOC_ID(hyp_page_to_virt(p), cn_virt_ptr);
    /*CN*//*@instantiate vmemmap_l_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, node); @*/
    /*CN*//*@extract RW<struct list_head>, order; @*/
    /*CN*//*@extract RW<struct hyp_page>, p_i; @*/
    /*CN*/void *node_prev = node->prev;
    /*CN*/void *node_next = node->next;
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, node_prev); @*/
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, node_next); @*/
        /*CN*/void *free_node = &pool->free_area[p->order];
    /*CN*/if (node_prev != node) {
        /*CN*/if (node_prev != free_node)
        ;
        /*CN*/if (node_next != node_prev && node_next != free_node)
        ;
    /*CN*/};
    page_remove_from_list(p);
}

static inline void page_add_to_list(struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  let phys = p_i * page_size(); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  take Hp = RW(p); 
  let order = (*p).order; 
  order < 11u8; 
  take AP1 = ZeroPage(virt, true, order); 
  let next = head; 
  take Node_head = RW<struct list_head>(next); 
  let prev = (*next).prev; 
  ptr_eq(prev, next) || !addr_eq(prev, next); 
  take Node_prev = O_struct_list_head(prev, !addr_eq(prev, next)); 
  (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); 
  (mod((u64) hyp_physvirt_offset, page_size())) == 0u64; 
  phys > (u64) hyp_physvirt_offset; 
  p >= __hyp_vmemmap; 
 ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {cn_virt_ptr} unchanged; 
  take AP1R = AllocatorPage(virt, true, order); 
  take Hp2 = RW(p); 
  {*p} unchanged; 
  take Node_head2 = RW<struct list_head>(next); 
  take Node_prev2 = O_struct_list_head(prev, !addr_eq(prev, next)); 
  (prev == next) || (Node_prev.prev == Node_prev2.prev); 
  (prev == next) || {(*next).next} unchanged; 
  (*next).prev == virt; 
  (prev == next) || (Node_prev2.next == virt); 
  !addr_eq(prev, next) || ((*next).next == virt); 
  (AP1R.next == head); (AP1R.prev == prev); @*/
{
    struct list_head *node = CN_COPY_ALLOC_ID(hyp_page_to_virt(p), cn_virt_ptr);

    /*CN*/if (head->prev != head) {}
    /*CN*//*@ apply bytes_to_struct_list_head(node, (*p).order); @*/
    INIT_LIST_HEAD(node);
    list_add_tail(node, head);
}

static inline void page_add_to_list_pool(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires (alloc_id) __hyp_vmemmap == (alloc_id) p; 
  p >= __hyp_vmemmap; 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  take HP = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); 
  let free_area_l = member_shift<struct hyp_pool>(pool, free_area); 
  let phys = p_i * page_size(); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  let virt_i = (u64) virt / page_size(); 
  let start_i = HP.pool.range_start / page_size(); 
  let end_i = HP.pool.range_end / page_size(); 
  (u64) hyp_physvirt_offset / page_size() <= p_i; p_i < shift_left(1u64, 63u64) / page_size(); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  let order = (HP.vmemmap[p_i]).order; 
  order != (hyp_no_order ()); 
  HP.vmemmap[p_i].refcount == 0u16; 
  take ZP = ZeroPage(virt, true, order); 
  head == array_shift<struct list_head>(&(pool->free_area), order); 
 ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; 
  H2.vmemmap == HP.vmemmap; @*/
{
    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@extract RW<struct list_head>, (u64) order; @*/
    /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*/struct list_head *prev = head->prev;
    /*CN*//*@instantiate freeArea_cell_wf, (*p).order;@*/
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, virt); @*/
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, prev); @*/
    /*CN*/if (prev != head) {
        /*CN*//*@instantiate vmemmap_l_wf, cn_hyp_virt_to_pfn(hyp_physvirt_offset,prev);@*/
        /*CN*//*@extract AllocatorPage, (i64) (((u64) prev) / page_size()); @*/
        *prev;
    /*CN*/};
    /*@ assert (ptr_eq(prev, head) || !addr_eq(prev, head)); @*/
    page_add_to_list(p, head);
}

static inline void page_add_to_list_pool_ex1(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head, struct hyp_page *p_ex)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  (alloc_id) __hyp_vmemmap == (alloc_id) p; 
  let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p_ex); 
  take HP = Hyp_pool_ex2(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i, p_i2); 
  let free_area_l = member_shift<struct hyp_pool>(pool, free_area); 
  let phys = p_i * page_size(); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  let start_i = HP.pool.range_start / page_size(); 
  let end_i = HP.pool.range_end / page_size(); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p_ex); 
  let order = (HP.vmemmap[p_i]).order; 
  order != hyp_no_order (); 
  (HP.vmemmap[p_i]).refcount == 0u16; 
  take ZP = ZeroPage(virt, true, order); 
  head == array_shift<struct list_head>(&(pool->free_area), order); 
  p_i != p_i2; 
 ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i2); 
  {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  H2.pool == {free_area: H2.pool.free_area, ..HP.pool}; 
  H2.vmemmap == HP.vmemmap; @*/
{
    /*CN*//*@extract RW<struct list_head>, order;@*/
    /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*/void *prev = head->prev;
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, virt); @*/
    /*CN*//*@extract AllocatorPage, cn_hyp_virt_to_pfn(hyp_physvirt_offset, prev); @*/
    /*CN*//*@instantiate freeArea_cell_wf, (*p).order;@*/
    /*CN*/if (prev != head) {
        /*CN*//*@instantiate vmemmap_l_wf, cn_hyp_virt_to_pfn(hyp_physvirt_offset,prev);@*/
    /*CN*/};
    page_add_to_list(p, head);
}


static inline struct hyp_page *node_to_page(struct list_head *node)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset; 
 requires 0i64 <= hyp_physvirt_offset; 
  let phys = (u64) node + (u64) hyp_physvirt_offset; 
  let p_i = phys / page_size(); 
  let page = array_shift<struct hyp_page>(__hyp_vmemmap, p_i); 
  mod((u64) hyp_physvirt_offset, page_size ()) == 0u64; 
  mod((u64) __hyp_vmemmap, (u64) (sizeof<struct hyp_page>)) == 0u64; 
 ensures return == page; 
  {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
{
    return hyp_virt_to_page(node);
}

static void __hyp_attach_page(struct hyp_pool *pool,
                  struct hyp_page *p)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires (alloc_id) __hyp_vmemmap == (alloc_id) p; 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  take H = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); 
  let start_i = H.pool.range_start / page_size(); 
  let end_i = H.pool.range_end / page_size (); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  (H.vmemmap[p_i]).refcount == 0u16; 
  ((H.vmemmap[p_i]).order) != (hyp_no_order()); 
  let i_order = (H.vmemmap[p_i]).order; 
  (p_i * page_size()) + (page_size_of_order(i_order)) <= (H.pool).range_end; 
  let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); 
  take P = Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, p_i), true, i_order); 
 ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  {free_area: H2.pool.free_area, ..H.pool} == H2.pool; 
  each (u64 i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0u16) || (H2.vmemmap[i] == H.vmemmap[i])}; @*/
{
    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/

    phys_addr_t phys = hyp_page_to_phys(p);
    /* struct hyp_page *buddy; */
    struct hyp_page *buddy = NULL;
    /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    u8 order = p->order;


        /*CN*//*@ apply page_size_of_order2((*p).order); @*/
    memset(CN_COPY_ALLOC_ID(hyp_page_to_virt(p), cn_virt_ptr), 0, PAGE_SIZE << p->order);

    //if (phys < pool->range_start || phys >= pool->range_end)
    //    goto insert;
    if (!(phys < pool->range_start || phys >= pool->range_end)) {
        /*
         * Only the first struct hyp_page of a high-order page (otherwise known
         * as the 'head') should have p->order set. The non-head pages should
         * have p->order = HYP_NO_ORDER. Here @p may no longer be the head
         * after coallescing, so make sure to mark it HYP_NO_ORDER proactively.
         */
        p->order = HYP_NO_ORDER;

        for (; (order + 1) < pool->max_order; order++)
        /*@ inv (alloc_id) __hyp_vmemmap == (alloc_id) p; 
          let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
          let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i2 * page_size()); 
          take Z = ZeroPage(virt, true, order); 

          take H_I = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
          let p_page = H_I.vmemmap[p_i2]; 
         // for page_group_ok 
          each (u64 i; (start_i <= i) && (i < end_i))
            {vmemmap_wf (i, (H_I.vmemmap)[p_i2: {order: order, ..p_page}], pool, H_I.pool)}; 

          order < H_I.pool.max_order; 
          cellPointer(__hyp_vmemmap,(u64) (sizeof<struct hyp_page>),start_i,end_i,p); 
          p_page.refcount == 0u16; p_page.order == hyp_no_order (); 
          order_aligned(p_i2,order); 
          (p_i2 * page_size()) + (page_size_of_order(order)) <= (H_I.pool).range_end; 
          each (u64 i; p_i < i && i < end_i)
            {(H.vmemmap[i].refcount == 0u16) || (H_I.vmemmap[i] == H.vmemmap[i])}; 
          {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {pool} unchanged; 
          H_I.pool == {free_area: (H_I.pool).free_area, ..H.pool}; @*/
        {

            buddy = __find_buddy_avail(pool, p, order);
            if (!buddy)
                break;

            /*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy); @*/
            /*CN*//*@ apply attach_inc_loop(H_I.vmemmap,__hyp_vmemmap,*pool, p, order); @*/
            /*CN*//*@ apply lemma2(cn_hyp_page_to_pfn(__hyp_vmemmap,p), order); @*/
            /*CN*//*@ apply page_size_of_order_inc(order); @*/
            /*CN*//*@ extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
            /*CN*//*@ extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy); @*/

            /* Take the buddy out of its list, and coallesce with @p */
            page_remove_from_list_pool(pool, buddy);

            buddy->order = HYP_NO_ORDER;
            p = min(p, buddy);
        }
    }

//insert:
    /*CN*//*@instantiate freeArea_cell_wf, order;@*/
    /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    /* Mark the new head, and insert it */
    p->order = order;
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    page_add_to_list_pool(pool, p, &pool->free_area[order]);
}

static struct hyp_page *__hyp_extract_page(struct hyp_pool *pool,
                       struct hyp_page *p,
                       u8 order)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires (alloc_id) __hyp_vmemmap == (alloc_id) p; 
  take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), H.pool.range_start / page_size(), H.pool.range_end / page_size(), p); 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  let p_order = (H.vmemmap[p_i]).order; 
  H.vmemmap[p_i].refcount == 0u16; 
  (H.APs[p_i]).prev == array_shift<struct list_head>(&(pool->free_area), p_order); 
  order <= p_order; p_order != (hyp_no_order ()); 
  order_aligned(p_i, order); 
  let start_i = H.pool.range_start / (page_size()); 
  let end_i = H.pool.range_end / page_size(); 
 ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset, p_i); 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i * page_size()); 
  take ZR = ZeroPage(virt, true, order); 
  {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  H2.pool == {free_area: (H2.pool).free_area, ..H.pool}; 
  return == p; 
  let p_page = H2.vmemmap[p_i]; 
  p_page.refcount == 0u16; p_page.order == order; @*/
{
    /* struct hyp_page *buddy; */
    struct hyp_page *buddy = NULL;
    page_remove_from_list_pool(pool, p);

    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/

    /*while (p->order > order)*/
    /*CN*/while (1)

    /*@ inv let vmemmap_l = __hyp_vmemmap; 
      take H_I = Hyp_pool_ex1(pool, vmemmap_l, cn_virt_ptr, hyp_physvirt_offset, p_i); 
      H_I.pool == {free_area: H_I.pool.free_area, ..H.pool}; 
      {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
      order_aligned(p_i, order); 
      let V_I = H_I.vmemmap; 
      V_I[p_i].refcount == 0u16; 
      let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, p_i * page_size()); 
      let i_p_order = V_I[p_i].order; 
      take ZI = ZeroPage(virt, true, i_p_order); 
      order <= i_p_order; i_p_order != hyp_no_order (); i_p_order < (max_order ()); 
      {p} unchanged; {pool} unchanged; {order} unchanged; @*/
    {
        /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
        /*CN*/if (!(p->order > order)) break;
        /*
         * The buddy of order n - 1 currently has HYP_NO_ORDER as it
         * is covered by a higher-level page (whose head is @p). Use
         * __find_buddy_nocheck() to find it and inject it in the
         * free_list[n - 1], effectively splitting @p in half.
         */
        /*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
        /*CN*//*@ apply order_dec_inv((*pool).range_end, cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order, (*p).order - 1u8); @*/
        /*CN*//*@apply lemma4(cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order); @*/
        /*CN*//*@instantiate freeArea_cell_wf, (*p).order - 1u8;@*/
        /*CN*//*@ apply order_align_inv_loop(__hyp_vmemmap,V_I,*pool, p); @*/
        p->order--;
        buddy = __find_buddy_nocheck(pool, p, p->order);
        /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy);@*/
        /*CN*//*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy);@*/
        buddy->order = p->order;
        /*CN*//*@ apply extract_l(cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order); @*/
        /*CN*//*@ apply page_size_of_order_inc((*p).order); @*/
        page_add_to_list_pool_ex1(pool, buddy, &pool->free_area[buddy->order], p);
    }

    /*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
    return p;
}

static void __hyp_put_page(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap, cn_virt_ptr; 
 requires (alloc_id) __hyp_vmemmap == (alloc_id) p; 
  take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p); 
  let phys = p_i * page_size(); 
  let start_i = H.pool.range_start / (page_size()); 
  let end_i = H.pool.range_end / page_size(); 
  H.pool.range_start <= phys; phys < H.pool.range_end; 
  let refcount = (H.vmemmap[p_i]).refcount; 
  cellPointer(__hyp_vmemmap, (u64) (sizeof<struct hyp_page>), start_i, end_i, p); 
  refcount > 0u16; 
  let virt = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, phys); 
  take P = Page(virt, (refcount == 1u16), H.vmemmap[p_i].order); 
 ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; 
  H2.pool == {free_area:H2.pool.free_area, .. H.pool}; 
  each (u64 i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0u16) || (H2.vmemmap[i] == H.vmemmap[i])}; @*/
{
    /*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
    /*CN*//*@ instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
    /*CN*//*@ extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
    if (hyp_page_ref_dec_and_test(p)) {
        __hyp_attach_page(pool, p);
    }
}

/*
 * Changes to the buddy tree and page refcounts must be done with the hyp_pool
 * lock held. If a refcount change requires an update to the buddy tree (e.g.
 * hyp_put_page()), both operations must be done within the same critical
 * section to guarantee transient states (e.g. a page with null refcount but
 * not yet attached to a free list) can't be observed by well-behaved readers.
 */
void hyp_put_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap, cn_virt_ptr; 
 requires (alloc_id) addr == (alloc_id) cn_virt_ptr; 
  take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  let phys = cn__hyp_pa(hyp_physvirt_offset, addr); 
  H.pool.range_start <= phys; phys < H.pool.range_end; 
  (mod(phys,page_size())) == 0u64; addr != NULL; 
  let page_i = phys / page_size(); 
  let refcount = (H.vmemmap[page_i]).refcount; 
  refcount > 0u16; 
  take P = Page(addr, (refcount == 1u16), H.vmemmap[page_i].order); 
 ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; 
  H2.pool == {free_area: H2.pool.free_area,.. H.pool}; @*/
{
    struct hyp_page *p = hyp_virt_to_page(addr);

    /* hyp_spin_lock(&pool->lock); */
    __hyp_put_page(pool, p);
    /* hyp_spin_unlock(&pool->lock); */
}

/* void hyp_get_page(void *addr) */
void hyp_get_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap, cn_virt_ptr; 
 requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  let phys = cn__hyp_pa(hyp_physvirt_offset, addr); 
  let page_i = phys / page_size(); 
  H.pool.range_start <= phys; phys < H.pool.range_end; 
  (H.vmemmap[page_i]).refcount > 0u16; 
  (H.vmemmap[page_i]).refcount <= shift_left(1u16,16u16) - 2u16; 
 ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged; 
  H2.pool == H.pool; @*/
{
    struct hyp_page *p = hyp_virt_to_page(addr);

    /* hyp_spin_lock(&pool->lock); */
    /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
    /*CN*//*@extract RW<struct hyp_page>, page_i; @*/
    hyp_page_ref_inc(p);
    /* hyp_spin_unlock(&pool->lock); */
}

// void hyp_split_page(struct hyp_page *p)
// {
//     u8 order = p->order;
//     unsigned int i;
//
//     p->order = 0;
//     for (i = 1; i < (1 << order); i++) {
//         struct hyp_page *tail = p + i;
//
//         tail->order = 0;
//         hyp_set_page_refcounted(tail);
//     }
// }

void *hyp_alloc_pages(struct hyp_pool *pool, u8 order)
/*@ accesses hyp_physvirt_offset, __hyp_vmemmap, cn_virt_ptr; 
 requires take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  0i64 <= hyp_physvirt_offset;  // FIXME from node_to_page, suspicious
 ensures  take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset);
             take ZR = ZeroPage(return, (return != NULL), order);
             {__hyp_vmemmap} unchanged;
             {hyp_physvirt_offset} unchanged;
             H2.pool == {free_area: H2.pool.free_area, ..H.pool}; @*/
{
    struct hyp_page *p = NULL; /* struct hyp_page *p; */
    u8 i = order;
    /* ----- hyp_spin_lock(&pool- >lock); */

    /* Look for a high-enough-order page */
    while /*CN(i < pool->max_order && list_empty(&pool->free_area[i]))*/ (1)
        /*@ inv take H_I = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset);
            H_I.vmemmap == H.vmemmap; H_I.pool == H.pool;
            order <= i; H.pool.max_order <= 11u8;
            {pool} unchanged; {order} unchanged;
            {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; @*/
        /*CN*/{
            /*CN*/ /*@extract RW<struct list_head>, (u64) i;@*/
            /*CN*/ /*@instantiate freeArea_cell_wf, (u8) i;@*/
            /*CN*/if (!(i < pool->max_order && list_empty(&pool->free_area[i]))) break;
            i++;
        /*CN*/}
    if (i >= pool->max_order) {
        /* ----- hyp_spin_unlock(&pool->lock); */
    //cn_print_nr_u64(555555, 555555);
        return NULL;
    }

    /*CN*//*@ instantiate freeArea_cell_wf, (u8) i; @*/
    /*CN*//*@extract RW<struct list_head>, (u64) i;@*/
    /* Extract it from the tree at the right order */
    p = node_to_page(pool->free_area[i].next);
    // p = hyp_virt_to_page(pool->free_area[i].next);
    /*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
                /*CN*/ /*@extract RW<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
    /*CN*//*@ apply order_dec_inv(H.pool.range_end, cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order, order); @*/
    p = __hyp_extract_page(pool, p, order);
    /* ----- hyp_spin_unlock(&pool->lock); */
    /*CN*//*@ instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
    hyp_set_page_refcounted(p);
    /* ----- hyp_spin_unlock(&pool->lock); */
    //cn_print_nr_u64(666666, 666666);
    return CN_COPY_ALLOC_ID(hyp_page_to_virt(p), cn_virt_ptr);
}

#include "getorder.h"

int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
          unsigned int reserved_pages)
/*@ accesses __hyp_vmemmap, hyp_physvirt_offset, cn_virt_ptr; 
 requires nr_pages > 0u32; 
  take O = RW<struct hyp_pool>(pool); 
  let start_i = pfn; let start = start_i * page_size(); 
  let end_i = start_i + ((u64) nr_pages); let end = end_i * page_size(); 
  reserved_pages < nr_pages; 
// The hyp_pool_wf below does not mention the free area. So the
// hyp_pool_wf constraint is just a short-hand for asking start,
// end, and others to have sensible values.
  let poolv = {range_start: start, range_end: end, max_order: 11u8, ..*pool}; 
  hyp_pool_wf(pool, poolv, __hyp_vmemmap, hyp_physvirt_offset); 
  take V = each (u64 i; start_i <= i && i < end_i){RW(array_shift<struct hyp_page>(__hyp_vmemmap, i)) }; 
  let ptr_phys_0 = cn__hyp_va(cn_virt_ptr, hyp_physvirt_offset, 0u64); 
  take P = each (u64 i; start_i + ((u64) reserved_pages) <= i && i < end_i)
  { Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, i), true, 0u8) }; 
 ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; 
  take H2 = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
  (H2.pool).range_start == start; 
  (H2.pool).range_end == end; 
  (H2.pool).max_order <= 11u8; @*/
{
    phys_addr_t phys = hyp_pfn_to_phys(pfn);
    struct hyp_page *p = NULL;
    /* struct hyp_page *p; */
    int i;

    /* hyp_spin_lock_init(&pool->lock); */
    pool->max_order = min(MAX_ORDER, get_order((nr_pages + 1) << PAGE_SHIFT));
    assert(pool->max_order <= 11);
    for (i = 0; i < pool->max_order; i++)
    /*@ inv take OI = RW(pool); 
      take V2 = each (u64 j; start_i <= j && j < end_i){RW(array_shift<struct hyp_page>(__hyp_vmemmap, j))}; 
      take PI = each (u64 j; start_i + ((u64) reserved_pages) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; 
      each(u64 j; j < (u64) i){((*pool).free_area[j]).prev == array_shift<struct list_head>(pool, j) }; 
      each(u64 j; j < (u64) i){((*pool).free_area[j]).next == array_shift<struct list_head>(pool, j) }; 
      {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; 
      0i32 <= i; i <= (i32) (*pool).max_order; (*pool).max_order > 0u8; (*pool).max_order <= 11u8; 
      let order = get_order_uf(((u64) nr_pages + 1u64)*(page_size())); 
      (*pool).max_order == (11u8 < order ? 11u8 : order); 
      phys == pfn * page_size(); @*/
    {
        /*CN*/ /*@ extract RW<struct list_head>, i; @*/
        INIT_LIST_HEAD(&pool->free_area[i]);
    }
    pool->range_start = phys;
    pool->range_end = phys + (nr_pages << PAGE_SHIFT);

    /* Init the vmemmap portion */
    p = hyp_phys_to_page(phys);
    for (i = 0; i < nr_pages; i++)
    /*@ inv take OI2 = RW(pool); 
      take V3 = each (u64 j; start_i <= j && j < end_i){RW(array_shift<struct hyp_page>(__hyp_vmemmap, j)) }; 
      take PI2 = each (u64 j; start_i + ((u64) reserved_pages) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; 
      each(u8 j; j < (*pool).max_order){((*pool).free_area[(u64) j]).prev == array_shift<struct list_head>(pool, j)}; 
      each(u8 j; j < ((*pool).max_order)){((*pool).free_area[(u64) j]).next == array_shift<struct list_head>(pool, j)}; 
      each (u64 j; start_i <= j && j < start_i + (u64) i){init_vmemmap_page(j, V3, pool, *pool)}; 
      0i32 <= i; (u32) i <= nr_pages; 
      {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; 
      (*pool).range_start == start; 
      (*pool).range_end == end; 
      (*pool).max_order > 0u8; 
      (*pool).max_order <= 11u8; 
      let order = get_order_uf(((u64)nr_pages + 1u64)*(page_size())); 
      (*pool).max_order == (11u8 < order ? 11u8 : order); 
      hyp_pool_wf(pool, (*pool), __hyp_vmemmap, hyp_physvirt_offset); 
      p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn); @*/
    {
        /*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, array_shift<struct hyp_page>(p, i)); @*/
        /*CN*//*@extract RW<struct hyp_page>, pfn+((u64) i); @*/
        p[i].refcount = 0; /* added for formalisation */
        p[i].order = 0;    /* added for formalisation */
        hyp_set_page_refcounted(&p[i]);
        /*CN*//*@ apply order_aligned_init(pfn+((u64) i)); @*/
        /*CN*//*@ apply page_size_of_order_lemma (); @*/
    }

    /*CN*//*@ apply page_group_ok_easy(__hyp_vmemmap,*pool); @*/

    /* Attach the unused pages to the buddy tree */
    for (i = reserved_pages; i < nr_pages; i++)
    /*@ inv take H = Hyp_pool(pool, __hyp_vmemmap, cn_virt_ptr, hyp_physvirt_offset); 
      i >= 0i32; 
      take PI3 = each(u64 j; start_i + ((u64) i) <= j && j < end_i){ Page(array_shift<PAGE_SIZE_t>(ptr_phys_0, j), true, 0u8) }; 
      each(u64 j; start_i + (u64) i <= j && j < end_i){H.vmemmap[j].order == 0u8}; 
      each(u64 j; start_i + (u64) i <= j && j < end_i){H.vmemmap[j].refcount == 1u16}; 
      (H.pool).range_start == start; 
      (H.pool).range_end == end; 
      p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn); 
      reserved_pages <= (u32) i; (u32) i <= nr_pages; 
      {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged; 
      (H.pool).range_start == start; 
      (H.pool).range_end == end; 
      (H.pool).max_order <= 11u8; @*/
    {
        /*CN*//*@instantiate ((u64) i)+pfn;@*/
        // p[i].refcount = 0; /* added for formalisation */
        /*CN*/ /*@extract Page, start_i+((u64) i);@*/
        __hyp_put_page(pool, &p[i]);
    }
    assert(i == nr_pages);
    return 0;
}

