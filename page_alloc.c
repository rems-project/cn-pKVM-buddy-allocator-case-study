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

#include "const.h"

#define PAGE_SHIFT		12 /* CP: we fix a value for PAGE_SHIFT */
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

/* NOTE: we give memset a bogus empty body to overcome a limitation of
   the current CN frontend (function declarations without body loose
   the variable name information that we rely on in the
   specifications).) */
void memset(void *b, int c, size_t len)
/*@ trusted @*/
/*@ requires let b_i = (integer) b @*/
/*@ requires take B = each (integer i; b_i <= i && i < b_i+len){Byte(array_shift<char>(NULL, i))} @*/
/*@ ensures take BR = each (integer i; b_i <= i && i < b_i+len){ByteV(array_shift<char>(NULL,i), c)} @*/
{}



struct hyp_page *__hyp_vmemmap;
/*CN*/ void *cn_virt_base;

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

#include "defs.h"
#include "lemmas.h"

static struct hyp_page *__find_buddy_nocheck(struct hyp_pool *pool,
					     struct hyp_page *p,
					     u8 order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires take O = Owned(pool) @*/
/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let start_i = (*pool).range_start / page_size () @*/
/*@ requires let end_i = (*pool).range_end / page_size () @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ ensures take OR = Owned(pool) @*/
/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures {*pool} unchanged @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order) @*/
/*@ ensures let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i) @*/
/*@ ensures let in_range_buddy = buddy_i >= start_i && buddy_i < end_i @*/
/*@ ensures let good_buddy = in_range_buddy @*/
/*@ ensures return == (good_buddy ? buddy : NULL) @*/
/*@ ensures (return == NULL) || (cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy) @*/
{
	phys_addr_t addr = hyp_page_to_phys(p);

	/*CN*/ /*@ apply find_buddy_xor(cn_hyp_page_to_pfn(__hyp_vmemmap,p), order); @*/

	addr ^= (PAGE_SIZE << order);

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
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires take O1 = Owned(pool) @*/
/*@ requires hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let start_i = (*pool).range_start / page_size() @*/
/*@ requires let end_i = (*pool).range_end / page_size() @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ requires take V = each (integer i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) } @*/
/*@ ensures take OR = Owned(pool) @*/
/*@ ensures hyp_pool_wf(pool, *pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures take V2 = each (integer i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) } @*/
/*@ ensures V2 == V @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures {*pool} unchanged @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order) @*/
/*@ ensures let addr = buddy_i * page_size () @*/
/*@ ensures let same_order = V2[buddy_i].order == order @*/
/*@ ensures let zero_refcount = V2[buddy_i].refcount == 0 @*/
/*@ ensures let buddy = array_shift<struct hyp_page>(__hyp_vmemmap, buddy_i) @*/
/*@ ensures let in_range_buddy = addr >= (*pool).range_start && addr < (*pool).range_end @*/
/*@ ensures let good_buddy = in_range_buddy && same_order && zero_refcount @*/
/*@ ensures return == (good_buddy ? buddy : NULL) @*/
/*@ ensures (return == NULL) || (cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy) @*/
{
	struct hyp_page *buddy = __find_buddy_nocheck(pool, p, order);

	/*CN*/ /*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy);@*/
	/*CN*/ /*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy);@*/
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
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires take OP = Owned(p) @*/
/*@ requires let order = (*p).order @*/
/*@ requires 0 <= order; order < 11 @*/
/*@ requires take AP = AllocatorPage(virt, 1, order) @*/
/*@ requires let prev = AP.prev; let next = AP.next @*/
/*@ requires take Node_prev = O_struct_list_head(prev, prev != virt) @*/
/*@ requires take Node_next = O_struct_list_head(next, prev != next) @*/
/*@ requires (prev != virt) || (next == virt) @*/
/*@ requires 0 <= hyp_physvirt_offset @*/
/*@ requires hyp_physvirt_offset <= phys; phys < power(2, 63) @*/
/*@ requires (mod(hyp_physvirt_offset, page_size())) == 0 @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures take OP2 = Owned(p) @*/
/*@ ensures {*p} unchanged @*/
/*@ ensures take ZP = ZeroPage(virt, 1, (*p).order) @*/
/*@ ensures take Node_prev2 = O_struct_list_head(prev, prev != virt) @*/
/*@ ensures take Node_next2 = O_struct_list_head(next, prev != next) @*/
/*@ ensures (prev == next) || (Node_next2.next == Node_next.next) @*/
/*@ ensures (prev == next) || (Node_prev2.prev == Node_prev.prev) @*/
/*@ ensures (prev == virt) || (Node_prev2.next == next) @*/
/*@ ensures (prev == next) || (Node_next2.prev == prev) @*/
/*@ ensures (prev != next) || ((prev == virt) || (Node_prev2.prev == prev)) @*/
{
	struct list_head *node = __cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base);

	      /*CN*/if (node->prev != node);
        /*CN*/if (node->prev != node->next);
	__list_del_entry(node);
	/*CN*//*@ apply struct_list_head_to_bytes(node); @*/
	memset(node, 0, sizeof(*node));
	/*CN*//*@ apply page_size_of_order2((*p).order); @*/
}

/* for verification */
static inline void page_remove_from_list_pool(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires take HP = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area) @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires let start_i = HP.pool.range_start / page_size() @*/
/*@ requires let end_i = HP.pool.range_end / page_size() @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires let order = HP.vmemmap[p_i].order @*/
/*@ requires order != hyp_no_order () @*/
/*@ requires HP.vmemmap[p_i].refcount == 0 @*/
/*@ requires let off_i = hyp_physvirt_offset / page_size() @*/
/*@ ensures take ZP = ZeroPage(virt, 1, order) @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures H2.vmemmap == HP.vmemmap @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool} @*/
{
	/*CN*/struct list_head *node = __cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base);
	/*CN*//*@instantiate vmemmap_l_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@extract AllocatorPage, ((integer) node) / (page_size()); @*/
	/*CN*//*@extract Owned<struct list_head>, order; @*/
	/*CN*//*@extract Owned<struct hyp_page>, p_i; @*/
	/*CN*/void *node_prev = node->prev;
	/*CN*/void *node_next = node->next;
	/*CN*//*@extract AllocatorPage, ((integer) node_prev) / (page_size()); @*/
	/*CN*//*@extract AllocatorPage, ((integer) node_next) / (page_size()); @*/
        /*CN*/void *free_node = &pool->free_area[p->order];
	/*CN*/if (node_prev != node) {
		/*CN*/if (node_prev != free_node);
		/*CN*/if (node_next != node_prev && node_next != free_node);
	/*CN*/};
	page_remove_from_list(p);
}

static inline void page_add_to_list(struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires take Hp = Owned(p) @*/
/*@ requires let order = (*p).order @*/
/*@ requires 0 <= order; order < 11 @*/
/*@ requires take AP1 = ZeroPage(virt, 1, order) @*/
/*@ requires let next = head @*/
/*@ requires take Node_head = Owned<struct list_head>(next) @*/
/*@ requires let prev = (*next).prev @*/
/*@ requires take Node_prev = O_struct_list_head(prev, prev != next) @*/
/*@ requires 0 <= hyp_physvirt_offset @*/
/*@ requires hyp_physvirt_offset <= phys; phys < power(2, 63) @*/
/*@ requires (mod(hyp_physvirt_offset, page_size())) == 0 @*/
/*@ requires phys > hyp_physvirt_offset @*/
/*@ requires p >= __hyp_vmemmap @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures take AP1R = AllocatorPage(virt, 1, order) @*/
/*@ ensures take Hp2 = Owned(p) @*/
/*@ ensures {*p} unchanged @*/
/*@ ensures take Node_head2 = Owned<struct list_head>(next) @*/
/*@ ensures take Node_prev2 = O_struct_list_head(prev, prev != next) @*/
/*@ ensures (prev == next) || (Node_prev.prev == Node_prev2.prev) @*/
/*@ ensures (prev == next) || {(*next).next} unchanged @*/
/*@ ensures (*next).prev == virt @*/
/*@ ensures (prev == next) || (Node_prev2.next == virt) @*/
/*@ ensures (prev != next) || ((*next).next == virt) @*/
/*@ ensures (AP1R.next == head); (AP1R.prev == prev) @*/
{
	struct list_head *node = __cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base);

	/*CN*/if (head->prev != head) {}
	/*CN*//*@ apply bytes_to_struct_list_head(node, (*p).order); @*/
	INIT_LIST_HEAD(node);
	list_add_tail(node, head);
}

static inline void page_add_to_list_pool(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires take HP = Hyp_pool_ex1(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i) @*/
/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires let start_i = HP.pool.range_start / page_size() @*/
/*@ requires let end_i = HP.pool.range_end / page_size() @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires let order = (HP.vmemmap[p_i]).order @*/
/*@ requires order != (hyp_no_order ()) @*/
/*@ requires HP.vmemmap[p_i].refcount == 0 @*/
/*@ requires take ZP = ZeroPage(virt, 1, order) @*/
/*@ requires head == array_shift<struct list_head>(&(pool->free_area), order) @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool} @*/
/*@ ensures H2.vmemmap == HP.vmemmap @*/
{
	/*CN*//*@extract Owned<struct list_head>, order; @*/
	/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*/void *prev = head->prev;
	/*CN*//*@instantiate freeArea_cell_wf, (*p).order;@*/
	/*CN*//*@extract AllocatorPage, ((integer) virt) / (page_size()); @*/
	/*CN*//*@extract AllocatorPage, ((integer) prev) / (page_size()); @*/
	/*CN*/if (prev != head) {
		/*CN*//*@instantiate vmemmap_l_wf, cn_hyp_virt_to_pfn(hyp_physvirt_offset,prev);@*/
	/*CN*/};
	page_add_to_list(p, head);
}

static inline void page_add_to_list_pool_ex1(struct hyp_pool *pool,
                struct hyp_page *p, struct list_head *head, struct hyp_page *p_ex)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p_ex) @*/
/*@ requires take HP = Hyp_pool_ex2(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i, p_i2) @*/
/*@ requires let free_area_l = member_shift<hyp_pool>(pool, free_area) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires let start_i = HP.pool.range_start / page_size() @*/
/*@ requires let end_i = HP.pool.range_end / page_size() @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p_ex) @*/
/*@ requires let order = (HP.vmemmap[p_i]).order @*/
/*@ requires order != hyp_no_order () @*/
/*@ requires (HP.vmemmap[p_i]).refcount == 0 @*/
/*@ requires take ZP = ZeroPage(virt, 1, order) @*/
/*@ requires head == array_shift<struct list_head>(&(pool->free_area), order) @*/
/*@ requires p_i != p_i2 @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i2) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area, ..HP.pool} @*/
/*@ ensures H2.vmemmap == HP.vmemmap @*/
{
	/*CN*//*@extract Owned<struct list_head>, order;@*/
	/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*/void *prev = head->prev;
	/*CN*//*@extract AllocatorPage, ((integer) virt) / (page_size()); @*/
	/*CN*//*@extract AllocatorPage, ((integer) prev) / (page_size()); @*/
	/*CN*//*@instantiate freeArea_cell_wf, (*p).order;@*/
	/*CN*/if (prev != head) {
		/*CN*//*@instantiate vmemmap_l_wf, cn_hyp_virt_to_pfn(hyp_physvirt_offset,prev);@*/
	/*CN*/};
	page_add_to_list(p, head);
}


static inline struct hyp_page *node_to_page(struct list_head *node)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset @*/
/*@ requires let phys = ((integer)node) + hyp_physvirt_offset @*/
/*@ requires phys < power(2, 64) @*/
/*@ requires let p_i = phys / page_size() @*/
/*@ requires let page = array_shift<struct hyp_page>(__hyp_vmemmap, p_i) @*/
/*@ requires ((integer) page) < power(2, 64) - 4 @*/
/*@ requires mod(hyp_physvirt_offset, page_size ()) == 0 @*/
/*@ requires mod((integer) __hyp_vmemmap, 4) == 0 @*/
/*@ requires 0 <= hyp_physvirt_offset @*/
/*@ ensures return == page @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
{
	return hyp_virt_to_page(node);
}

static void __hyp_attach_page(struct hyp_pool *pool,
			      struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires take H = Hyp_pool_ex1(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i) @*/
/*@ requires let start_i = H.pool.range_start / page_size() @*/
/*@ requires let end_i = H.pool.range_end / page_size () @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires ((H.vmemmap[p_i]).refcount) == 0 @*/
/*@ requires ((H.vmemmap[p_i]).order) != (hyp_no_order()) @*/
/*@ requires let i_order = (H.vmemmap[p_i]).order @*/
/*@ requires (p_i * page_size()) + (page_size_of_order(i_order)) <= (H.pool).range_end @*/
/*@ requires let p_offset =  p_i * page_size() - hyp_physvirt_offset - (integer) cn_virt_base @*/
/*@ requires take P = Page(array_shift<char>(cn_virt_base, p_offset), 1, i_order) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {free_area: H2.pool.free_area, ..H.pool} == H2.pool @*/
/*@ ensures each (integer i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0) || (H2.vmemmap[i] == H.vmemmap[i])} @*/
{
	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/

	phys_addr_t phys = hyp_page_to_phys(p);
	/* struct hyp_page *buddy; */
	struct hyp_page *buddy = NULL;
	/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
	u8 order = p->order;


        /*CN*//*@ apply page_size_of_order2((*p).order); @*/
	memset(__cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base), 0, PAGE_SIZE << p->order);

	//if (phys < pool->range_start || phys >= pool->range_end)
	//	goto insert;
	if (!(phys < pool->range_start || phys >= pool->range_end)) {
		/*
		 * Only the first struct hyp_page of a high-order page (otherwise known
		 * as the 'head') should have p->order set. The non-head pages should
		 * have p->order = HYP_NO_ORDER. Here @p may no longer be the head
		 * after coallescing, so make sure to mark it HYP_NO_ORDER proactively.
		 */
		p->order = HYP_NO_ORDER;

		for (; (order + 1) < pool->max_order; order++)
		/*@ inv let p_i2 = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
		/*@ inv let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, p_i2 * page_size()) @*/
		/*@ inv take Z = ZeroPage(virt, 1, order) @*/

		/*@ inv take H_I = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
		/*@ inv let p_page = H_I.vmemmap[p_i2] @*/
		/* for page_group_ok */
		/*@ inv each (integer i; (start_i <= i) && (i < end_i))
			{vmemmap_wf (i, (H_I.vmemmap)[p_i2: {order: order, ..p_page}], pool, H_I.pool)} @*/

		/*@ inv 0 <= order; order < H_I.pool.max_order @*/
		/*@ inv cellPointer(__hyp_vmemmap,sizeof<struct hyp_page>,start_i,end_i,p) @*/
		/*@ inv p_page.refcount == 0; p_page.order == hyp_no_order () @*/
		/*@ inv order_aligned(p_i2,order) @*/
		/*@ inv (p_i2 * page_size()) + (page_size_of_order(order)) <= (H_I.pool).range_end @*/
		/*@ inv each (integer i; p_i < i && i < end_i)
			{(H.vmemmap[i].refcount == 0) || (H_I.vmemmap[i] == H.vmemmap[i])} @*/
		/*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {pool} unchanged @*/
		/*@ inv H_I.pool == {free_area: (H_I.pool).free_area, ..H.pool} @*/
		{

			buddy = __find_buddy_avail(pool, p, order);
			if (!buddy)
				break;

			/*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy); @*/
			/*CN*//*@ apply attach_inc_loop(H_I.vmemmap,__hyp_vmemmap,*pool, p, order); @*/
			/*CN*//*@ apply lemma2(cn_hyp_page_to_pfn(__hyp_vmemmap,p), order); @*/
			/*CN*//*@ apply page_size_of_order_inc(order); @*/
			/*CN*//*@ extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
			/*CN*//*@ extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy); @*/

			/* Take the buddy out of its list, and coallesce with @p */
			page_remove_from_list_pool(pool, buddy);

			buddy->order = HYP_NO_ORDER;
			p = min(p, buddy);
		}
	}

//insert:
	/*CN*//*@instantiate freeArea_cell_wf, order;@*/
	/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
	/* Mark the new head, and insert it */
	p->order = order;
	/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	page_add_to_list_pool(pool, p, &pool->free_area[order]);
}

static struct hyp_page *__hyp_extract_page(struct hyp_pool *pool,
					   struct hyp_page *p,
					   u8 order)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, H.pool.range_start / page_size(), H.pool.range_end / page_size(), p) @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let p_order = (H.vmemmap[p_i]).order @*/
/*@ requires H.vmemmap[p_i].refcount == 0 @*/
/*@ requires let off_i = hyp_physvirt_offset / page_size() @*/
/*@ requires (H.APs[p_i - off_i]).prev == array_shift<struct list_head>(&(pool->free_area), p_order) @*/
/*@ requires 0 <= order; order <= p_order; p_order != (hyp_no_order ()) @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires let start_i = H.pool.range_start / (page_size()) @*/
/*@ requires let end_i = H.pool.range_end / page_size() @*/
/*@ ensures take H2 = Hyp_pool_ex1(pool, __hyp_vmemmap, hyp_physvirt_offset, p_i) @*/
/*@ ensures take ZR = ZeroPage(array_shift<char>(cn_virt_base, p_i * page_size() - hyp_physvirt_offset - (integer) cn_virt_base), 1, order) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures H2.pool == {free_area: (H2.pool).free_area, ..H.pool} @*/
/*@ ensures return == p @*/
/*@ ensures let p_page = H2.vmemmap[p_i] @*/
/*@ ensures p_page.refcount == 0; p_page.order == order @*/
/*@ ensures let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, p_i * page_size()) @*/
{
	/* struct hyp_page *buddy; */
	struct hyp_page *buddy = NULL;
	page_remove_from_list_pool(pool, p);

	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/

	/*while (p->order > order)*/
	/*CN*/while (1)

/* sigh, copying in Hyp_pool_ex1 */

	/*@ inv let vmemmap_l = __hyp_vmemmap @*/
	/*@ inv let ex = exclude_one (p_i) @*/
	/*@ inv take P_I = Owned<struct hyp_pool>(pool) @*/
	/*@ inv P_I == {free_area: P_I.free_area, ..H.pool} @*/
	/*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
	/*@ inv hyp_pool_wf (pool, P_I, vmemmap_l, hyp_physvirt_offset) @*/
	/*@ inv take V_I = each(integer i; (start_i <= i) && (i < end_i))
		{Owned(array_shift<struct hyp_page>(vmemmap_l, i))} @*/
	/*@ inv take APs = each(integer i; (start_i <= i + off_i) && (i + off_i < end_i)
			&& (V_I[i+off_i].refcount == 0)
			&& (V_I[i+off_i].order != hyp_no_order ())
			&& ((not (excluded (ex, i + off_i)))))
		{AllocatorPage(array_shift<PAGE_SIZE_t>(NULL, i), 1, (V_I[i+off_i]).order)} @*/
	/*@ inv each (integer i; (start_i <= i) && (i < end_i))
		{vmemmap_wf (i, V_I, pool, P_I)} @*/
	/*@ inv each (integer i; (start_i <= i) && (i < end_i)
			&& (V_I[i].refcount == 0)
			&& (V_I[i].order != hyp_no_order ())
			&& ((not (excluded (ex, i)))))
		{vmemmap_l_wf (i, hyp_physvirt_offset, V_I, APs, pool, P_I, ex)} @*/
	/*@ inv each(integer i; (0 <= i) && (i < P_I.max_order))
		{freeArea_cell_wf (i, hyp_physvirt_offset, V_I, APs, pool, P_I, ex)} @*/

	/*@ inv order_aligned(p_i, order) @*/
	/*@ inv V_I[p_i].refcount == 0 @*/
	/*@ inv let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, p_i * page_size()) @*/
	/*@ inv let i_p_order = V_I[p_i].order @*/
	/*@ inv take ZI = ZeroPage(virt, 1, i_p_order) @*/
	/*@ inv 0 <= order; order <= i_p_order; i_p_order != hyp_no_order (); i_p_order < (max_order ()) @*/
	/*@ inv {p} unchanged; {pool} unchanged; {order} unchanged @*/
	{
		/*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
		/*CN*/if (!(p->order > order)) break;
		/*
		 * The buddy of order n - 1 currently has HYP_NO_ORDER as it
		 * is covered by a higher-level page (whose head is @p). Use
		 * __find_buddy_nocheck() to find it and inject it in the
		 * free_list[n - 1], effectively splitting @p in half.
		 */
		/*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
		/*CN*//*@ apply order_dec_inv((*pool).range_end, cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order, (*p).order - 1); @*/
		/*CN*//*@apply lemma4(cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order); @*/
		/*CN*//*@instantiate freeArea_cell_wf, (*p).order - 1;@*/
		/*CN*//*@ apply order_align_inv_loop(__hyp_vmemmap,V_I,*pool, p); @*/
		p->order--;
		buddy = __find_buddy_nocheck(pool, p, p->order);
		/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,buddy);@*/
		            /*CN*//*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, buddy);@*/
		buddy->order = p->order;
		/*CN*//*@ apply extract_l(cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order); @*/
		/*CN*//*@ apply page_size_of_order_inc((*p).order); @*/
		page_add_to_list_pool_ex1(pool, buddy, &pool->free_area[buddy->order], p);
	}

	/*CN*//*@instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap, p);@*/
	return p;
}

static void __hyp_put_page(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_base @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let p_i = cn_hyp_page_to_pfn(__hyp_vmemmap, p) @*/
/*@ requires let phys = p_i * page_size() @*/
/*@ requires let start_i = H.pool.range_start / (page_size()) @*/
/*@ requires let end_i = H.pool.range_end / page_size() @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ requires let refcount = (H.vmemmap[p_i]).refcount @*/
/*@ requires cellPointer(__hyp_vmemmap, sizeof<struct hyp_page>, start_i, end_i, p) @*/
/*@ requires refcount > 0 @*/
/*@ requires let virt = cn__hyp_va(cn_virt_base, hyp_physvirt_offset, phys) @*/
/*@ requires take P = Page(virt, (refcount == 1) ? 1 : 0, H.vmemmap[p_i].order) @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures H2.pool == {free_area:H2.pool.free_area, .. H.pool} @*/
/*@ ensures each (integer i; p_i < i && i < end_i){(H.vmemmap[i].refcount == 0) || (H2.vmemmap[i] == H.vmemmap[i])} @*/
{
	/*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
	/*CN*//*@ instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
	/*CN*//*@ extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
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
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_base @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ requires (mod(phys,page_size())) == 0; addr != NULL @*/
/*@ requires let page_i = phys / page_size() @*/
/*@ requires let refcount = (H.vmemmap[page_i]).refcount @*/
/*@ requires refcount > 0 @*/
/*@ requires take P = Page(addr, (refcount == 1) ? 1 : 0, H.vmemmap[page_i].order) @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures H2.pool == {free_area: H2.pool.free_area,.. H.pool} @*/
{
	struct hyp_page *p = hyp_virt_to_page(addr);

	/* hyp_spin_lock(&pool->lock); */
	__hyp_put_page(pool, p);
	/* hyp_spin_unlock(&pool->lock); */
}

/* void hyp_get_page(void *addr) */
void hyp_get_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires let page_i = phys / page_size() @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ requires (H.vmemmap[page_i]).refcount > 0 @*/
/*@ requires (H.vmemmap[page_i]).refcount <= power(2,16) - 2 @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures H2.pool == H.pool @*/
{
	struct hyp_page *p = hyp_virt_to_page(addr);

	/* hyp_spin_lock(&pool->lock); */
	/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p);@*/
	/*CN*//*@extract Owned<struct hyp_page>, page_i; @*/
	hyp_page_ref_inc(p);
	/* hyp_spin_unlock(&pool->lock); */
}

// void hyp_split_page(struct hyp_page *p)
// {
// 	u8 order = p->order;
// 	unsigned int i;
//
// 	p->order = 0;
// 	for (i = 1; i < (1 << order); i++) {
// 		struct hyp_page *tail = p + i;
//
// 		tail->order = 0;
// 		hyp_set_page_refcounted(tail);
// 	}
// }

void *hyp_alloc_pages(struct hyp_pool *pool, u8 order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap; cn_virt_base @*/
/*@ requires take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures  take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset);
             take ZR = ZeroPage(return, (return == NULL) ? 0 : 1, order);
             {__hyp_vmemmap} unchanged;
             {hyp_physvirt_offset} unchanged;
             H2.pool == {free_area: H2.pool.free_area, ..H.pool} @*/
{
	struct hyp_page *p = NULL; /* struct hyp_page *p; */
	u8 i = order;
	/*CN*/ /*@extract Owned<struct list_head>, i;@*/
	/* ----- hyp_spin_lock(&pool->lock); */

	/* Look for a high-enough-order page */
	while /*CN(i < pool->max_order && list_empty(&pool->free_area[i]))*/ (1)
		/*@ inv take H_I = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset);
			H_I.vmemmap == H.vmemmap; H_I.pool == H.pool;
			order <= i; H.pool.max_order <= 11;
			{pool} unchanged; {order} unchanged;
			{__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
		/*CN*/{
			/*CN*/ /*@extract Owned<struct list_head>, i;@*/
			/*CN*/if (!(i < pool->max_order && list_empty(&pool->free_area[i]))) break;
			i++;
		/*CN*/}
	if (i >= pool->max_order) {
		/* ----- hyp_spin_unlock(&pool->lock); */
		return NULL;
	}

	/*CN*//*@ instantiate freeArea_cell_wf, i; @*/
	/*CN*//*@extract Owned<struct list_head>, i;@*/
	/* Extract it from the tree at the right order */
	p = node_to_page(pool->free_area[i].next);
	// p = hyp_virt_to_page(pool->free_area[i].next);
	/*CN*//*@ instantiate vmemmap_wf, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
				/*CN*/ /*@extract Owned<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, p); @*/
	/*CN*//*@ apply order_dec_inv(H.pool.range_end, cn_hyp_page_to_pfn(__hyp_vmemmap,p), (*p).order, order); @*/
	p = __hyp_extract_page(pool, p, order);
	/* ----- hyp_spin_unlock(&pool->lock); */
	/*CN*//*@ instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap,p); @*/
	hyp_set_page_refcounted(p);
	/* ----- hyp_spin_unlock(&pool->lock); */
	return __cerbvar_copy_alloc_id(hyp_page_to_virt(p), cn_virt_base);
}

/* NOTE: as above, we add a bogus empty body for this function, to
   work around a frontend limitation. */
static inline const int get_order(unsigned long size)
/*@ trusted @*/
/*@ requires size >= page_size() @*/
/*@ ensures return == (get_order_uf(size)) @*/
/*@ ensures return > 0 @*/
/*@ ensures return < power(2,32) @*/
{}

int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
		  unsigned int reserved_pages)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset; cn_virt_base @*/
/*@ requires nr_pages > 0 @*/
/*@ requires take O = Owned<struct hyp_pool>(pool) @*/
/*@ requires let start_i = pfn; let start = start_i * page_size() @*/
/*@ requires start_i >= 0 @*/
/*@ requires let end_i = start_i + nr_pages; let end = end_i * page_size() @*/
/*@ requires let off_i = hyp_physvirt_offset / page_size() @*/
/*@ requires (nr_pages + 1) * page_size() < power(2,32) @*/ /* because of (nr_pages + 1) << PAGE_SHIFT */
/*@ requires reserved_pages < nr_pages @*/
/* The hyp_pool_wf below does not mention the free area. So the
   hyp_pool_wf constraint is just a short-hand for asking start,
   end, and others to have sensible values. */
/*@ requires let poolv = {range_start: start, range_end: end, max_order: 11, ..*pool} @*/
/*@ requires hyp_pool_wf(pool, poolv, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires take V = each (integer i; start_i <= i && i < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, i)) } @*/
/*@ requires take P = each (integer i; start_i + reserved_pages <= (i+off_i) && (i+off_i) < end_i){ Page(array_shift<PAGE_SIZE_t>(NULL, i), 1, 0) } @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures take H2 = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures (H2.pool).range_start == start @*/
/*@ ensures (H2.pool).range_end == end @*/
/*@ ensures (H2.pool).max_order <= 11 @*/
{
	phys_addr_t phys = hyp_pfn_to_phys(pfn);
	struct hyp_page *p = NULL;
	/* struct hyp_page *p; */
	int i;

	/* hyp_spin_lock_init(&pool->lock); */
	pool->max_order = min(MAX_ORDER, get_order((nr_pages + 1) << PAGE_SHIFT));
	assert(pool->max_order <= 11);
	for (i = 0; i < pool->max_order; i++)
	/*@ inv take OI = Owned(pool) @*/
	/*@ inv take V2 = each (integer j; start_i <= j && j < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, j))} @*/
	/*@ inv 0 <= off_i; off_i < start_i @*/
	/*@ inv take PI = each (integer j; start_i + reserved_pages <= (j+off_i) && (j+off_i) < end_i){ Page(array_shift<PAGE_SIZE_t>(NULL, j), 1, 0) } @*/
	/*@ inv each(integer j; 0 <= j && j < i){((*pool).free_area[j]).prev == array_shift<struct list_head>(pool, j) } @*/
	/*@ inv each(integer j; 0 <= j && j < i){((*pool).free_area[j]).next == array_shift<struct list_head>(pool, j) } @*/
	/*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
	/*@ inv 0 <= i; i <= (*pool).max_order; (*pool).max_order > 0; (*pool).max_order <= 11 @*/
	/*@ inv (*pool).max_order == ((11 < (get_order_uf((nr_pages + 1)*page_size()))) ? 11 : (get_order_uf((nr_pages + 1)*page_size()))) @*/
	/*@ inv phys == pfn * page_size() @*/
	{
		/*CN*/ /*@ extract Owned<struct list_head>, i; @*/
		INIT_LIST_HEAD(&pool->free_area[i]);
	}
	pool->range_start = phys;
	pool->range_end = phys + (nr_pages << PAGE_SHIFT);

	/* Init the vmemmap portion */
	p = hyp_phys_to_page(phys);
	for (i = 0; i < nr_pages; i++)
	/*@ inv take OI2 = Owned(pool) @*/
	/*@ inv take V3 = each (integer j; start_i <= j && j < end_i){Owned(array_shift<struct hyp_page>(__hyp_vmemmap, j)) } @*/
	/*@ inv 0 <= off_i; off_i < start_i @*/
	/*@ inv take PI2 = each (integer j; start_i + reserved_pages <= (j+off_i) && (j+off_i) < end_i){ Page(array_shift<PAGE_SIZE_t>(NULL, j), 1, 0) } @*/
	/*@ inv each(integer j; 0 <= j && j < ((*pool).max_order)){((*pool).free_area[j]).prev == array_shift<struct list_head>(pool, j)} @*/
	/*@ inv each(integer j; 0 <= j && j < ((*pool).max_order)){((*pool).free_area[j]).next == array_shift<struct list_head>(pool, j)} @*/
	/*@ inv each (integer j; start_i <= j && j < start_i + i){init_vmemmap_page(j, V3, pool, *pool)} @*/
	/*@ inv each (integer j; start_i <= (j+off_i) && (j+off_i) < start_i + i){init_vmemmap_page(j+off_i, V3, pool, *pool)} @*/ /* to help with quantifier instantiation strategy */
	/*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
	/*@ inv (*pool).range_start == start @*/
	/*@ inv (*pool).range_end == end @*/
	/*@ inv (*pool).max_order > 0 @*/
	/*@ inv (*pool).max_order <= 11 @*/
	/*@ inv (*pool).max_order == ((11 < (get_order_uf((nr_pages + 1)*page_size()))) ? 11 : (get_order_uf((nr_pages + 1)*page_size()))) @*/
	/*@ inv hyp_pool_wf(pool, (*pool), __hyp_vmemmap, hyp_physvirt_offset) @*/
	/*@ inv p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn) @*/
	/*@ inv 0 <= i; i <= nr_pages @*/
	{
		/*CN*//*@instantiate good<struct hyp_page>, cn_hyp_page_to_pfn(__hyp_vmemmap, array_shift<struct hyp_page>(p, i)); @*/
		/*CN*//*@extract Owned<struct hyp_page>, pfn+i; @*/
		p[i].refcount = 0; /* added for formalisation */
		p[i].order = 0;    /* added for formalisation */
		hyp_set_page_refcounted(&p[i]);
		/*CN*//*@ apply order_aligned_init(pfn+i); @*/
		/*CN*//*@ apply page_size_of_order (); @*/
	}

	/*CN*//*@ apply page_group_ok_easy(__hyp_vmemmap,*pool); @*/

	/* Attach the unused pages to the buddy tree */
	for (i = reserved_pages; i < nr_pages; i++)
	/*@ inv take H = Hyp_pool(pool, __hyp_vmemmap, hyp_physvirt_offset) @*/
	/*@ inv i >= 0 @*/
	/*@ inv 0 <= off_i; off_i < start_i @*/
	/*@ inv take PI3 = each(integer j; start_i + i <= (j+off_i) && (j+off_i) < end_i){ Page(array_shift<PAGE_SIZE_t>(NULL, j), 1, 0) } @*/
	/*@ inv each(integer j; start_i + i <= j && j < end_i){H.vmemmap[j].order == 0} @*/
	/*@ inv each(integer j; start_i + i <= j && j < end_i){H.vmemmap[j].refcount == 1} @*/
	/*@ inv (H.pool).range_start == start @*/
	/*@ inv (H.pool).range_end == end @*/
	/*@ inv p == array_shift<struct hyp_page>(__hyp_vmemmap, pfn) @*/
	/*@ inv reserved_pages <= i; i <= nr_pages @*/
	/*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
	/*@ inv (H.pool).range_start == start @*/
	/*@ inv (H.pool).range_end == end @*/
	/*@ inv (H.pool).max_order <= 11 @*/
	{
		/*CN*//*@instantiate i+pfn;@*/
		// p[i].refcount = 0; /* added for formalisation */
		/*CN*/ /*@extract Page, start_i+i-off_i;@*/
		__hyp_put_page(pool, &p[i]);
	}
	assert(i == nr_pages);
	return 0;
}

// // INLINE_FUNCPTR
// struct hyp_pool host_s2_pool;
//
// void *host_s2_zalloc_pages_exact(size_t size)
// {
// 	void *addr = hyp_alloc_pages(&host_s2_pool, get_order(size));
//
// 	hyp_split_page(hyp_virt_to_page(addr));
//
// 	/*
// 	 * The size of concatenated PGDs is always a power of two of PAGE_SIZE,
// 	 * so there should be no need to free any of the tail pages to make the
// 	 * allocation exact.
// 	 */
// 	WARN_ON(size != (PAGE_SIZE << get_order(size)));
//
// 	return addr;
// }
//
// struct memblock_region hyp_memory[HYP_MEMBLOCK_REGIONS];
// unsigned int hyp_memblock_nr;
//
// struct memblock_region *find_mem_range(phys_addr_t addr, struct kvm_mem_range *range)
// {
// 	int cur, left = 0, right = hyp_memblock_nr;
// 	struct memblock_region *reg;
// 	phys_addr_t end;
//
// 	range->start = 0;
// 	range->end = ULONG_MAX;
//
// 	/* The list of memblock regions is sorted, binary search it */
// 	while (left < right) {
// 		cur = (left + right) >> 1;
// 		reg = &hyp_memory[cur];
// 		end = reg->base + reg->size;
// 		if (addr < reg->base) {
// 			right = cur;
// 			range->end = reg->base;
// 		} else if (addr >= end) {
// 			left = cur + 1;
// 			range->start = end;
// 		} else {
// 			range->start = reg->base;
// 			range->end = end;
// 			return reg;
// 		}
// 	}
//
// 	return NULL;
// }
//
// bool is_in_mem_range(u64 addr, struct kvm_mem_range *range)
// {
// 	return range->start <= addr && addr < range->end;
// }
//
// bool range_is_memory(u64 start, u64 end)
// {
// 	struct kvm_mem_range r;
//
// 	if (!find_mem_range(start, &r))
// 		return false;
//
// 	return is_in_mem_range(end - 1, &r);
// }
//
// bool host_stage2_force_pte_cb(u64 addr, u64 end, enum kvm_pgtable_prot prot)
// {
// 	/*
// 	 * Block mappings must be used with care in the host stage-2 as a
// 	 * kvm_pgtable_stage2_map() operation targeting a page in the range of
// 	 * an existing block will delete the block under the assumption that
// 	 * mappings in the rest of the block range can always be rebuilt lazily.
// 	 * That assumption is correct for the host stage-2 with RWX mappings
// 	 * targeting memory or RW mappings targeting MMIO ranges (see
// 	 * host_stage2_idmap() below which implements some of the host memory
// 	 * abort logic). However, this is not safe for any other mappings where
// 	 * the host stage-2 page-table is in fact the only place where this
// 	 * state is stored. In all those cases, it is safer to use page-level
// 	 * mappings, hence avoiding to lose the state because of side-effects in
// 	 * kvm_pgtable_stage2_map().
// 	 */
// 	if (range_is_memory(addr, end))
// 		return prot != PKVM_HOST_MEM_PROT;
// 	else
// 		return prot != PKVM_HOST_MMIO_PROT;
// }
//
// void host_s2_put_page(void *addr)
// {
// 	hyp_put_page(&host_s2_pool, addr);
// }
//
// void *host_s2_zalloc_page(void *pool)
// {
// 	return hyp_alloc_pages(pool, 0);
// }
//
// void host_s2_get_page(void *addr)
// {
// 	hyp_get_page(&host_s2_pool, addr);
// }
//
// void *hoisted_hyp_phys_to_virt(phys_addr_t phys) {
// 	return hyp_phys_to_virt(phys);
// }
//
// phys_addr_t hoisted_hyp_virt_to_phys(void* addr) {
// 	return hyp_virt_to_phys(addr);
// }
//
// int hoisted_hyp_page_count(void *addr) {
// 	return hyp_page_count(addr);
// }
//
// /* **************************************** */
// /* print page table memory operation function pointers */
//
// void dump_kvm_pgtable_mm_ops (const char *func_name, struct kvm_pgtable_mm_ops *mm_ops) {
// 	if (mm_ops) {
// 		char *f2 = (char *) func_name;
// 		hyp_puts("##### mm_ops #####");
// 		hyp_puts(f2);
// 		hyp_putsxn("zalloc_page_exact", (u64) mm_ops->zalloc_pages_exact, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("zalloc_page      ", (u64) mm_ops->zalloc_page, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("phys_to_virt     ", (u64) mm_ops->phys_to_virt, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("virt_to_phys     ", (u64) mm_ops->virt_to_phys, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("page_count       ", (u64) mm_ops->page_count, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("get_page         ", (u64) mm_ops->get_page, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("put_page         ", (u64) mm_ops->put_page, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("dcache_clean_inval_poc", (u64) mm_ops->dcache_clean_inval_poc, 64);
// 			hyp_putc('\n');
// 		hyp_putsxn("icache_inval_pou", (u64) mm_ops->icache_inval_pou, 64);
// 			hyp_putc('\n');
// 		hyp_putc('\n');
// 	}
// }
// // /INLINE_FUNCPTR
