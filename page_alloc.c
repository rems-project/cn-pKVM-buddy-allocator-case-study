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
/*@ requires let B = each (integer i; b_i <= i && i < b_i+len){Byte(((pointer) 0)+(i*1))} @*/
/*@ ensures let BR = each (integer i; b_i <= i && i < b_i+len){ByteV(((pointer) 0)+(i*1), c)} @*/
{}



u64 __hyp_vmemmap;

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
					     unsigned int order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let O = Owned(pool) @*/
/*@ requires hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let start_i = (*pool).range_start / 4096 @*/
/*@ requires let end_i = (*pool).range_end / 4096 @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ ensures let OR = Owned(pool) @*/
/*@ ensures hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures {*pool} unchanged @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order) @*/
/*@ ensures let buddy = (pointer)(__hyp_vmemmap + (buddy_i * 32)) @*/
/*@ ensures let addr = buddy_i * 4096 @*/
/*@ ensures let in_range_buddy = buddy_i >= start_i && buddy_i < end_i @*/
/*@ ensures let good_buddy = in_range_buddy @*/ 
/*@ ensures return == (good_buddy ? buddy : NULL) @*/
/*@ ensures (return == NULL) || (cellPointer(hyp_vmemmap, 32, start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy) @*/
{
	phys_addr_t addr = hyp_page_to_phys(p);

	/*CN*/ find_buddy_xor_lemma(hyp_page_to_pfn(p), order);

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
					   unsigned int order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let O1 = Owned(pool) @*/
/*@ requires hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let start_i = (*pool).range_start / 4096 @*/
/*@ requires let end_i = (*pool).range_end / 4096 @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ requires let Vmemmap = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ ensures let OR = Owned(pool) @*/
/*@ ensures hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures let Vmemmap2 = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ ensures Vmemmap2.value == {Vmemmap.value}@start @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures {*pool} unchanged @*/
/*@ ensures let buddy_i = pfn_buddy(p_i, order) @*/
/*@ ensures let addr = buddy_i * 4096 @*/
/*@ ensures let same_order = (Vmemmap2.value[buddy_i]).order == order @*/
/*@ ensures let buddy = (pointer)(__hyp_vmemmap + (buddy_i * 32)) @*/
/*@ ensures let self_pointer = (pointer) (((integer) buddy) + offsetof(hyp_page,node)) @*/
/*@ ensures let not_self_pointer = (Vmemmap2.value[buddy_i]).node.next != self_pointer @*/
/*@ ensures let in_range_buddy = addr >= (*pool).range_start && addr < (*pool).range_end @*/
/*@ ensures let good_buddy = in_range_buddy && same_order && not_self_pointer @*/
/*@ ensures return == (good_buddy ? buddy : NULL) @*/
/*@ ensures (return == NULL) || (cellPointer(hyp_vmemmap, 32, start_i, end_i, buddy) && order_aligned(buddy_i, order) && p != buddy) @*/
{
	struct hyp_page *buddy = __find_buddy_nocheck(pool, p, order);
        
        /*CN*/ instantiate good, hyp_page_to_pfn(buddy);
	if (!buddy || buddy->order != order || list_empty(&buddy->node))
		return NULL;

	return buddy;

}











static void __hyp_attach_page(struct hyp_pool *pool,
			      struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset @*/
/*@ requires let O = Owned(pool) @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let start_i = (*pool).range_start / 4096 @*/
/*@ requires let end_i = (*pool).range_end / 4096 @*/
/*@ requires let off_i = hyp_physvirt_offset / 4096 @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ requires each (integer i; start_i <= i && i < end_i){vmemmap_wf(i, hyp_vmemmap, V.value, pool, *pool)} @*/
/*@ requires each (integer i; i != p_i && start_i <= i && i < end_i){vmemmap_l_wf(i, hyp_vmemmap, V.value, pool, *pool)} @*/
/*@ requires each (integer i; 0 <= i && i < ((*pool).max_order)){freeArea_cell_wf(i, hyp_vmemmap, V.value, pool, (*pool))} @*/
/*@ requires hyp_pool_wf(pool, *pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let Zs = each (integer i; (i + off_i) != p_i && start_i <= (i + off_i) && (i + off_i) < end_i && (V.value[(i + off_i)]).refcount == 0 && (V.value[(i + off_i)]).order != (hyp_no_order ())) { ZeroPage(((pointer) 0) + (i*4096), 1, (V.value[(i + off_i)]).order) } @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires ((V.value[p_i]).refcount) == 0 @*/
/*@ requires ((V.value[p_i]).order) != (hyp_no_order ()) @*/
/*@ requires ((V.value[p_i]).pool) == pool @*/
/*@ requires ((V.value[p_i]).node.next) == &(p->node) @*/
/*@ requires ((V.value[p_i]).node.prev) == &(p->node) @*/
/*@ requires let order = (V.value[p_i]).order @*/
/*@ requires order_aligned(p_i,order) @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ requires (p_i * 4096) + (page_size_of_order(order)) <= (*pool).range_end @*/
/*@ requires let P = Page((pointer) ((p_i * 4096) - hyp_physvirt_offset), 1, order) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures let H2 = Hyp_pool(pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures ({*pool}@start){.free_area = H2.pool.free_area} == H2.pool @*/
/*@ ensures each (integer i; p_i < i && i < end_i){(({V.value[i]}@start).refcount == 0) || ((H2.vmemmap[i]) == {V.value[i]}@start)} @*/ 
{
	unsigned int order = p->order;
	/* struct hyp_page *buddy; */
	struct hyp_page *buddy = NULL;


        /*CN*/page_size_of_order_lemma(p->order);
        /*CN*/unpack Page (hyp_page_to_virt(p), 1, p->order);
	memset(hyp_page_to_virt(p), 0, PAGE_SIZE << p->order);
        /*CN*/pack ZeroPage (hyp_page_to_virt(p), 1, p->order);

	/*
	 * Only the first struct hyp_page of a high-order page (otherwise known
	 * as the 'head') should have p->order set. The non-head pages should
	 * have p->order = HYP_NO_ORDER. Here @p may no longer be the head
	 * after coallescing, so make sure to mark it HYP_NO_ORDER proactively.
	 */
	p->order = HYP_NO_ORDER;

	for (; (order + 1) < pool->max_order; order++) 
            /*@ inv let p_i2 = (((integer) p) - __hyp_vmemmap) / 32 @*/
            /*@ inv let Z = ZeroPage((pointer) ((p_i2 * 4096) - hyp_physvirt_offset), 1, order) @*/
            /*@ inv let OP = Owned(pool) @*/
            /*@ inv let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
            /*@ inv let start_i2 = (*pool).range_start / 4096 @*/
            /*@ inv let end_i2 = (*pool).range_end / 4096 @*/
            /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
            /*@ inv let V2 = each (integer i; start_i2 <= i && i < end_i2) {Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
            /*@ inv let p_page = V2.value[p_i2] @*/
            /*@ inv let p_page_tweaked2 = (p_page){.order = order} @*/
            /*@ inv each(integer i; start_i2 <= i && i < end_i2) {vmemmap_b_wf(i, hyp_vmemmap, V2.value[p_i2 = p_page_tweaked2], pool, *pool)} @*/
            /*@ inv each(integer i; 0 <= i && i < ((*pool).max_order)) {freeArea_cell_wf(i, hyp_vmemmap, V2.value, pool, (*pool))} @*/
            /*@ inv hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
            /*@ inv let R = each(integer i; start_i2 <= (i + off_i) && (i + off_i) < end_i2 && (V2.value[i + off_i]).refcount == 0 && (V2.value[i + off_i]).order != (hyp_no_order ())) { ZeroPage(((pointer) 0) + (i*4096), 1, (V2.value[i+off_i]).order) } @*/
            /*@ inv 0 <= order; order+1 <= (*pool).max_order @*/
            /*@ inv cellPointer(hyp_vmemmap,32,start_i2,end_i2,p) @*/
            /*@ inv (p_page.refcount) == 0; (p_page.order) == (hyp_no_order ()); (p_page.pool) == pool @*/
            /*@ inv (p_page.node.next) == &(p->node); (p_page.node.prev) == &(p->node) @*/
            /*@ inv order_aligned(p_i2,order) @*/
            /*@ inv (p_i2 * 4096) + (page_size_of_order(order)) <= (*pool).range_end @*/  
            /*@ inv each(integer i; {p_i}@start < i && i < end_i2) {(({V.value[i]}@start).refcount == 0) || ((V2.value[i]) == {V.value[i]}@start)} @*/ 
            /*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged; {pool} unchanged @*/ 
            /*@ inv ({*pool}@start){.free_area = (*pool).free_area} == *pool @*/
          {
		buddy = __find_buddy_avail(pool, p, order);
		if (!buddy)
			break;

                /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(buddy);
                /*CN*/unpack ZeroPage (hyp_page_to_virt(p), 1, order);
                /*CN*/unpack ZeroPage (hyp_page_to_virt(buddy), 1, order);
                /*CN*/lemma_attach_inc_loop(*pool, p, order);
                /*CN*/lemma2(hyp_page_to_pfn(p), order);
                /*CN*/lemma_page_size_of_order_inc(order);
                /*CN*/if ((buddy->node).next != &pool->free_area[order])
                /*CN*/  instantiate vmemmap_b_wf, hyp_page_to_pfn(container_of((buddy->node).next, struct hyp_page, node));
                /*CN*/if ((buddy->node).prev != &pool->free_area[order])
                /*CN*/  instantiate vmemmap_b_wf, hyp_page_to_pfn(container_of((buddy->node).prev, struct hyp_page, node));
                /*CN*/if ((buddy->node).prev != (buddy->node).next);

                /* Take the buddy out of its list, and coallesce with @p */
                list_del_init(&buddy->node);
                buddy->order = HYP_NO_ORDER;
                p = min(p, buddy);
                /*CN*/pack ZeroPage (hyp_page_to_virt(p), 1, order + 1);
	}

        /*CN*/instantiate freeArea_cell_wf, order;
        /*CN*/if (!(list_empty(&pool->free_area[order]))) {
        /*CN*/  instantiate good, hyp_page_to_pfn((pool->free_area[order]).prev);
        /*CN*/};
        p->order = order;
        list_add_tail(&p->node, &pool->free_area[order]);
        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
}

static void hyp_attach_page(struct hyp_pool *pool, struct hyp_page *p)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset @*/
/*@ requires let O = Owned(pool) @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let start_i = (*pool).range_start / 4096 @*/
/*@ requires let end_i = (*pool).range_end / 4096 @*/
/*@ requires let off_i = hyp_physvirt_offset / 4096 @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ requires each (integer i; start_i <= i && i < end_i){vmemmap_wf(i, hyp_vmemmap, V.value, pool, *pool)} @*/
/*@ requires each (integer i; (i != p_i) && start_i <= i && i < end_i){vmemmap_l_wf(i, hyp_vmemmap, V.value, pool, *pool)} @*/
/*@ requires each (integer i; 0 <= i && i < ((*pool).max_order)){freeArea_cell_wf(i, hyp_vmemmap, V.value, pool, (*pool))} @*/
/*@ requires hyp_pool_wf(pool, *pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let Zs = each (integer i; (i+off_i) != p_i && start_i <= (i+off_i) && (i+off_i) < end_i && (V.value[(i+off_i)]).refcount == 0 && (V.value[(i+off_i)]).order != (hyp_no_order ())) { ZeroPage(((pointer) 0) + (i*4096), 1, (V.value[(i+off_i)]).order) } @*/
/*@ requires cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
/*@ requires ((V.value[p_i]).refcount) == 0 @*/
/*@ requires ((V.value[p_i]).order) != (hyp_no_order ()) @*/
/*@ requires ((V.value[p_i]).pool) == pool @*/
/*@ requires ((V.value[p_i]).node.next) == &(p->node) @*/
/*@ requires ((V.value[p_i]).node.prev) == &(p->node) @*/
/*@ requires let order = (V.value[p_i]).order @*/
/*@ requires order_aligned(p_i,order) @*/
/*@ requires (p_i * 4096) + (page_size_of_order(order)) <= (*pool).range_end @*/
/*@ requires 0 <= order; order < (*pool).max_order @*/
/*@ requires let virt = (pointer) ((p_i * 4096) - hyp_physvirt_offset) @*/
/*@ requires let P = Page(virt, 1, order) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures let H2 = Hyp_pool(pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures H2.pool.range_start == {(*pool).range_start}@start @*/
/*@ ensures H2.pool.range_end == {(*pool).range_end}@start @*/
/*@ ensures H2.pool.max_order == {(*pool).max_order}@start @*/
{
	/* struct hyp_pool *pool = hyp_page_to_pool(p); */

	/* hyp_spin_lock(&pool->lock); */
	__hyp_attach_page(pool, p);
	/* hyp_spin_unlock(&pool->lock); */
}


static struct hyp_page *__hyp_extract_page(struct hyp_pool *pool,
					   struct hyp_page *p,
					   unsigned int order)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let H = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires cellPointer(hyp_vmemmap, 32, H.pool.range_start / 4096, H.pool.range_end / 4096, p) @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
/*@ requires let p_order = (H.vmemmap[p_i]).order @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires (H.vmemmap[p_i]).refcount == 0 @*/
/*@ requires ((H.vmemmap[p_i]).node.prev) == ((pointer) (((integer) &(pool->free_area)) + (p_order*16))) @*/
/*@ requires 0 <= order; order <= p_order; p_order != (hyp_no_order ()) @*/
/*@ ensures let H2 = Owned<struct hyp_pool>(pool) @*/
/*@ ensures let start_i = H2.value.range_start / 4096 @*/
/*@ ensures let end_i = H2.value.range_end / 4096 @*/
/*@ ensures let off_i = hyp_physvirt_offset / 4096 @*/
/*@ ensures let V2 = each(integer i; (start_i <= i) && (i < end_i)) {Owned<struct hyp_page>(hyp_vmemmap + i*32)} @*/
/*@ ensures each (integer i; (start_i <= i) && (i < end_i) && (i != p_i)) {vmemmap_b_wf (i, hyp_vmemmap, V2.value, pool, H2.value)} @*/
/*@ ensures each (integer i; (0 <= i) && (i < H2.value.max_order)){freeArea_cell_wf (i, hyp_vmemmap, V2.value, pool, H2.value)} @*/
/*@ ensures hyp_pool_wf (pool, H2.value, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures let zero = (pointer) 0 @*/
/*@ ensures let ZPs = each (integer i; (start_i <= i + off_i) && (i + off_i < end_i) && (i + off_i != p_i) && (((V2.value)[i+off_i]).refcount == 0) && (((V2.value)[i+off_i]).order != (hyp_no_order ()))) {ZeroPage((zero + i*4096), 1, ((V2.value)[i+off_i]).order)} @*/
/*@ ensures let ZR = ZeroPage((pointer) (p_i * 4096 - hyp_physvirt_offset), 1, order) @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures ({H.pool}@start){.free_area = H2.value.free_area} == H2.value @*/
/*@ ensures vmemmap_wf(p_i, hyp_vmemmap, V2.value, pool, H2.value) @*/
/*@ ensures return == p @*/
/*@ ensures (V2.value[p_i]).refcount == 0 @*/
/*@ ensures (V2.value[p_i]).node.next == &(p->node) @*/
/*@ ensures (V2.value[p_i]).node.prev == &(p->node) @*/
/*@ ensures (V2.value[p_i]).pool == pool @*/
/*@ ensures (V2.value[p_i]).order == order @*/
{
        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	/* struct hyp_page *buddy; */
	struct hyp_page *buddy = NULL;
        /*CN*/instantiate hyp_page_to_pfn(p);
        /*CN*/if (p->node.prev != p->node.next) { 
        /*CN*/  instantiate hyp_page_to_pfn(container_of(p->node.next, struct hyp_page, node));
        /*CN*/};
	list_del_init(&p->node);


	while (p->order > order) 
            /*@ inv let OI = Owned(pool) @*/
            /*@ inv let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
            /*@ inv let start_i = (*pool).range_start / 4096 @*/
            /*@ inv let end_i = (*pool).range_end / 4096 @*/
            /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
            /*@ inv let p_i = (((integer) p) - __hyp_vmemmap) / 32 @*/
            /*@ inv let V3 = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
            /*@ inv each (integer i; start_i <= i && i < end_i){vmemmap_b_wf(i, hyp_vmemmap, V3.value, pool, *pool)} @*/
            /*@ inv each (integer i; 0 <= i && i < ((*pool).max_order)){freeArea_cell_wf(i, hyp_vmemmap, V3.value, pool, (*pool))} @*/
            /*@ inv hyp_pool_wf(pool, *pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
            /*@ inv let ZsI = each (integer i; (p_i != (i+off_i)) && start_i <= (i+off_i) && (i+off_i) < end_i && (V3.value[(i+off_i)]).refcount == 0 && ((V3.value[(i+off_i)]).order) != (hyp_no_order ())) { ZeroPage(((pointer) 0) + (i*4096), 1, (V3.value[(i+off_i)]).order) } @*/
            /*@ inv cellPointer(hyp_vmemmap, 32, start_i, end_i, p) @*/
            /*@ inv order_aligned(p_i, order) @*/
            /*@ inv (V3.value[p_i]).refcount == 0 @*/
            /*@ inv (V3.value[p_i]).node.next == &(p->node) @*/
            /*@ inv (V3.value[p_i]).node.prev == &(p->node) @*/
            /*@ inv let p_order = (V3.value[p_i]).order @*/
            /*@ inv let ZI = ZeroPage((pointer) ((p_i * 4096) - hyp_physvirt_offset), 1, p_order) @*/
            /*@ inv 0 <= order; order <= p_order; p_order != (hyp_no_order ()) @*/
            /*@ inv {p} unchanged @*/
            /*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
            /*@ inv {pool} unchanged; {order} unchanged @*/
            /*@ inv ({H.pool}@start){.free_area = (*pool).free_area} == *pool @*/
        {
		/*
		 * The buddy of order n - 1 currently has HYP_NO_ORDER as it
		 * is covered by a higher-level page (whose head is @p). Use
		 * __find_buddy_nocheck() to find it and inject it in the
		 * free_list[n - 1], effectively splitting @p in half.
		 */
                /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(p);
                /*CN*/lemma_order_dec_inv_(pool->range_end, (u64) hyp_page_to_pfn(p), p->order);
		/*CN*/struct hyp_page *cn_buddy = __find_buddy_nocheck(pool, p, p->order - 1);
                /*CN*/lemma4(hyp_page_to_pfn(p), p->order);
                /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(cn_buddy);
                /*CN*/instantiate freeArea_cell_wf, p->order - 1;
                /*CN*/unpack ZeroPage(hyp_page_to_virt(p), 1, p->order);
                /*CN*/lemma_order_align_inv_loop(*pool, p);
		p->order--;
		buddy = __find_buddy_nocheck(pool, p, p->order);
		buddy->order = p->order;
                /*CN*/lemma_extract(hyp_page_to_pfn(p), p->order);
                /*CN*/lemma_page_size_of_order_inc(p->order);
                /*CN*/pack ZeroPage(hyp_page_to_virt(p), 1, p->order);
                /*CN*/pack ZeroPage(hyp_page_to_virt(buddy), 1, buddy->order);
                /*CN*/if (!(list_empty(&pool->free_area[buddy->order]))) {
                /*CN*/  instantiate good, hyp_page_to_pfn((pool->free_area[buddy->order]).prev);
                /*CN*/}; 
                list_add_tail(&buddy->node, &pool->free_area[buddy->order]);
	}

        /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(p);
	return p;
}

void hyp_put_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let H = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ requires (mod(phys,4096)) == 0; addr != NULL @*/
/*@ requires let page_i = phys / 4096 @*/
/*@ requires let refcount = (H.vmemmap[page_i]).refcount @*/
/*@ requires let order = (H.vmemmap[page_i]).order @*/
/*@ requires refcount > 0 @*/
/*@ requires let P = Page(addr, (refcount == 1) ? 1 : 0, order) @*/
/*@ ensures let H2 = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures H2.pool.range_start == {H.pool.range_start}@start @*/
/*@ ensures H2.pool.range_end == {H.pool.range_end}@start @*/
/*@ ensures H2.pool.max_order == {H.pool.max_order}@start @*/
{
        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	struct hyp_page *p = hyp_virt_to_page(addr);
        /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(p);
	if (hyp_page_ref_dec_and_test(p)) {
		hyp_attach_page(pool, p);
        }
        /*CN*/else {
        /*CN*/        /* prove emptiness of Page resource */
        /*CN*/        unpack Page(hyp_page_to_virt(p), 0, p->order);
        /*CN*/        pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
        /*CN*/}
}



/* void hyp_get_page(void *addr) */
void hyp_get_page(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let H = Hyp_pool(pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires let page_i =phys / 4096 @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ requires (H.vmemmap[page_i]).refcount > 0 @*/
/*@ requires (H.vmemmap[page_i]).refcount <= ((power(2,31)) - 2) @*/
/*@ ensures let H2 = Hyp_pool(pool, (pointer) __hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {__hyp_vmemmap} unchanged @*/
/*@ ensures {H2.pool}@end == {H.pool}@start @*/
{
        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	struct hyp_page *p = hyp_virt_to_page(addr);

        /*CN*/instantiate good, hyp_page_to_pfn(p);
	hyp_page_ref_inc(p);
        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
}





void *hyp_alloc_pages(struct hyp_pool *pool, unsigned int order)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let H = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures let H2 = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures let ZR = ZeroPage(return, (return == NULL) ? 0 : 1, order) @*/
/*@ ensures {__hyp_vmemmap} unchanged @*/
/*@ ensures {hyp_physvirt_offset} unchanged @*/
/*@ ensures H2.pool.range_start == {H.pool.range_start}@start @*/
/*@ ensures H2.pool.range_end == {H.pool.range_end}@start @*/
/*@ ensures H2.pool.max_order == {H.pool.max_order}@start @*/
{
	unsigned int i = order;
	/* struct hyp_page *p; */
	struct hyp_page *p = NULL;

        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);

	/* hyp_spin_lock (&pool->lock); */

	/* Look for a high-enough-order page */
	while (i < pool->max_order && list_empty(&pool->free_area[i])) 
            /*@ inv let OI = Owned(pool) @*/
            /*@ inv let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
            /*@ inv let start = {H.pool.range_start}@start @*/
            /*@ inv let end = {H.pool.range_end}@start @*/
            /*@ inv let max_order = {H.pool.max_order}@start @*/
            /*@ inv let start_i = start / 4096 @*/
            /*@ inv let end_i = end / 4096 @*/
            /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
            /*@ inv 0 <= off_i; off_i < start_i  @*/
            /*@ inv start_i >= 0 @*/
            /*@ inv let V3 = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap + (i*32)) } @*/
            /*@ inv V3.value == {H.vmemmap}@start @*/
            /*@ inv each (integer i; start_i <= i && i < end_i){vmemmap_b_wf(i, hyp_vmemmap, V3.value, pool, *pool)} @*/
            /*@ inv each (integer i; 0 <= i && i < ((*pool).max_order)){freeArea_cell_wf(i, hyp_vmemmap, V3.value, pool, *pool)} @*/
            /*@ inv hyp_pool_wf(pool, *pool, hyp_vmemmap, hyp_physvirt_offset) @*/
            /*@ inv let ZsI = each (integer i; start_i <= (i+off_i) && (i+off_i) < end_i && (V3.value[(i+off_i)]).refcount == 0 && (V3.value[(i+off_i)]).order != (hyp_no_order ())) { ZeroPage(((pointer) 0) + (i*4096), 1, (V3.value[(i+off_i)]).order) } @*/
            /*@ inv order <= i @*/
            /*@ inv max_order <= 11 @*/
            /*@ inv (*pool).range_start == start @*/
            /*@ inv (*pool).range_end == end @*/
            /*@ inv (*pool).max_order == max_order @*/
            /*@ inv {pool} unchanged; {order} unchanged @*/
            /*@ inv {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
                i++;      
	if (i >= pool->max_order) {
		/* hyp_spin_unlock(&pool->lock); */
                /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
                /*CN*/pack ZeroPage(NULL, 0, order);
		return NULL;
	}
	/* Extract it from the tree at the right order */
        /*CN*/instantiate freeArea_cell_wf, i;
	p = list_first_entry(&pool->free_area[i], struct hyp_page, node);
        /* the refcount==0 precondition needs to know wellformedness facts about the free area cell that link it to the vmemmap; */
        /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(p);
        /*CN*/lemma_order_dec_inv(pool->range_end, (u64) hyp_page_to_pfn(p), p->order, order);
        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	p = __hyp_extract_page(pool, p, order);
	/* hyp_spin_unlock(&pool->lock); */
        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	hyp_set_page_refcounted(p);
        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	return hyp_page_to_virt(p);
}




/* NOTE: as above, we add a bogus empty body for this function, to
   work around a frontend limitation. */
static inline const int get_order(unsigned long size)
/*@ trusted @*/
/*@ requires size >= 4096 @*/
/*@ ensures return == (get_order_uf(size)) @*/
/*@ ensures return > 0 @*/
/*@ ensures return < (power(2,32)) @*/
{}




int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
		  unsigned int reserved_pages)
/*@ accesses __hyp_vmemmap; hyp_physvirt_offset @*/
/*@ requires nr_pages > 0 @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let O = Owned(pool) @*/
/*@ requires let start_i = pfn; let start = start_i * 4096 @*/
/*@ requires start_i >= 0 @*/
/*@ requires let end_i = start_i + nr_pages; let end = end_i * 4096 @*/
/*@ requires let off_i = hyp_physvirt_offset / 4096 @*/
/*@ requires nr_pages * 4096 < (power(2,32)) @*/ /* because of nr_pages << PAGE_SHIFT */
/*@ requires reserved_pages < nr_pages @*/
/* The hyp_pool_wf below does not mention the free area. So the
   hyp_pool_wf constraint is just a short-hand for asking start,
   end, and others to have sensible values. */
/*@ requires let poolv = ((*pool{.range_start = start}){.range_end = end}){.max_order = 11} @*/
/*@ requires hyp_pool_wf(pool, poolv, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*32)) } @*/
/*@ requires let P = each (integer i; start_i + reserved_pages <= (i+off_i) && (i+off_i) < end_i){ Page(((pointer) 0) + (i*4096), 1, 0) } @*/
/*@ ensures {__hyp_vmemmap} unchanged; {hyp_physvirt_offset} unchanged @*/
/*@ ensures let H2 = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures (H2.pool).range_start == start @*/
/*@ ensures (H2.pool).range_end == end @*/
/*@ ensures (H2.pool).max_order <= 11 @*/
{
	phys_addr_t phys = hyp_pfn_to_phys(pfn);
	struct hyp_page *p = NULL;
	/* struct hyp_page *p; */
	int i;

	/* hyp_spin_lock_init(&pool->lock); */
	pool->max_order = min(MAX_ORDER, get_order(nr_pages << PAGE_SHIFT));
        assert(pool->max_order <= 11);
	for (i = 0; i < pool->max_order; i++) 
             /*@ inv let OI = Owned(pool) @*/
             /*@ inv let V2 = each (integer j; {start_i}@start <= j && j < {end_i}@start){Owned<struct hyp_page>({hyp_vmemmap}@start+(j*32))} @*/
             /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
             /*@ inv 0 <= off_i; off_i < {start_i}@start @*/
             /*@ inv let PI = each (integer i; {start_i + reserved_pages}@start <= (i+off_i) && (i+off_i) < {end_i}@start){ Page(((pointer) 0) + (i*4096), 1, 0) } @*/
             /*@ inv each(integer j; 0 <= j && j < i){((*pool).free_area[j]).prev == ((pointer) (((integer) pool) + (j * 16)))} @*/
             /*@ inv each(integer j; 0 <= j && j < i){((*pool).free_area[j]).next == ((pointer) (((integer) pool) + (j * 16)))} @*/
             /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
             /*@ inv 0 <= i; i <= (*pool).max_order; (*pool).max_order > 0; (*pool).max_order <= 11 @*/
             /*@ inv (*pool).max_order == ((11 < (get_order_uf(nr_pages*4096))) ? 11 : (get_order_uf(nr_pages*4096))) @*/
             /*@ inv phys == pfn * 4096 @*/
        {
		INIT_LIST_HEAD(&pool->free_area[i]);
        }
	pool->range_start = phys;
	pool->range_end = phys + (nr_pages << PAGE_SHIFT);

	/* Init the vmemmap portion */
	p = hyp_phys_to_page(phys);
	/* memset(p, 0, sizeof(*p) * nr_pages); */
	for (i = 0; i < nr_pages; i++) 
             /*@ inv let OI2 = Owned(pool) @*/
             /*@ inv let V3 = each (integer j; {start_i}@start <= j && j < {end_i}@start){Owned<struct hyp_page>({hyp_vmemmap}@start+(j*32)) } @*/
             /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
             /*@ inv 0 <= off_i; off_i < {start_i}@start @*/
             /*@ inv let PI2 = each (integer i; {start_i + reserved_pages}@start <= (i+off_i) && (i+off_i) < {end_i}@start){ Page(((pointer) 0) + (i*4096), 1, 0) } @*/
             /*@ inv each(integer j; 0 <= j && j < ((*pool).max_order)){((*pool).free_area[j]).prev == ((pointer) (((integer) pool) + (j * 16)))} @*/
             /*@ inv each(integer j; 0 <= j && j < ((*pool).max_order)){((*pool).free_area[j]).next == ((pointer) (((integer) pool) + (j * 16)))} @*/
             /*@ inv each (integer j; {start_i}@start <= j && j < {start_i}@start + i){init_vmemmap_page(j, {hyp_vmemmap}@start, V3.value, pool, *pool)} @*/
             /*@ inv each (integer j; {start_i}@start <= (j+off_i) && (j+off_i) < {start_i}@start + i){init_vmemmap_page(j+off_i, {hyp_vmemmap}@start, V3.value, pool, *pool)} @*/ /* to help with quantifier instantiation strategy */
             /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
             /*@ inv (*pool).range_start == {start}@start @*/
             /*@ inv (*pool).range_end == {end}@start @*/
             /*@ inv (*pool).max_order > 0 @*/
             /*@ inv (*pool).max_order <= 11 @*/
             /*@ inv (*pool).max_order == ((11 < (get_order_uf(nr_pages*4096))) ? 11 : (get_order_uf(nr_pages*4096))) @*/
             /*@ inv hyp_pool_wf(pool, (*pool), {hyp_vmemmap}@start, {hyp_physvirt_offset}@start) @*/
             /*@ inv p == ((pointer) (__hyp_vmemmap + (pfn*32))) @*/
             /*@ inv 0 <= i; i <= nr_pages @*/
        {
		p[i].pool = pool;
		p[i].refcount = 1; /* added for formalisation */
		p[i].order = 0;    /* added for formalisation */
                /*CN*/instantiate good, hyp_page_to_pfn(&p[i]);
		INIT_LIST_HEAD(&p[i].node);
                /*CN*/lemma_order_aligned_init(pfn+i);
                /*CN*/lemma_page_size_of_order ();
	}

        /*CN*/lemma_page_group_ok_easy(*pool);
        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);


	/* /\* Attach the unused pages to the buddy tree *\/ */
	for (i = reserved_pages; i < nr_pages; i++) 
             /*@ inv let H = Hyp_pool(pool, {hyp_vmemmap}@start, hyp_physvirt_offset) @*/
             /*@ inv i >= 0 @*/
             /*@ inv let off_i = hyp_physvirt_offset / 4096 @*/
             /*@ inv 0 <= off_i; off_i < {start_i}@start @*/
             /*@ inv let PI3 = each(integer j; {start_i}@start + i <= (j+off_i) && (j+off_i) < {end_i}@start){ Page(((pointer) 0) + (j*4096), 1, 0) } @*/
             /*@ inv each(integer j; {start_i}@start + i <= j && j < {end_i}@start){(H.vmemmap[j]).order == 0} @*/
             /*@ inv each(integer j; {start_i}@start + i <= j && j < {end_i}@start){(H.vmemmap[j]).refcount == 1} @*/
             /*@ inv (H.pool).range_start == {start}@start @*/
             /*@ inv (H.pool).range_end == {end}@start @*/
             /*@ inv p == ((pointer) (__hyp_vmemmap + (pfn*32))) @*/
             /*@ inv reserved_pages <= i; i <= nr_pages @*/
             /*@ inv {__hyp_vmemmap} unchanged; {pool} unchanged; {hyp_physvirt_offset} unchanged; {pfn} unchanged; {nr_pages} unchanged; {reserved_pages} unchanged @*/
             /*@ inv (H.pool).range_start == {start}@start @*/
             /*@ inv (H.pool).range_end == {end}@start @*/
             /*@ inv (H.pool).max_order <= 11 @*/

        {
                /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
                /*CN*/instantiate i+pfn;
		p[i].refcount = 0; /* added for formalisation */
		__hyp_attach_page(pool, &p[i]);
        }
        assert(i == nr_pages);
	return 0;
}
