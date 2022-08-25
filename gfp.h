/* originally: ./arch/arm64/kvm/hyp/include/nvhe/gfp.h */



/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_GFP_H
#define __KVM_HYP_GFP_H

/* #include <linux/list.h> */

/* #include <nvhe/memory.h> */
/* #include <nvhe/spinlock.h> */

#define HYP_NO_ORDER	0xff

struct hyp_pool {
	/*
	 * Spinlock protecting concurrent changes to the memory pool as well as
	 * the struct hyp_page of the pool's pages until we have a proper atomic
	 * API at EL2.
	 */
	/* hyp_spinlock_t lock; */
	struct list_head free_area[MAX_ORDER];
	phys_addr_t range_start;
	phys_addr_t range_end;
	u8 max_order;
};


/* Allocation */
void *hyp_alloc_pages(struct hyp_pool *pool, u8 order);
void hyp_split_page(struct hyp_page *page);
void hyp_get_page(struct hyp_pool *pool, void *addr);
void hyp_put_page(struct hyp_pool *pool, void *addr);

/* Used pages cannot be freed */
int hyp_pool_init(struct hyp_pool *pool, u64 pfn, unsigned int nr_pages,
		  unsigned int reserved_pages);

// // INLINE_FUNCPTR
// extern struct hyp_pool host_s2_pool;
// struct kvm_mem_range {
// 	u64 start;
// 	u64 end;
// };
// struct memblock_region *find_mem_range(phys_addr_t addr, struct kvm_mem_range *range);
// bool is_in_mem_range(u64 addr, struct kvm_mem_range *range);
// bool range_is_memory(u64 start, u64 end);
//
// void *host_s2_zalloc_pages_exact(size_t size);
//
// #define _UL(x)		(_AC(x, UL))
// #define BIT(nr)			(_UL(1) << (nr))
// /* from kvm_pgtable.h */
// /**
//  * enum kvm_pgtable_prot - Page-table permissions and attributes.
//  * @KVM_PGTABLE_PROT_X:		Execute permission.
//  * @KVM_PGTABLE_PROT_W:		Write permission.
//  * @KVM_PGTABLE_PROT_R:		Read permission.
//  * @KVM_PGTABLE_PROT_DEVICE:	Device attributes.
//  * @KVM_PGTABLE_PROT_SW0:	Software bit 0.
//  * @KVM_PGTABLE_PROT_SW1:	Software bit 1.
//  * @KVM_PGTABLE_PROT_SW2:	Software bit 2.
//  * @KVM_PGTABLE_PROT_SW3:	Software bit 3.
//  */
// enum kvm_pgtable_prot {
// 	KVM_PGTABLE_PROT_X			= BIT(0),
// 	KVM_PGTABLE_PROT_W			= BIT(1),
// 	KVM_PGTABLE_PROT_R			= BIT(2),
//
// 	KVM_PGTABLE_PROT_DEVICE			= BIT(3),
//
// 	KVM_PGTABLE_PROT_SW0			= BIT(55),
// 	KVM_PGTABLE_PROT_SW1			= BIT(56),
// 	KVM_PGTABLE_PROT_SW2			= BIT(57),
// 	KVM_PGTABLE_PROT_SW3			= BIT(58),
// };
//
// bool host_stage2_force_pte_cb(u64 addr, u64 end, enum kvm_pgtable_prot prot);
// void host_s2_put_page(void *addr);
// void *host_s2_zalloc_page(void *pool);
// void host_s2_get_page(void *addr);
// // /INLINE_FUNCPTR

#endif /* __KVM_HYP_GFP_H */
