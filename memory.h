/* originally: ./arch/arm64/kvm/hyp/include/nvhe/memory.h */



/* SPDX-License-Identifier: GPL-2.0-only */
#ifndef __KVM_HYP_MEMORY_H
#define __KVM_HYP_MEMORY_H

/* #include <asm/page.h> */

/* #include <linux/types.h> */

struct hyp_pool;
struct hyp_page {
	unsigned int refcount;
	unsigned int order;
	struct hyp_pool *pool;
	struct list_head node;
};

extern s64 hyp_physvirt_offset;
extern u64 __hyp_vmemmap;
#define hyp_vmemmap ((struct hyp_page *)__hyp_vmemmap)

#define __hyp_pa(virt)	((phys_addr_t)(virt) + hyp_physvirt_offset)
#define __hyp_va(phys)	((void *)((phys_addr_t)(phys) - hyp_physvirt_offset))







static inline void *hyp_phys_to_virt(phys_addr_t phys)
/*@ accesses hyp_physvirt_offset @*/
/*@ requires let virt = phys - hyp_physvirt_offset @*/
/*@ requires 0 <= virt; virt < (power(2,64)) @*/
/*@ ensures {hyp_physvirt_offset} unchanged @*/
/*@ ensures return == ((pointer) virt) @*/
{
	return __hyp_va(phys);
}

static inline phys_addr_t hyp_virt_to_phys(void *addr)
/*@ accesses hyp_physvirt_offset @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires 0 <= phys; phys < (power(2,64)) @*/
/*@ ensures {hyp_physvirt_offset} unchanged @*/
/*@ ensures return == phys @*/
{
	return __hyp_pa(addr);
}

#define hyp_phys_to_pfn(phys)	((phys) >> PAGE_SHIFT)
#define hyp_pfn_to_phys(pfn)	((phys_addr_t)((pfn) << PAGE_SHIFT))
#define hyp_phys_to_page(phys)	(&hyp_vmemmap[hyp_phys_to_pfn(phys)])
#define hyp_virt_to_page(virt)	hyp_phys_to_page(__hyp_pa(virt))
#define hyp_virt_to_pfn(virt)	hyp_phys_to_pfn(__hyp_pa(virt))

#define hyp_page_to_pfn(page)	((struct hyp_page *)(page) - hyp_vmemmap)
#define hyp_page_to_phys(page)  hyp_pfn_to_phys((hyp_page_to_pfn(page)))
#define hyp_page_to_virt(page)	__hyp_va(hyp_page_to_phys(page))
#define hyp_page_to_pool(page)	(((struct hyp_page *)page)->pool)


/* static inline int hyp_page_count(void *addr) */
/* { */
/* 	struct hyp_page *p = hyp_virt_to_page(addr); */

/* 	return p->refcount; */
/* } */





static inline int hyp_page_count(struct hyp_pool *pool, void *addr)
/*@ accesses hyp_physvirt_offset; __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let phys = ((integer) addr) + hyp_physvirt_offset @*/
/*@ requires let H = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ requires H.pool.range_start <= phys; phys < H.pool.range_end @*/
/*@ ensures let H2 = Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset) @*/
/*@ ensures {hyp_physvirt_offset} unchanged; {hyp_vmemmap} unchanged @*/
/*@ ensures {H2.pool}@end == {H.pool}@start @*/
/*@ ensures return == ((H2.vmemmap)[phys / 4096]).refcount @*/
{
        /*CN*/unpack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
	struct hyp_page *p = hyp_virt_to_page(addr);
        /*CN*/instantiate good, hyp_page_to_pfn(p);
        /*CN*/instantiate vmemmap_b_wf, hyp_page_to_pfn(p);
	/* TODO originally: return p->refcount.  Introducing 'ret' here, so we can pack resources before returning; */
	int ret = p->refcount;

        /*CN*/pack Hyp_pool(pool, hyp_vmemmap, hyp_physvirt_offset);
        return ret;
}


#endif /* __KVM_HYP_MEMORY_H */

