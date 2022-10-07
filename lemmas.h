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
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 4 @*/
/*@ requires let start_i = (pool).range_start / 4096 @*/
/*@ requires let end_i = (pool).range_end / 4096 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*4))} @*/
/*@ requires let p_order = (V.value[p_i]).order @*/
/*@ requires p_order >= 1; p_order < 11 @*/
/*@ requires order_aligned(p_i, p_order) @*/
/*@ requires cellPointer(hyp_vmemmap, 4, start_i, end_i, p) @*/
/*@ requires let buddy_i = pfn_buddy(p_i, p_order - 1) @*/
/*@ requires each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V.value, pool) } @*/
/*@ ensures let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*4))} @*/
/*@ ensures V.value == {V.value}@start @*/
/*@ ensures let p_new_page = (V.value[p_i]){.order = (p_order - 1)} @*/
/*@ ensures let buddy_new_page = (V.value[buddy_i]){.order = (p_order - 1)} @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, (V.value[p_i = p_new_page])[buddy_i = buddy_new_page], pool) } @*/
/*@ ensures {__hyp_vmemmap} unchanged @*/
{}

void lemma_page_group_ok_easy (struct hyp_pool pool) 
/*@ trusted @*/
/*@ accesses __hyp_vmemmap @*/
/*@ requires let hyp_vmemmap = (pointer) __hyp_vmemmap @*/
/*@ requires let start_i = (pool).range_start / 4096 @*/
/*@ requires let end_i = (pool).range_end / 4096 @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hyp_vmemmap+(i*4)) } @*/
/*@ requires each (integer i; start_i <= i && i < end_i) { (V.value[i]).order == 0 } @*/
/*@ ensures let V = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hyp_vmemmap+(i*4)) } @*/
/*@ ensures V.value == {V.value}@start @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V.value, pool) } @*/
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
/*@ requires cellPointer(hyp_vmemmap, 4, start_i, end_i, p) @*/
/*@ requires let V = each (integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*4)) } @*/
/*@ requires let p_i = (((integer) p) - __hyp_vmemmap) / 4 @*/
/*@ requires let buddy_i = pfn_buddy(p_i, order) @*/
/*@ requires let buddy_order = (V.value[buddy_i]).order @*/
/*@ requires start_i <= buddy_i; buddy_i < end_i @*/
/*@ requires 0 <= order; order + 1 < 11; buddy_order == order @*/
/*@ requires order_aligned(p_i, order) @*/
/*@ requires order_aligned(buddy_i, order) @*/
/*@ requires (V.value[p_i]).order == (hyp_no_order ()) @*/
/*@ requires let p_page_tweaked = (V.value[p_i]){.order = order} @*/
/*@ requires each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V.value[p_i = p_page_tweaked], pool) } @*/
/*@ requires let min_i = (p_i < buddy_i) ? p_i : buddy_i @*/
/*@ requires let min_page = (V.value[min_i]){.order = (order + 1)} @*/
/*@ requires let buddy_page = (V.value[buddy_i]){.order = (hyp_no_order ())} @*/
/*@ ensures let V2 = each(integer i; start_i <= i && i < end_i){Owned<struct hyp_page>(hyp_vmemmap+(i*4)) } @*/
/*@ ensures V2.value == {V.value}@start @*/
/*@ ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, (V2.value[buddy_i = buddy_page])[min_i = min_page], pool) } @*/
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

void struct_list_head_to_bytes_lemma(struct list_head *node)
/*@ trusted @*/
/*@ requires let Node = Owned(node) @*/
/*@ ensures let B = each (integer i; ((integer) node) <= i && i < (((integer) node) + (sizeof_struct_list_head()))){Byte(((pointer) 0)+(i*1))} @*/
{}

