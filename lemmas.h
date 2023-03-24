/* define intptr_t a hacky way, for lemmas */
/*CN*/ typedef u64 intptr_t;

lemma order_dec_inv (integer /* phys_addr_t */ pool_range_end,
                     integer /* u64 */ pfn,
                     integer /* unsigned int */ order1,
                     integer /* unsigned int */ order2) 
  requires order_aligned(pfn, order1);
           (pfn*4096) + (page_size_of_order(order1)) <= pool_range_end;
           0 <= order2; order2 <= order1
  ensures order_aligned(pfn, order2);
          (pfn * 4096) + (page_size_of_order(order2)) <= pool_range_end



lemma lemma2 (integer /* intptr_t */ p_i, integer /* unsigned int */ order)
  requires order >= 0; 
           let p_phys = p_i * 4096; 
           let buddy_i = pfn_buddy(p_i, order); 
           let buddy_phys = buddy_i * 4096; 
           order_aligned(p_i, order); 
           order_aligned(buddy_i, order) 
  ensures let min_i = (p_i < buddy_i) ? p_i : buddy_i; 
          let min_i_phys = min_i * 4096; 
          order_aligned(min_i, order+1); 
          page_aligned(min_i_phys, order+1); 
          (p_phys + (page_size_of_order(order)) == buddy_phys) || (p_phys - (page_size_of_order(order)) == buddy_phys) 


lemma extract (integer /* intptr_t */ p_i, integer /* unsigned int */ order)
 requires order >= 0 ;
          let p_phys = p_i * 4096 ;
          let buddy_i = pfn_buddy(p_i, order) ;
          let buddy_phys = buddy_i * 4096 ;
          order_aligned(p_i, order + 1)
 ensures p_phys + (page_size_of_order(order)) == buddy_phys ;
         page_aligned(p_phys, order) ;
         page_aligned(buddy_phys, order)


lemma page_size_of_order_inc (integer /* unsigned int */ order) 
  requires order >= 0 
  ensures (page_size_of_order(order+1)) == 2*(page_size_of_order(order))


lemma lemma4 (integer /* intptr_t */ p_i, integer /* unsigned int */ order)
  requires order >= 1 ;
           let p_phys = p_i * 4096 ;
           order_aligned(p_i, order)
  ensures let buddy_i = pfn_buddy(p_i, order - 1) ;
          let buddy_phys = buddy_i * 4096 ;
          !(order_aligned(buddy_i, order)) ;
          buddy_phys == p_phys + (page_size_of_order(order - 1)) ;
          0 < (page_size_of_order(order)) ;
          0 < (page_size_of_order(order - 1)) ;
          (page_size_of_order(order - 1)) * 2 == (page_size_of_order(order)) ;
          (order_align(buddy_i, order)) == p_i




lemma order_align_inv_loop (integer __hypvmemmap,
                            map<integer, struct hyp_page> V,
                            struct hyp_pool pool,
                            pointer /* struct hyp_page* */ p) 
 requires let hypvmemmap = (pointer) __hypvmemmap ;
          let p_i = (((integer) p) - __hypvmemmap) / 4 ;
          let start_i = (pool).range_start / 4096 ;
          let end_i = (pool).range_end / 4096 ;
          let p_order = (V[p_i]).order ;
          p_order >= 1; p_order < 11 ;
          order_aligned(p_i, p_order) ;
          cellPointer(hypvmemmap, 4, start_i, end_i, p) ;
          let buddy_i = pfn_buddy(p_i, p_order - 1) ;
          each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V, pool) }
 ensures let p_new_page = {order: (p_order - 1), ..V[p_i]} ;
         let buddy_new_page = {order: (p_order - 1), ..V[buddy_i]} ;
         each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V[p_i: p_new_page, buddy_i: buddy_new_page], pool) }



lemma page_group_ok_easy (integer __hypvmemmap, struct hyp_pool pool) 
  requires let hypvmemmap = (pointer) __hypvmemmap ;
           pool.range_start >= 0; pool.range_end >= 0; /* this used to be implied by the range_start and range_end uint types */
           let start_i = (pool).range_start / 4096 ;
           let end_i = (pool).range_end / 4096 ;
           take V = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hypvmemmap+(i*4)) } ;
           each (integer i; start_i <= i && i < end_i) { (V[i]).order == 0 } 
  ensures take V2 = each (integer i; start_i <= i && i < end_i) { Owned<struct hyp_page>(hypvmemmap+(i*4)) } ;
          V2 == V ;
          each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V2, pool) } 


lemma order_aligned_init (integer /* unsigned long */ i) 
  requires 0==0
  ensures order_aligned(i, 0) 

lemma page_size_of_order ()
  requires 0==0
  ensures (page_size_of_order(0)) == 4096 


lemma attach_inc_loop (map<integer, struct hyp_page> V,
                            integer __hypvmemmap,
                            struct hyp_pool pool,
                            pointer /* struct hyp_page* */ p,
                            integer /* unsigned int */ order) 
 requires let hypvmemmap = (pointer) __hypvmemmap ;
          let start_i = (pool).range_start / 4096 ;
          let end_i = (pool).range_end / 4096 ;
          cellPointer(hypvmemmap, 4, start_i, end_i, p) ;
          let p_i = (((integer) p) - __hypvmemmap) / 4 ;
          let buddy_i = pfn_buddy(p_i, order) ;
          let buddy_order = (V[buddy_i]).order ;
          start_i <= buddy_i; buddy_i < end_i ;
          0 <= order; order + 1 < 11; buddy_order == order ;
          order_aligned(p_i, order) ;
          order_aligned(buddy_i, order) ;
          (V[p_i]).order == (hyp_no_order ()) ;
          let p_page_tweaked = {order: order, ..V[p_i]} ;
          each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V[p_i: p_page_tweaked], pool) } ;
          let min_i = (p_i < buddy_i) ? p_i : buddy_i ;
          let min_page = {order: (order + 1), ..V[min_i]} ;
          let buddy_page = {order: (hyp_no_order ()), ..V[buddy_i]}
 ensures each(integer i; start_i <= i && i < end_i) { page_group_ok(i, V[buddy_i: buddy_page,min_i: min_page], pool) }



lemma find_buddy_xor(integer /* intptr_t */ addr_i, integer /* unsigned int */ order)
  requires order_aligned(addr_i, order) ;
           0 <= order; order < 11 ;
           addr_i * 4096 < (power(2, 64))
  ensures 0 < (power_uf(2, order)) ;
          (power_uf(2, order)) < (power(2, 11)) ;
          0 <= (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) ;
          (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) < (power(2, 64)) ;
          let buddy_addr = (xor_uf(addr_i * 4096, 4096 * (power_uf(2, order)))) ;
          let buddy_i = (buddy_addr / 4096) ;
          buddy_i == (pfn_buddy (addr_i, order)) ;
          (mod(buddy_addr, 4096)) == 0 ;
          order_aligned(buddy_i, order) ;
          addr_i != buddy_i


lemma page_size_of_order2(integer /* unsigned int */ order)
  requires 0 <= order; order < 11
  ensures 0 < (power_uf(2, order)) ;
          (power_uf(2, order)) < (power(2, 11)) ;
          let size = 4096 * (power_uf(2, order)) ;
          size == (page_size_of_order(order))


lemma struct_list_head_to_bytes(pointer/* struct list_head * */ node)
  requires take Node = Owned<struct list_head>(node) ;
           (integer) node >= 0  /* this should maybe not be necessary to say */
  ensures take B = each (integer i; ((integer) node) <= i && i < (((integer) node) + (sizeof_struct_list_head()))){Byte(((pointer) 0)+(i*1))} 


lemma bytes_to_struct_list_head(pointer /* struct list_head * */ node, integer /* u8 */ order)
  requires ((integer) node) >= 0 ; /* this should maybe not be necessary to say */
           let length = page_size_of_order(order) ;
           let nodeI = ((integer) node) ;
           take B = each (integer i; (nodeI <= i) && (i < (nodeI + length))) {ByteV(((pointer) 0) + (i * 1), 0)} 
  ensures take Node = Owned<struct list_head>(node) ;
          take BR = each (integer i; (nodeI + (sizeof_struct_list_head())) <= i && i < (nodeI + length)){ByteV(((pointer) 0)+(i*1), 0)} 

