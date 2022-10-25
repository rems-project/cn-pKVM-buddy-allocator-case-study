(* coq_lemmas/theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.


Module Type Parameters.

  Parameter order_aligned : Z -> Z -> bool.

  Parameter page_size_of_order : Z -> Z.

  Parameter page_aligned : Z -> Z -> Prop.

  Parameter pfn_buddy : Z -> Z -> Z.

  Parameter order_align : Z -> Z -> Z.

End Parameters.


Module Defs (P : Parameters).

  Import P.
  Open Scope Z.

  Definition get_next_0_2 {T_0 T_1: Type} (t : (T_0 * T_1)) :=
    (let '(x_t_0,x_t_1) := (t : (T_0 * T_1)) in
x_t_0).

  Definition get_free_area_0_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_0).

  Definition get_prev_1_2 {T_0 T_1: Type} (t : (T_0 * T_1)) :=
    (let '(x_t_0,x_t_1) := (t : (T_0 * T_1)) in
x_t_1).

  Definition get_range_start_1_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_1).

  Definition get_range_end_2_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_2).

  Definition get_max_order_3_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_3).

  Definition struct_hyp_pool_good (x : (((Z -> (Z * Z))) * Z * Z * Z)) :=
    ((forall (a_4485 : Z),
(((0 <= a_4485) /\ (a_4485 <= 10)) ->
(((0 <= (get_next_0_2 ((get_free_area_0_4 x) a_4485))) /\
(((((get_next_0_2 ((get_free_area_0_4 x) a_4485)) + 16) - 1) <= 18446744073709551615) /\
(((get_next_0_2 ((get_free_area_0_4 x) a_4485)) mod 8) = 0))) /\
((0 <= (get_prev_1_2 ((get_free_area_0_4 x) a_4485))) /\
(((((get_prev_1_2 ((get_free_area_0_4 x) a_4485)) + 16) - 1) <= 18446744073709551615) /\
(((get_prev_1_2 ((get_free_area_0_4 x) a_4485)) mod 8) = 0)))))) /\
(((0 <= (get_range_start_1_4 x)) /\ ((get_range_start_1_4 x) <= 18446744073709551615)) /\
(((0 <= (get_range_end_2_4 x)) /\ ((get_range_end_2_4 x) <= 18446744073709551615)) /\
((0 <= (get_max_order_3_4 x)) /\ ((get_max_order_3_4 x) <= 4294967295))))).

  Definition get_refcount_0_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_0).

  Definition get_order_1_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_1).

  Definition get_pool_2_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_2).

  Definition get_node_3_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_3).

  Definition struct_hyp_page_good (x : (Z * Z * Z * (Z * Z))) :=
    (((0 <= (get_refcount_0_4 x)) /\ ((get_refcount_0_4 x) <= 4294967295)) /\
(((0 <= (get_order_1_4 x)) /\ ((get_order_1_4 x) <= 4294967295)) /\
(((0 <= (get_pool_2_4 x)) /\
(((((get_pool_2_4 x) + 200) - 1) <= 18446744073709551615) /\ (((get_pool_2_4 x) mod 8) = 0))) /\
(((0 <= (get_next_0_2 (get_node_3_4 x))) /\
(((((get_next_0_2 (get_node_3_4 x)) + 16) - 1) <= 18446744073709551615) /\
(((get_next_0_2 (get_node_3_4 x)) mod 8) = 0))) /\
((0 <= (get_prev_1_2 (get_node_3_4 x))) /\
(((((get_prev_1_2 (get_node_3_4 x)) + 16) - 1) <= 18446744073709551615) /\
(((get_prev_1_2 (get_node_3_4 x)) mod 8) = 0))))))).

  Definition fun_upd {A B : Type} (eq : A -> A -> bool) (f : A -> B) x y z :=
    if eq x z then y else f z.

  Definition upd_order_1_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) (x : T_1) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
(x_t_0,(x : T_1),x_t_2,x_t_3)).

  Definition lemma_order_dec_inv_type : Prop :=
    forall (pool_range_end : Z),

forall (pfn : Z),

forall (order1 : Z),

forall (order2 : Z),

((0 <= pool_range_end) /\ (pool_range_end <= 18446744073709551615)) -> 
((0 <= pfn) /\ (pfn <= 18446744073709551615)) -> 
((0 <= order1) /\ (order1 <= 4294967295)) -> 
((0 <= order2) /\ (order2 <= 4294967295)) -> 
(Is_true (order_aligned pfn order1)) -> 
(((pfn * 4096) + (page_size_of_order order1)) <= pool_range_end) -> 
(0 <= order2) -> 
(order2 <= order1) -> 
(Is_true (order_aligned pfn order2)) /\ (((pfn * 4096) + (page_size_of_order order2)) <=
pool_range_end).

  Definition lemma2_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

((0 <= p_i) /\ (p_i <= 18446744073709551615)) -> 
((0 <= order) /\ (order <= 4294967295)) -> 
(0 <= order) -> 
let p_phys := (p_i * 4096) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_phys := (buddy_i * 4096) in 
(Is_true (order_aligned p_i order)) -> 
(Is_true (order_aligned buddy_i order)) -> 
let min_i := (if (p_i <? buddy_i) then p_i else buddy_i) in 
let min_i_phys := (min_i * 4096) in 
(Is_true (order_aligned min_i (order + 1))) /\ (page_aligned min_i_phys (order + 1)) /\ (((p_phys +
(page_size_of_order order)) = buddy_phys) \/ ((p_phys - (page_size_of_order order)) = buddy_phys)).

  Definition lemma_extract_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

((0 <= p_i) /\ (p_i <= 18446744073709551615)) -> 
((0 <= order) /\ (order <= 4294967295)) -> 
(0 <= order) -> 
let p_phys := (p_i * 4096) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_phys := (buddy_i * 4096) in 
(Is_true (order_aligned p_i (order + 1))) -> 
((p_phys + (page_size_of_order order)) = buddy_phys) /\ (page_aligned p_phys order) /\ (page_aligned
buddy_phys order).

  Definition lemma_page_size_of_order_inc_type : Prop :=
    forall (order : Z),

((0 <= order) /\ (order <= 4294967295)) -> 
(0 <= order) -> 
((page_size_of_order (order + 1)) = (2 * (page_size_of_order order))).

  Definition lemma4_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

((0 <= p_i) /\ (p_i <= 18446744073709551615)) -> 
((0 <= order) /\ (order <= 4294967295)) -> 
(1 <= order) -> 
let p_phys := (p_i * 4096) in 
(Is_true (order_aligned p_i order)) -> 
let buddy_i := (pfn_buddy p_i (order - 1)) in 
let buddy_phys := (buddy_i * 4096) in 
(~ (Is_true (order_aligned buddy_i order))) /\ (buddy_phys =
(p_phys + (page_size_of_order (order - 1)))) /\ (0 < (page_size_of_order order)) /\ (0 <
(page_size_of_order (order - 1))) /\ (((page_size_of_order (order - 1)) * 2) =
(page_size_of_order order)) /\ ((order_align buddy_i order) = p_i).

  Definition lemma_order_aligned_init_type : Prop :=
    forall (i : Z),

((0 <= i) /\ (i <= 18446744073709551615)) -> 
(Is_true (order_aligned i 0)).

  Definition lemma_page_size_of_order_type : Prop :=
    ((page_size_of_order 0) = 4096).

  Definition find_buddy_xor_lemma_type : Prop :=
    forall (addr_i : Z),

forall (order : Z),

((0 <= addr_i) /\ (addr_i <= 18446744073709551615)) -> 
((0 <= order) /\ (order <= 4294967295)) -> 
(Is_true (order_aligned addr_i order)) -> 
(0 <= order) -> 
(order < 11) -> 
((addr_i * 4096) < (2 ^ 64)) -> 
(0 < (2 ^ order)) /\ ((2 ^ order) < (2 ^ 11)) /\ (0 <=
(Z.lxor (addr_i * 4096) (4096 * (2 ^ order)))) /\ ((Z.lxor (addr_i * 4096) (4096 * (2 ^ order))) <
(2 ^ 64)) /\ let buddy_addr := (Z.lxor (addr_i * 4096) (4096 * (2 ^ order))) in 
let buddy_i := (buddy_addr / 4096) in 
(buddy_i = (pfn_buddy addr_i order)) /\ ((buddy_addr mod 4096) = 0) /\ (Is_true
(order_aligned buddy_i order)) /\ (~ (addr_i = buddy_i)).

  Definition page_size_of_order_lemma_type : Prop :=
    forall (order : Z),

((0 <= order) /\ (order <= 4294967295)) -> 
(0 <= order) -> 
(order < 11) -> 
(0 < (2 ^ order)) /\ ((2 ^ order) < (2 ^ 11)) /\ let size := (4096 * (2 ^ order)) in 
(size = (page_size_of_order order)).

  Definition lemma_order_align_inv_loop_type : Prop :=
    forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (p : Z),

forall (R70 : (Z)),

forall (V : (((Z -> (Z * Z * Z * (Z * Z)))))),

((Is_true true) -> ((0 <= R70) /\ (R70 <= 18446744073709551615))) -> 
(struct_hyp_pool_good pool) -> 
((0 <= p) /\ ((((p + 32) - 1) <= 18446744073709551615) /\ ((p mod 8) = 0))) -> 
let hyp_vmemmap := R70 in 
let p_i := ((p - R70) / 32) in 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
(forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) -> 
let p_order := (get_order_1_4 (V p_i)) in 
(1 <= p_order) -> 
(p_order < 11) -> 
(Is_true (order_aligned p_i p_order)) -> 
((hyp_vmemmap <= p) /\
((((p - hyp_vmemmap) mod 32) = 0) /\
((start_i <= ((p - hyp_vmemmap) / 32)) /\ (((p - hyp_vmemmap) / 32) < end_i)))) -> 
let buddy_i := (pfn_buddy p_i (p_order - 1)) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(((get_order_1_4 (V i)) = 4294967295) \/
(forall (i_0 : Z),
(((1 <= i_0) /\ (i_0 <= 10)) ->
(~
(((((order_align i i_0) < i) /\ (((get_range_start_1_4 pool) / 4096) <= (order_align i i_0))) /\
(i_0 <= (get_order_1_4 (V (order_align i i_0))))) /\
(~ ((get_order_1_4 (V (order_align i i_0))) = 4294967295))))))))) -> 
((Is_true true) -> ((0 <= R70) /\ (R70 <= 18446744073709551615))) /\ (forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) /\ let p_new_page := (upd_order_1_4
(V p_i) (p_order - 1)) in 
let buddy_new_page := (upd_order_1_4 (V buddy_i) (p_order - 1)) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(((get_order_1_4 ((fun_upd Z.eqb (fun_upd Z.eqb V p_i p_new_page) buddy_i buddy_new_page) i)) =
4294967295) \/
(forall (i_0 : Z),
(((1 <= i_0) /\ (i_0 <= 10)) ->
(~
(((((order_align i i_0) < i) /\ (((get_range_start_1_4 pool) / 4096) <= (order_align i i_0))) /\
(i_0 <=
(get_order_1_4
((fun_upd Z.eqb (fun_upd Z.eqb V p_i p_new_page) buddy_i buddy_new_page) (order_align i i_0))))) /\
(~
((get_order_1_4
((fun_upd Z.eqb (fun_upd Z.eqb V p_i p_new_page) buddy_i buddy_new_page) (order_align i i_0))) =
4294967295))))))))).

  Definition lemma_page_group_ok_easy_type : Prop :=
    forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (R72 : (Z)),

forall (V : (((Z -> (Z * Z * Z * (Z * Z)))))),

((Is_true true) -> ((0 <= R72) /\ (R72 <= 18446744073709551615))) -> 
(struct_hyp_pool_good pool) -> 
let hyp_vmemmap := R72 in 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
(forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) -> 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> ((get_order_1_4 (V i)) = 0))) -> 
((Is_true true) -> ((0 <= R72) /\ (R72 <= 18446744073709551615))) /\ (forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) /\ (forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(((get_order_1_4 (V i)) = 4294967295) \/
(forall (i_0 : Z),
(((1 <= i_0) /\ (i_0 <= 10)) ->
(~
(((((order_align i i_0) < i) /\ (((get_range_start_1_4 pool) / 4096) <= (order_align i i_0))) /\
(i_0 <= (get_order_1_4 (V (order_align i i_0))))) /\
(~ ((get_order_1_4 (V (order_align i i_0))) = 4294967295))))))))).

  Definition lemma_attach_inc_loop_type : Prop :=
    forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (p : Z),

forall (order : Z),

forall (R74 : (Z)),

forall (V : (((Z -> (Z * Z * Z * (Z * Z)))))),

((Is_true true) -> ((0 <= R74) /\ (R74 <= 18446744073709551615))) -> 
(struct_hyp_pool_good pool) -> 
((0 <= p) /\ ((((p + 32) - 1) <= 18446744073709551615) /\ ((p mod 8) = 0))) -> 
((0 <= order) /\ (order <= 4294967295)) -> 
let hyp_vmemmap := R74 in 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
((hyp_vmemmap <= p) /\
((((p - hyp_vmemmap) mod 32) = 0) /\
((start_i <= ((p - hyp_vmemmap) / 32)) /\ (((p - hyp_vmemmap) / 32) < end_i)))) -> 
(forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) -> 
let p_i := ((p - R74) / 32) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_order := (get_order_1_4 (V buddy_i)) in 
(start_i <= buddy_i) -> 
(buddy_i < end_i) -> 
(0 <= order) -> 
((order + 1) < 11) -> 
(buddy_order = order) -> 
(Is_true (order_aligned p_i order)) -> 
(Is_true (order_aligned buddy_i order)) -> 
((get_order_1_4 (V p_i)) = 4294967295) -> 
let p_page_tweaked := (upd_order_1_4 (V p_i) order) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(((get_order_1_4 ((fun_upd Z.eqb V p_i p_page_tweaked) i)) = 4294967295) \/
(forall (i_0 : Z),
(((1 <= i_0) /\ (i_0 <= 10)) ->
(~
(((((order_align i i_0) < i) /\ (((get_range_start_1_4 pool) / 4096) <= (order_align i i_0))) /\
(i_0 <= (get_order_1_4 ((fun_upd Z.eqb V p_i p_page_tweaked) (order_align i i_0))))) /\
(~ ((get_order_1_4 ((fun_upd Z.eqb V p_i p_page_tweaked) (order_align i i_0))) = 4294967295))))))))) -> 
let min_i := (if (p_i <? buddy_i) then p_i else buddy_i) in 
let min_page := (upd_order_1_4 (V min_i) (order + 1)) in 
let buddy_page := (upd_order_1_4 (V buddy_i) 4294967295) in 
((Is_true true) -> ((0 <= R74) /\ (R74 <= 18446744073709551615))) /\ (forall (i : Z),
(((0 <= i) /\ ((start_i <= i) /\ (i < end_i))) -> (struct_hyp_page_good (V i)))) /\ (forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(((get_order_1_4 ((fun_upd Z.eqb (fun_upd Z.eqb V buddy_i buddy_page) min_i min_page) i)) =
4294967295) \/
(forall (i_0 : Z),
(((1 <= i_0) /\ (i_0 <= 10)) ->
(~
(((((order_align i i_0) < i) /\ (((get_range_start_1_4 pool) / 4096) <= (order_align i i_0))) /\
(i_0 <=
(get_order_1_4
((fun_upd Z.eqb (fun_upd Z.eqb V buddy_i buddy_page) min_i min_page) (order_align i i_0))))) /\
(~
((get_order_1_4
((fun_upd Z.eqb (fun_upd Z.eqb V buddy_i buddy_page) min_i min_page) (order_align i i_0))) =
4294967295))))))))).

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter lemma_order_dec_inv : lemma_order_dec_inv_type.

  Parameter lemma2 : lemma2_type.

  Parameter lemma_extract : lemma_extract_type.

  Parameter lemma_page_size_of_order_inc : lemma_page_size_of_order_inc_type.

  Parameter lemma4 : lemma4_type.

  Parameter lemma_order_aligned_init : lemma_order_aligned_init_type.

  Parameter lemma_page_size_of_order : lemma_page_size_of_order_type.

  Parameter find_buddy_xor_lemma : find_buddy_xor_lemma_type.

  Parameter page_size_of_order_lemma : page_size_of_order_lemma_type.

  Parameter lemma_order_align_inv_loop : lemma_order_align_inv_loop_type.

  Parameter lemma_page_group_ok_easy : lemma_page_group_ok_easy_type.

  Parameter lemma_attach_inc_loop : lemma_attach_inc_loop_type.

End Lemma_Spec.


