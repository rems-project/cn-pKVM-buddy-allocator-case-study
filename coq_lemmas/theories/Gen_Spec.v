(* theories/Gen_Spec.v: generated lemma specifications from CN *)

Require Import ZArith Bool.
Require CN_Lemmas.CN_Lib.


Module Types.

  (* no type definitions required *)

End Types.


Module Type Parameters.
  Import Types.

  Parameter order_aligned : Z -> Z -> bool.

  Parameter page_size_of_order : Z -> Z.

  Parameter page_aligned : Z -> Z -> Prop.

  Parameter pfn_buddy : Z -> Z -> Z.

  Parameter order_align : Z -> Z -> Z.

End Parameters.


Module Defs (P : Parameters).

  Import Types P.
  Open Scope Z.

  Definition get_order_1_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_1).

  Definition hyp_no_order :=
    255.

  Definition get_range_start_1_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_1).

  Definition page_group_ok (page_index : Z) (vmemmap : ((Z -> (Z * Z * Z))))
(pool : (((Z -> (Z * Z))) * Z * Z * Z)) :=
    ((get_order_1_3 (vmemmap page_index)) = (hyp_no_order) \/
(forall (i : Z),
(((1 <= i) /\ (i <= 10)) ->
(~
(((((order_align page_index i) < page_index) /\
(((get_range_start_1_4 pool) / 4096) <= (order_align page_index i))) /\
(i <= (get_order_1_3 (vmemmap (order_align page_index i))))) /\
(~ (get_order_1_3 (vmemmap (order_align page_index i))) = (hyp_no_order))))))).

  Definition fun_upd {A B : Type} (eq : A -> A -> bool) (f : A -> B) x y z :=
    if eq x z then y else f z.

  Definition upd_order_1_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) (x : T_1) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
(x_t_0,(x : T_1),x_t_2)).

  Definition get_range_end_2_4 {T_0 T_1 T_2 T_3: Type} (t : (T_0 * T_1 * T_2 * T_3)) :=
    (let '(x_t_0,x_t_1,x_t_2,x_t_3) := (t : (T_0 * T_1 * T_2 * T_3)) in
x_t_2).

  Definition get_refcount_0_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_0).

  Definition get_flags_2_3 {T_0 T_1 T_2: Type} (t : (T_0 * T_1 * T_2)) :=
    (let '(x_t_0,x_t_1,x_t_2) := (t : (T_0 * T_1 * T_2)) in
x_t_2).

  Definition struct_hyp_page_good (x : (Z * Z * Z)) :=
    ((((0 <= (get_refcount_0_3 x)) /\ ((get_refcount_0_3 x) <= 65535)) /\
((0 <= (get_order_1_3 x)) /\ ((get_order_1_3 x) <= 255))) /\
((0 <= (get_flags_2_3 x)) /\ ((get_flags_2_3 x) <= 255))).

  Definition order_dec_inv_type : Prop :=
    forall (pool_range_end : Z),

forall (pfn : Z),

forall (order1 : Z),

forall (order2 : Z),

(Is_true (order_aligned pfn order1)) -> 
(((pfn * 4096) + (page_size_of_order order1)) <= pool_range_end) -> 
(0 <= order2) -> 
(order2 <= order1) -> 
(Is_true (order_aligned pfn order2)) /\ (((pfn * 4096) + (page_size_of_order order2)) <=
pool_range_end).

  Definition lemma2_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

(0 <= order) -> 
let p_phys := (p_i * 4096) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_phys := (buddy_i * 4096) in 
(Is_true (order_aligned p_i order)) -> 
(Is_true (order_aligned buddy_i order)) -> 
let min_i := (if (p_i <? buddy_i) then p_i else buddy_i) in 
let min_i_phys := (min_i * 4096) in 
(Is_true (order_aligned min_i (order + 1))) /\ (page_aligned min_i_phys (order + 1)) /\ ((p_phys +
(page_size_of_order order)) = buddy_phys \/ (p_phys - (page_size_of_order order)) = buddy_phys).

  Definition extract_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

(0 <= order) -> 
let p_phys := (p_i * 4096) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_phys := (buddy_i * 4096) in 
(Is_true (order_aligned p_i (order + 1))) -> 
(p_phys + (page_size_of_order order)) = buddy_phys /\ (page_aligned p_phys order) /\ (page_aligned
buddy_phys order).

  Definition page_size_of_order_inc_type : Prop :=
    forall (order : Z),

(0 <= order) -> 
(page_size_of_order (order + 1)) = (2 * (page_size_of_order order)).

  Definition lemma4_type : Prop :=
    forall (p_i : Z),

forall (order : Z),

(1 <= order) -> 
let p_phys := (p_i * 4096) in 
(Is_true (order_aligned p_i order)) -> 
let buddy_i := (pfn_buddy p_i (order - 1)) in 
let buddy_phys := (buddy_i * 4096) in 
(~ (Is_true (order_aligned buddy_i order))) /\ buddy_phys =
(p_phys + (page_size_of_order (order - 1))) /\ (0 < (page_size_of_order order)) /\ (0 <
(page_size_of_order (order - 1))) /\ ((page_size_of_order (order - 1)) * 2) =
(page_size_of_order order) /\ (order_align buddy_i order) = p_i.

  Definition order_align_inv_loop_type : Prop :=
    forall (__hypvmemmap : Z),

forall (V : ((Z -> (Z * Z * Z)))),

forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (p : Z),

let hypvmemmap := __hypvmemmap in 
let p_i := ((p - __hypvmemmap) / 4) in 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
let p_order := (get_order_1_3 (V p_i)) in 
(1 <= p_order) -> 
(p_order < 11) -> 
(Is_true (order_aligned p_i p_order)) -> 
((((hypvmemmap + (4 * start_i)) <= p) /\ (p < (hypvmemmap + (4 * end_i)))) /\
((p - hypvmemmap) mod 4) = 0) -> 
let buddy_i := (pfn_buddy p_i (p_order - 1)) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (page_group_ok i V pool))) -> 
let p_new_page := (upd_order_1_3 (V p_i) (p_order - 1)) in 
let buddy_new_page := (upd_order_1_3 (V buddy_i) (p_order - 1)) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(page_group_ok i (fun_upd Z.eqb (fun_upd Z.eqb V p_i p_new_page) buddy_i buddy_new_page) pool))).

  Definition order_aligned_init_type : Prop :=
    forall (i : Z),


(Is_true (order_aligned i 0)).

  Definition page_size_of_order_type : Prop :=
    
(page_size_of_order 0) = 4096.

  Definition attach_inc_loop_type : Prop :=
    forall (V : ((Z -> (Z * Z * Z)))),

forall (__hypvmemmap : Z),

forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (p : Z),

forall (order : Z),

let hypvmemmap := __hypvmemmap in 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
((((hypvmemmap + (4 * start_i)) <= p) /\ (p < (hypvmemmap + (4 * end_i)))) /\
((p - hypvmemmap) mod 4) = 0) -> 
let p_i := ((p - __hypvmemmap) / 4) in 
let buddy_i := (pfn_buddy p_i order) in 
let buddy_order := (get_order_1_3 (V buddy_i)) in 
(start_i <= buddy_i) -> 
(buddy_i < end_i) -> 
(0 <= order) -> 
((order + 1) < 11) -> 
buddy_order = order -> 
(Is_true (order_aligned p_i order)) -> 
(Is_true (order_aligned buddy_i order)) -> 
(get_order_1_3 (V p_i)) = (hyp_no_order) -> 
let p_page_tweaked := (upd_order_1_3 (V p_i) order) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (page_group_ok i (fun_upd Z.eqb V p_i p_page_tweaked) pool))) -> 
let min_i := (if (p_i <? buddy_i) then p_i else buddy_i) in 
let min_page := (upd_order_1_3 (V min_i) (order + 1)) in 
let buddy_page := (upd_order_1_3 (V buddy_i) (hyp_no_order)) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) ->
(page_group_ok i (fun_upd Z.eqb (fun_upd Z.eqb V buddy_i buddy_page) min_i min_page) pool))).

  Definition find_buddy_xor_type : Prop :=
    forall (addr_i : Z),

forall (order : Z),

(Is_true (order_aligned addr_i order)) -> 
(0 <= order) -> 
(order < 11) -> 
(0 <= addr_i) -> 
((addr_i * 4096) < (2 ^ 64)) -> 
(0 < (2 ^ order)) /\ ((2 ^ order) < (2 ^ 11)) /\ (0 <=
(Z.lxor (addr_i * 4096) (4096 * (2 ^ order)))) /\ ((Z.lxor (addr_i * 4096) (4096 * (2 ^ order))) <
(2 ^ 64)) /\ let buddy_addr := (Z.lxor (addr_i * 4096) (4096 * (2 ^ order))) in 
let buddy_i := (buddy_addr / 4096) in 
buddy_i = (pfn_buddy addr_i order) /\ (buddy_addr mod 4096) = 0 /\ (Is_true
(order_aligned buddy_i order)) /\ (~ addr_i = buddy_i).

  Definition page_size_of_order2_type : Prop :=
    forall (order : Z),

(0 <= order) -> 
(order < 11) -> 
(0 < (2 ^ order)) /\ ((2 ^ order) < (2 ^ 11)) /\ let size := (4096 * (2 ^ order)) in 
size = (page_size_of_order order).

  Definition page_group_ok_easy_type : Prop :=
    forall (__hypvmemmap : Z),

forall (pool : (((Z -> (Z * Z))) * Z * Z * Z)),

forall (V : ((Z -> (Z * Z * Z)))),

let hypvmemmap := __hypvmemmap in 
(0 <= (get_range_start_1_4 pool)) -> 
(0 <= (get_range_end_2_4 pool)) -> 
let start_i := ((get_range_start_1_4 pool) / 4096) in 
let end_i := ((get_range_end_2_4 pool) / 4096) in 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (struct_hyp_page_good (V i)))) -> 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (get_order_1_3 (V i)) = 0)) -> 
(forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (struct_hyp_page_good (V i)))) /\ (forall (i : Z),
(((start_i <= i) /\ (i < end_i)) -> (page_group_ok i V pool))).

End Defs.


Module Type Lemma_Spec (P : Parameters).

  Module D := Defs(P).
  Import D.

  Parameter order_dec_inv : order_dec_inv_type.

  Parameter lemma2 : lemma2_type.

  Parameter extract : extract_type.

  Parameter page_size_of_order_inc : page_size_of_order_inc_type.

  Parameter lemma4 : lemma4_type.

  Parameter order_align_inv_loop : order_align_inv_loop_type.

  Parameter order_aligned_init : order_aligned_init_type.

  Parameter page_size_of_order : page_size_of_order_type.

  Parameter attach_inc_loop : attach_inc_loop_type.

  Parameter find_buddy_xor : find_buddy_xor_type.

  Parameter page_size_of_order2 : page_size_of_order2_type.

  Parameter page_group_ok_easy : page_group_ok_easy_type.

End Lemma_Spec.


