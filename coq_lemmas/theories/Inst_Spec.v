(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool Lia.
Require CN_Lemmas.Pages_Aligned CN_Lemmas.Gen_Spec.

Module Inst.

  Definition order_align := CN_Lemmas.Buddy_Aligned.order_align.

  Definition order_aligned := CN_Lemmas.Buddy_Aligned.order_aligned_b.

  Definition page_size_of_order := CN_Lemmas.Pages_Aligned.page_size_of_order.

  Definition pfn_buddy := CN_Lemmas.Buddy_Aligned.buddy.

  Definition pages_no_overlap : ((Z -> Z * Z * Z * (Z * Z)) -> Z -> Z -> Prop)
    := CN_Lemmas.Pages_Aligned.pages_no_overlap.

  Definition page_aligned := CN_Lemmas.Pages_Aligned.page_aligned.

End Inst.

Module Defs := CN_Lemmas.Gen_Spec.Defs (Inst).

Module Proofs.

(* now prove lemmas *)
Import Defs Inst CN_Lemmas.Pages_Aligned CN_Lemmas.Buddy_Aligned.
Open Scope Z.

Lemma le_triv:
  forall n m, n <= m -> n <= m.
Proof.
  auto.
Qed.

Ltac lia_ineq :=
  match goal with
    | |- (_ <= _) => lia
    | |- (_ < _) => lia
    | _ => try fail
  end.

Ltac order_aligned_b1 :=
  match goal with H : Is_true (order_aligned_b _ _) |- _
    => apply order_aligned_b_true1 in H; lia_ineq
  | |- Is_true (order_aligned_b _ _)
    => apply order_aligned_b_true2; lia_ineq
  | _ => fail
  end.
Ltac order_aligned_b := repeat order_aligned_b1.

Lemma order_dec_inv: order_dec_inv_type.
Proof.
  unfold order_dec_inv_type, Inst.order_aligned, Inst.page_size_of_order.

  intros.
  constructor; order_aligned_b.
  -
    apply order_aligned_sz_mono with (order1 := order1); auto.
  -
    pose (p := page_size_of_order_mono order2 order1).
    apply le_triv in p; lia.
Qed.

Lemma lemma2: lemma2_type.
Proof.
  unfold lemma2_type, Inst.order_aligned, Inst.page_size_of_order,
      Inst.pfn_buddy, Inst.page_aligned.
  intros.
  order_aligned_b.
  rewrite buddy_lt_eq by lia.
  match goal with |- ?x /\ _ => assert x end.
    destruct (order_aligned_b p_i (order + 1)) eqn:al; auto using Is_true_eq_left.
    order_aligned_b.
    apply buddy_higher_aligned; auto; lia.
  constructor; auto.
  constructor.
    apply page_aligned_times_4096; try lia.
    order_aligned_b.
    auto.
  apply pfn_add_sub_eq_pfn_times_4096; try lia.
Qed.

Lemma extract_l: extract_l_type.
Proof.
  unfold extract_l_type, Inst.order_aligned,
      Inst.page_size_of_order, Inst.pfn_buddy, Inst.page_aligned.
  intros.
  constructor.
    apply Is_true_eq_true in H0.
    unfold buddy.
    rewrite H0.
    rewrite Z.mul_add_distr_r, page_size_of_order_times_4096; auto.
  order_aligned_b.
  constructor; apply page_aligned_times_4096; try lia.
    apply order_aligned_sz_mono with (order1 := order + 1);
      auto; lia.
  apply order_aligned_buddy; try lia.
  apply order_aligned_sz_mono with (order1 := order + 1);
    auto; lia.
Qed.

Lemma page_size_of_order_inc: page_size_of_order_inc_type.
Proof.
  unfold page_size_of_order_inc_type, Inst.page_size_of_order.
  intros.
  apply page_size_of_order_inc.
  lia.
Qed.

Lemma lemma4: lemma4_type.
Proof.
  unfold lemma4_type, Inst.order_aligned, Inst.pfn_buddy,
      Inst.page_size_of_order, Inst.order_align.
  intros.
  rewrite<- page_size_of_order_inc2, Z.sub_simpl_r by lia.
  repeat constructor;
    auto;
    try (apply page_size_of_order_pos; lia).

  -
    order_aligned_b.
    rewrite aligned_lower_buddy_eq; try lia; auto.
  -
    unfold buddy.
    rewrite Z.sub_simpl_r.
    apply Is_true_eq_true in H0.
    rewrite H0.
    rewrite Z.mul_add_distr_r, page_size_of_order_times_4096 by lia.
    auto.
  -
    unfold Inst.order_align.
    apply align_buddy_eq; try lia.
    order_aligned_b.
    auto.
Qed.

Lemma order_aligned_init: order_aligned_init_type.
Proof.
  unfold order_aligned_init_type.
  unfold Inst.order_aligned, order_aligned_b, order_align.
  intros.
  simpl.
  rewrite Z.mod_1_r, Z.sub_0_r, Z.eqb_refl.
  simpl.
  auto.
Qed.

Lemma page_size_of_order : page_size_of_order_type.
Proof.
  unfold page_size_of_order_type.
  unfold Inst.page_size_of_order, page_size_of_order.
  cbv.
  auto.
Qed.

Lemma buddy_idemp_impossible3:
  forall n sz,
  0 <= sz ->
  (n =? buddy n sz) = false.
Proof.
  intros.
  destruct (n =? buddy n sz) eqn: x; auto.
  rewrite Z.eqb_eq in x.
  apply eq_sym in x.
  rewrite buddy_idemp_impossible in x; auto.
  lia.
Qed.

Lemma find_buddy_xor : find_buddy_xor_type.
Proof.
  unfold find_buddy_xor_type, Inst.order_aligned,
      Inst.pfn_buddy.
  intros.
  order_aligned_b.
  assert (pw12: 4096 = 2 ^ 12) by (cbv; auto).
  repeat constructor; pow_sign.
  - apply Z.pow_lt_mono_r; try lia.
  - rewrite Z.lxor_nonneg.
    rewrite iff_to_and.
    constructor; intros; pow_sign.
  - rewrite pw12 in *.
    rewrite<- Z.pow_add_r by lia.
    apply lxor_lt_pow2; try apply Z.pow_lt_mono_r; pow_sign.
  - apply lxor_eq_buddy_times_page; auto.
  - apply Z.bits_inj_0.
    intros.
    rewrite pw12, Z.testbit_mod_pow2, Z.lxor_spec by lia.
    destruct (n <? 12) eqn: n_lt; auto.
    rewrite Z.ltb_lt in n_lt.
    rewrite (Z.mul_comm (2 ^ 12)).
    repeat rewrite Z.mul_pow2_bits_low by lia.
    auto.
  - order_aligned_b.
    rewrite lxor_eq_buddy_times_page by (auto; lia).
    apply order_aligned_buddy; auto.
  - rewrite lxor_eq_buddy_times_page by (auto; lia).
    rewrite<- Z.eqb_neq.
    rewrite buddy_idemp_impossible3; auto.
Qed.

Lemma page_size_of_order2: page_size_of_order2_type.
Proof.
  unfold page_size_of_order2_type, Inst.page_size_of_order.
  intros.
  rewrite (Z.mul_comm 4096).
  rewrite page_size_of_order_times_4096 by lia.
  repeat constructor; auto; pow_sign.
  apply Z.pow_lt_mono_r; lia.
Qed.

Ltac is_true_or_step :=
  match goal with H : Is_true (_ || _) |- _
    => apply orb_prop_elim in H
  | H: Is_true (_ <? _) |- _
    => apply Is_true_eq_true in H; rewrite Z.ltb_lt in H
  | H: Is_true (_ <=? _) |- _
    => apply Is_true_eq_true in H; rewrite Z.leb_le in H
  | H: Is_true (_ =? _) |- _
    => apply Is_true_eq_true in H; rewrite Z.eqb_eq in H
  | H: _ \/ _ |- _ => destruct H
  | _ => fail
  end.
Ltac is_true_or := repeat is_true_or_step.

Lemma forall_group_ok_to_inv:
  forall V pool start_i end_i,
  start_i = get_range_start_1_4 pool / 4096 ->
  (forall i : Z, start_i <= i < end_i -> page_group_ok i V pool)
  <->
  group_ok_inv start_i end_i 11 hyp_no_order (fun i => get_order_1_3 (V i)).
Proof.
  intros.
  unfold group_ok_inv.
  constructor.
  - intros.
    pose (X := H0 _ H1).
    unfold page_group_ok, Inst.order_align in X.
    destruct X as [X2 | X2]; try lia.
    destruct (Zle_lt_or_eq (order_align i ord) i); auto.
      apply order_align_le; auto; lia.
    pose (H_ord := X2 ord).
    apply (Decidable.not_and _) in H_ord;
      repeat apply Decidable.dec_and;
      try apply Z.lt_decidable;
      try apply Z.le_decidable; try lia.
  - intros.
    unfold page_group_ok, Inst.order_align.
    destruct (get_order_1_3 (V i) =? hyp_no_order) eqn: inval_cases.
    + rewrite Z.eqb_eq in inval_cases.
      auto.
    + rewrite Z.eqb_neq in inval_cases.
      constructor 2.
      intros.
      destruct (H0 _ i0 H1); try lia.
Qed.

Lemma group_ok_inv_eq_orders:
  forall start_i end_i o_max o_inval orders orders2,
  group_ok_inv start_i end_i o_max o_inval orders ->
  (forall i, orders2 i = orders i) ->
  group_ok_inv start_i end_i o_max o_inval orders2.
Proof.
  unfold group_ok_inv.
  intros.
  rewrite H0 in *.
  apply H; auto.
Qed.

Ltac split_if_anon :=
  match goal with |- context [if ?P then _ else _] =>
    destruct P
  end.

Lemma get_upd_order_1_3:
  forall {A : Type} (t : Z * Z * A) x, get_order_1_3 (upd_order_1_3 t x) = x.
Proof.
  intros.
  unfold get_order_1_3, upd_order_1_3.
  destruct t.
  destruct p.
  auto.
Qed.

Lemma get_fun_upd:
  forall {A B : Type} (f : A -> B) g x y i,
  f (fun_upd Z.eqb g x y i) =
  if x =? i
  then f y
  else f (g i).
Proof.
  intros.
  unfold fun_upd.
  split_if_anon; auto.
Qed.

Ltac conjI :=
  match goal with |- _ /\ _ => constructor end.
Ltac conjunctsI := repeat conjI.

Ltac lia2 :=
  try lia;
  try (apply Z.div_le_lower_bound; lia);
  try (apply Z.div_lt_upper_bound; lia).

Lemma order_align_inv_loop : order_align_inv_loop_type.
Proof.
  unfold order_align_inv_loop_type, Inst.order_align,
    Inst.order_aligned.
  intros until p.
  rewrite forall_group_ok_to_inv; try reflexivity.
  rewrite forall_group_ok_to_inv; try reflexivity.
  pose (start_i := get_range_start_1_4 pool / 4096).
  fold start_i.
  pose (end_i := get_range_end_2_4 pool / 4096).
  fold end_i.
  intros.
  order_aligned_b.
  match goal with |- context [pfn_buddy ?pgx _] =>
    pose (pg := pgx) end.
  match goal with m: group_ok_inv _ _ _ _ _ |- _ =>
    rename m into g_ok end.
  unfold hyp_no_order in *.
  apply (group_ok_inv_split pg) in g_ok;
    (try unfold pg in *); try lia2; auto.
  eapply group_ok_inv_eq_orders.
  apply g_ok.
  clear g_ok.
  intros.
  unfold fun_upd, Defs.fun_upd, Inst.pfn_buddy.
  fold pg.
  repeat split_if_anon; repeat rewrite get_upd_order_1_3; auto.
Qed.

Lemma page_group_ok_easy : page_group_ok_easy_type.
Proof.
  unfold page_group_ok_easy_type, Inst.order_align.
  intros until V.
  rewrite forall_group_ok_to_inv; try reflexivity.
  intros.
  conjunctsI; auto.
  apply group_ok_inv_0_order.
  auto.
Qed.

Lemma attach_inc_loop : attach_inc_loop_type.
  unfold attach_inc_loop_type, Inst.order_align,
    Inst.order_aligned, Inst.pfn_buddy.
  intros until order.
  rewrite forall_group_ok_to_inv; try reflexivity.
  rewrite forall_group_ok_to_inv; try reflexivity.
  intros.
  order_aligned_b.
  unfold hyp_no_order in *.
  match goal with |- context [buddy ?pgx _] =>
    pose (pg := pgx) end.
  fold pg.
  match goal with g_okx: group_ok_inv _ _ _ _ _ |- _ =>
    pose (g_ok := g_okx); fold pg in g_ok end.
  rewrite buddy_lt_eq in * by lia.
  destruct (order_aligned_b pg (order + 1)) eqn: is_al.
    apply Is_true_eq_left in is_al.
    order_aligned_b.
    apply (group_ok_inv_join pg) in g_ok;
      repeat rewrite (get_fun_upd get_order_1_3);
      repeat rewrite get_upd_order_1_3;
      repeat rewrite Z.eqb_refl;
      auto; try lia2.
      eapply group_ok_inv_eq_orders.
        apply g_ok.
      clear g_ok.
      intros.
      unfold Defs.fun_upd, fun_upd.
      rewrite Z.eqb_refl.
      split_if x; repeat rewrite get_upd_order_1_3; auto.
      split_if y; repeat rewrite get_upd_order_1_3; auto.
    split_if x; auto.
  pose (buddy_le := is_al).
  rewrite<- buddy_lt_eq in buddy_le by lia.
  rewrite Z.ltb_ge in buddy_le.
  match goal with b: get_order_1_3 (V (buddy _ _)) =_ |- _ =>
    pose (buddy_order := b) end.
  apply (group_ok_inv_join (buddy pg order)) in g_ok;
    unfold pg in *;
    repeat rewrite (get_fun_upd get_order_1_3);
    repeat rewrite buddy_idemp_impossible3;
    repeat rewrite Z.eqb_refl;
    repeat rewrite get_upd_order_1_3;
    repeat rewrite buddy_order;
    auto; try lia.
      eapply group_ok_inv_eq_orders.
        apply g_ok.
      clear g_ok.
      unfold fun_upd, Defs.fun_upd.
      intros.
      rewrite buddy_idemp_impossible3 by lia.
      rewrite H4.
      rewrite buddy_involution_gt_case; auto.
      split_if x; repeat rewrite get_upd_order_1_3; try lia.
      split_if y; repeat rewrite get_upd_order_1_3; try lia.
      rewrite Z.eqb_eq in y.
      rewrite y in *.
      auto.
    apply buddy_higher_aligned; auto.
  rewrite buddy_involution_gt_case; auto.
  rewrite Z.eqb_refl; auto.
Qed.

End Proofs.

Module InstOK: CN_Lemmas.Gen_Spec.Lemma_Spec(Inst).

  Module D := CN_Lemmas.Gen_Spec.Defs (Inst).

  Include Proofs.

End InstOK.

