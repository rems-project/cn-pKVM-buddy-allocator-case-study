(* Instantiation of the CN-exported specification
   using results from the prior theories. *)

Require Import ZArith Bool.
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

Ltac omega_ineq :=
  match goal with
    | |- (_ <= _) => omega
    | |- (_ < _) => omega
    | _ => try fail
  end.

Ltac order_aligned_b1 :=
  match goal with H : Is_true (order_aligned_b _ _) |- _
    => apply order_aligned_b_true1 in H; omega_ineq
  | |- Is_true (order_aligned_b _ _)
    => apply order_aligned_b_true2; omega_ineq
  | _ => fail
  end.
Ltac order_aligned_b := repeat order_aligned_b1.

Lemma lemma_order_dec_inv: lemma_order_dec_inv_type.
Proof.
  unfold lemma_order_dec_inv_type, Inst.order_aligned, Inst.page_size_of_order.

  intros.
  constructor; order_aligned_b.
  -
    apply order_aligned_sz_mono with (order1 := order1); auto.
  -
    pose (p := page_size_of_order_mono order2 order1).
    apply le_triv in p; omega.
Qed.

Lemma lemma2: lemma2_type.
Proof.
  unfold lemma2_type, Inst.order_aligned, Inst.page_size_of_order,
      Inst.pfn_buddy, Inst.page_aligned.
  intros.
  order_aligned_b.
  rewrite buddy_lt_eq by omega.
  match goal with |- ?x /\ _ => assert x end.
    destruct (order_aligned_b p_i (order + 1)) eqn:al; auto using Is_true_eq_left.
    order_aligned_b.
    apply buddy_higher_aligned; auto; omega.
  constructor; auto.
  constructor.
    apply page_aligned_times_4096; try omega.
    order_aligned_b.
    auto.
  apply pfn_add_sub_eq_pfn_times_4096; try omega.
Qed.

Lemma lemma_extract: lemma_extract_type.
Proof.
  unfold lemma_extract_type, Inst.order_aligned,
      Inst.page_size_of_order, Inst.pfn_buddy, Inst.page_aligned.
  intros.
  constructor.
    apply Is_true_eq_true in H2.
    unfold buddy.
    rewrite H2.
    rewrite Z.mul_add_distr_r, page_size_of_order_times_4096; auto.
  order_aligned_b.
  constructor; apply page_aligned_times_4096; try omega.
    apply order_aligned_sz_mono with (order1 := order + 1);
      auto; omega.
  apply order_aligned_buddy; try omega.
  apply order_aligned_sz_mono with (order1 := order + 1);
    auto; omega.
Qed.

Lemma lemma_page_size_of_order_inc: lemma_page_size_of_order_inc_type.
Proof.
  unfold lemma_page_size_of_order_inc_type, Inst.page_size_of_order.
  intros.
  apply page_size_of_order_inc.
  omega.
Qed.

Lemma lemma4: lemma4_type.
Proof.
  unfold lemma4_type, Inst.order_aligned, Inst.pfn_buddy,
      Inst.page_size_of_order, Inst.order_align.
  intros.
  rewrite<- page_size_of_order_inc2, Z.sub_simpl_r by omega.
  repeat constructor;
    auto;
    try (apply page_size_of_order_pos; omega).

  -
    order_aligned_b.
    rewrite aligned_lower_buddy_eq; try omega; auto.
  -
    unfold buddy.
    rewrite Z.sub_simpl_r.
    apply Is_true_eq_true in H2.
    rewrite H2.
    rewrite Z.mul_add_distr_r, page_size_of_order_times_4096 by omega.
    auto.
  -
    unfold Inst.order_align.
    apply align_buddy_eq; try omega.
    order_aligned_b.
    auto.
Qed.

Lemma lemma_order_aligned_init: lemma_order_aligned_init_type.
Proof.
  unfold lemma_order_aligned_init_type.
  unfold Inst.order_aligned, order_aligned_b, order_align.
  intros.
  simpl.
  rewrite Z.mod_1_r, Z.sub_0_r, Z.eqb_refl.
  simpl.
  auto.
Qed.

Lemma lemma_page_size_of_order : lemma_page_size_of_order_type.
Proof.
  unfold lemma_page_size_of_order_type.
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
  omega.
Qed.

Lemma find_buddy_xor_lemma : find_buddy_xor_lemma_type.
Proof.
  unfold find_buddy_xor_lemma_type, Inst.order_aligned,
      Inst.pfn_buddy.
  intros.
  order_aligned_b.
  assert (pw12: 4096 = 2 ^ 12) by (cbv; auto).
  repeat constructor; pow_sign.
  - apply Z.pow_lt_mono_r; try omega.
  - rewrite Z.lxor_nonneg.
    rewrite iff_to_and.
    constructor; intros; pow_sign.
    apply Z.mul_nonneg_nonneg; pow_sign.
  - rewrite pw12 in *.
    rewrite<- Z.pow_add_r by omega.
    apply lxor_lt_pow2; try apply Z.pow_lt_mono_r; pow_sign.
    apply Z.mul_nonneg_nonneg; pow_sign.
  - apply lxor_eq_buddy_times_page; auto.
  - apply Z.bits_inj_0.
    intros.
    rewrite pw12, Z.testbit_mod_pow2, Z.lxor_spec by omega.
    destruct (n <? 12) eqn: n_lt; auto.
    rewrite Z.ltb_lt in n_lt.
    rewrite (Z.mul_comm (2 ^ 12)).
    repeat rewrite Z.mul_pow2_bits_low by omega.
    auto.
  - order_aligned_b.
    rewrite lxor_eq_buddy_times_page by (auto; omega).
    apply order_aligned_buddy; auto.
  - rewrite lxor_eq_buddy_times_page by (auto; omega).
    rewrite<- Z.eqb_neq.
    rewrite buddy_idemp_impossible3; auto.
Qed.

Lemma page_size_of_order_lemma: page_size_of_order_lemma_type.
Proof.
  unfold page_size_of_order_lemma_type, Inst.page_size_of_order.
  intros.
  rewrite (Z.mul_comm 4096).
  rewrite page_size_of_order_times_4096 by omega.
  repeat constructor; auto; pow_sign.
  apply Z.pow_lt_mono_r; omega.
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

Lemma CN_form_to_group_ok:
  forall orders orders2 start_i end_i o_inval o_max_dec,
  0 <= o_max_dec ->
  o_max_dec + 1 < o_inval ->
  (forall i ord, orders2 i ord = orders (order_align i ord)) ->
  (forall i : Z,
    start_i <= i < end_i ->
    orders i = o_inval \/
    (forall ord : Z,
      1 <= ord <= o_max_dec ->
      ~ (
        (((order_align i ord < i) /\
        (start_i <= order_align i ord)) /\
        (ord <= orders2 i ord)) /\
        (~ (orders2 i ord = o_inval)) )
    )) <->
  group_ok_inv start_i end_i (o_max_dec + 1) o_inval orders.
Proof.
  intros.
  unfold group_ok_inv.
  constructor.
  - intros.
    destruct (H2 i); try omega.
    clear H2.
    destruct (Zle_lt_or_eq (order_align i ord) i); auto.
      apply order_align_le; auto; omega.
    pose (H_ord := H7 ord).
    apply (Decidable.not_and _) in H_ord;
      repeat apply Decidable.dec_and;
      try apply Z.lt_decidable;
      try apply Z.le_decidable; try omega.
    clear H7.
    rewrite H1 in *.
    repeat (apply Z.lt_decidable || apply Z.le_decidable
      || apply Decidable.dec_and
      || match goal with Hx: ~ (_ /\ _) |- _
          => apply (Decidable.not_and _) in Hx
        | Ho: _ \/ _ |- _ => destruct Ho end);
    try omega.
  - intros.
    destruct (orders i =? o_inval) eqn: inval_cases.
      rewrite Z.eqb_eq in inval_cases; auto.
    rewrite Z.eqb_neq in inval_cases.
    constructor 2.
    intros.
    rewrite H1.
    destruct (H2 i ord); try omega.
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

Lemma get_upd_order_1_4:
  forall (t : Z * Z * Z * (Z * Z)) x, get_order_1_4 (upd_order_1_4 t x) = x.
Proof.
  intros.
  unfold get_order_1_4, upd_order_1_4.
  destruct t.
  destruct p.
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

Lemma lemma_order_align_inv_loop : lemma_order_align_inv_loop_type.
Proof.
  unfold lemma_order_align_inv_loop_type, Inst.order_align,
    Inst.order_aligned.
  intros until V.
  rewrite CN_form_to_group_ok; auto; try omega.
  rewrite CN_form_to_group_ok; auto; try omega.
  simpl.
  intros.
  conjunctsI; auto.
  order_aligned_b.
  match goal with |- context [pfn_buddy ?pgx _] =>
    pose (pg := pgx) end.
  match goal with m: group_ok_inv _ _ _ _ _ |- _ =>
    rename m into g_ok end.
  apply (group_ok_inv_split pg) in g_ok;
    (try unfold pg in *); try omega; auto.
  eapply group_ok_inv_eq_orders.
  apply g_ok.
  clear g_ok.
  intros.
  unfold fun_upd, Defs.fun_upd, Inst.pfn_buddy.
  fold pg.
  repeat split_if_anon; repeat rewrite get_upd_order_1_4; auto.
Qed.

Lemma lemma_page_group_ok_easy : lemma_page_group_ok_easy_type.
Proof.
  unfold lemma_page_group_ok_easy_type, Inst.order_align.
  intros until V.
  rewrite CN_form_to_group_ok; auto; try omega.
  intros.
  conjunctsI; auto.
  apply group_ok_inv_0_order.
  auto.
Qed.

Lemma lemma_attach_inc_loop : lemma_attach_inc_loop_type.
  unfold lemma_attach_inc_loop_type, Inst.order_align,
    Inst.order_aligned, Inst.pfn_buddy.
  intros until V.
  rewrite CN_form_to_group_ok; auto; try omega.
  rewrite CN_form_to_group_ok; auto; try omega.
  intros.
  conjunctsI; auto.
  order_aligned_b.
  match goal with |- context [buddy ?pgx _] =>
    pose (pg := pgx) end.
  fold pg.
  match goal with g_okx: group_ok_inv _ _ _ _ _ |- _ =>
    pose (g_ok := g_okx); fold pg in g_ok end.
  rewrite buddy_lt_eq in * by omega.
  destruct (order_aligned_b pg (order + 1)) eqn: is_al.
    apply Is_true_eq_left in is_al.
    order_aligned_b.
    apply (group_ok_inv_join pg) in g_ok;
      repeat rewrite (get_fun_upd get_order_1_4);
      repeat rewrite get_upd_order_1_4;
      repeat rewrite Z.eqb_refl;
      auto; try omega.
      eapply group_ok_inv_eq_orders.
        apply g_ok.
      clear g_ok.
      intros.
      unfold Defs.fun_upd, fun_upd.
      rewrite Z.eqb_refl.
      split_if x; repeat rewrite get_upd_order_1_4; auto.
      split_if y; repeat rewrite get_upd_order_1_4; auto.
    split_if x; auto.
  pose (buddy_le := is_al).
  rewrite<- buddy_lt_eq in buddy_le by omega.
  rewrite Z.ltb_ge in buddy_le.
  match goal with b: get_order_1_4 (V (buddy _ _)) =_ |- _ =>
    pose (buddy_order := b) end.
  apply (group_ok_inv_join (buddy pg order)) in g_ok;
    unfold pg in *;
    repeat rewrite (get_fun_upd get_order_1_4);
    repeat rewrite buddy_idemp_impossible3;
    repeat rewrite Z.eqb_refl;
    repeat rewrite get_upd_order_1_4;
    repeat rewrite buddy_order;
    auto; try omega.
      eapply group_ok_inv_eq_orders.
        apply g_ok.
      clear g_ok.
      unfold fun_upd, Defs.fun_upd.
      intros.
      rewrite buddy_idemp_impossible3 by omega.
      rewrite H9.
      rewrite buddy_involution_gt_case; auto.
      split_if x; repeat rewrite get_upd_order_1_4; try omega.
      split_if y; repeat rewrite get_upd_order_1_4; try omega.
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

