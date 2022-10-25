(* Notionally target-independent definitions and proofs
   about alignment and buddy trees as a spec concept. *)

Require Import ZArith Bool.

Open Scope Z.

Definition order_align (ptr order : Z) : Z :=
  ptr - (ptr mod (2 ^ order)).

Definition order_aligned (ptr order : Z) : Prop :=
  Z.divide (2 ^ order) ptr.

Definition order_aligned_b (ptr order : Z) : bool :=
  Z.eqb (order_align ptr order) ptr.

Definition buddy (ptr order : Z) : Z :=
  if order_aligned_b ptr (order + 1)
  then ptr + (2 ^ order)
  else ptr - (2 ^ order).

  Ltac pow_sign :=
    try apply Z.pow_pos_nonneg;
    try apply Z.pow_nonzero;
    try apply Z.pow_nonneg; try omega.
  
    Lemma order_aligned_b_true1:
    forall p order,
    Is_true (order_aligned_b p order) ->
    0 <= order ->
    order_aligned p order.
  Proof.
    unfold order_aligned_b, order_align, order_aligned.
    intros.
    apply Is_true_eq_true in H.
    rewrite Z.eqb_eq in *.
    rewrite<- Z.mod_divide by pow_sign.
    omega.
  Qed.
  
  Lemma order_aligned_b_true2:
    forall p order, 0 <= order ->
    order_aligned p order ->
    Is_true (order_aligned_b p order).
  Proof.
    unfold order_aligned_b, order_align, order_aligned.
    intros.
    apply Is_true_eq_left.
    rewrite Z.eqb_eq in *.
    rewrite<- Z.mod_divide in * by pow_sign.
    omega.
  Qed.
  
  Lemma order_aligned_sz_mono:
    forall p order1 order2,
    order_aligned p order1 ->
    0 <= order2 ->
    order2 <= order1 ->
    order_aligned p order2.
  Proof.
    unfold order_aligned.
    intros.
    apply Z.divide_trans with (m := 2 ^ order1); auto.
    unfold Z.divide.
    exists (2 ^ (order1 - order2)).
    rewrite<- Zpower_exp by omega.
    rewrite Z.sub_simpl_r.
    auto.
  Qed.
  
  Lemma div_power_impl_le:
    forall a i j,
    (a ^ i | a ^ j) ->
    1 < a ->
    0 <= i ->
    0 <= j ->
    i <= j.
  Proof.
    intros.
    destruct (i <? j) eqn: lt.
    -
      apply Z.ltb_lt in lt.
      omega.
    -
      apply Z.ltb_ge in lt.
      apply (Z.divide_pos_le _) in H; try apply Z.pow_pos_nonneg; try omega.
      apply Z.le_antisymm in H.
      apply (Z.pow_inj_r _ _ _) in H; try omega.
      apply Z.pow_le_mono_r_iff; omega.
  Qed.
  
  Lemma order_aligned_two_power:
    forall order1 order2,
    0 <= order1 ->
    0 <= order2 ->
    order_aligned_b (2 ^ order1) order2 = (order2 <=? order1).
  Proof.
    intros.
    destruct (order2 <=? order1) eqn: ineq.
    -
      apply Is_true_eq_true.
      apply order_aligned_b_true2; auto.
      apply Z.leb_le in ineq.
      apply order_aligned_sz_mono with (order1 := order1); try omega.
      unfold order_aligned.
      apply Z.divide_refl.
    -
      destruct (order_aligned_b (2 ^ order1) order2) eqn: ord; auto.
      apply Is_true_eq_left in ord.
      apply order_aligned_b_true1 in ord; try omega.
      unfold order_aligned in ord.
      apply Z.leb_gt in ineq.
      apply div_power_impl_le in ord; try omega.
  Qed.
  
  Lemma buddy_lt_eq:
  forall p order, 0 <= order ->
  p <? buddy p order = order_aligned_b p (order + 1).
Proof.
  intros.
  apply (Z.pow_pos_nonneg 2 order) in H; try omega.
  unfold buddy.
  destruct (order_aligned_b p (order + 1));
    rewrite Z.ltb_lt || rewrite Z.ltb_ge; omega.
Qed.

Lemma buddy_aligned_imp_le:
  forall p order,
  order_aligned p (order + 1) ->
  0 <= order ->
  p <= buddy p order.
Proof.
  intros.
  apply order_aligned_b_true2 in H; try omega.
  apply Is_true_eq_true in H.
  apply (Z.pow_pos_nonneg 2 order) in H0; try omega.
  unfold buddy.
  rewrite H.
  omega.
Qed.

Lemma buddy_higher_aligned:
  forall i order,
  0 <= order ->
  order_aligned i order ->
  order_aligned_b i (order + 1) = false ->
  order_aligned (buddy i order) (order + 1).
Proof.
  unfold buddy, order_aligned_b.
  intros.
  rewrite H1.
  unfold order_aligned in *.
  unfold Z.divide in H0.
  destruct H0.
  rewrite H0 in *.
  unfold order_align in H1.
  rewrite Z.pow_add_r, Z.pow_1_r in * by omega.
  rewrite Z.mul_comm in H1.
  rewrite Zmult_mod_distr_l in H1.
  destruct (Z.even x) eqn: even.
  - 
    rewrite Zmod_even, even, Z.mul_0_r, Z.sub_0_r in *.
    rewrite Z.eqb_refl in *.
    discriminate.
  -
    rewrite (Z.div_mod x 2) by omega.
    rewrite Zmod_even, even, Z.mul_add_distr_r, Z.mul_1_l.
    rewrite Z.add_simpl_r.
    rewrite Z.mul_comm.
    apply Z.mul_divide_mono_r.
    apply Z.divide_factor_l.
Qed.

Lemma aligned_lower_buddy_eq:
  forall i order,
  1 <= order ->
  order_aligned i order ->
  order_aligned_b (buddy i (order - 1)) order = false.
Proof.
  intros.
  unfold buddy.
  rewrite Z.sub_simpl_r.
  pose (H0_b := H0).
  apply order_aligned_b_true2 in H0_b; try omega.
  apply Is_true_eq_true in H0_b.
  rewrite H0_b.
  match goal with |- ?b = _ => destruct b eqn: bv end; auto.
  apply Is_true_eq_left in bv.
  apply order_aligned_b_true1 in bv; try omega.
  unfold order_aligned in *.
  destruct H0.
  rewrite H0 in *.
  apply (Z.divide_add_cancel_r _) in bv; try apply Z.divide_factor_r.
  apply div_power_impl_le in bv; try omega.
Qed.

Lemma align_buddy_eq:
  forall i order order2,
  1 <= order ->
  order_aligned i order ->
  order2 = order - 1 ->
  order_align (buddy i order2) order = i.
Proof.
  intros.
  unfold order_align, buddy.
  rewrite H1.
  rewrite Z.sub_simpl_r.
  pose (H0_b := H0).
  apply order_aligned_b_true2 in H0_b; try omega.
  apply Is_true_eq_true in H0_b.
  rewrite H0_b.
  unfold order_aligned in *.
  rewrite<- Z.add_mod_idemp_l; try apply Z.pow_nonzero; try omega.
  rewrite<- Z.mod_divide in H0; try apply Z.pow_nonzero; try omega.
  rewrite H0.
  simpl.
  rewrite Z.mod_small; try omega.
  constructor.
  apply Z.pow_nonneg; omega.
  apply Z.pow_lt_mono_r; try omega.
Qed.

Lemma order_aligned_imp_testbit_false:
  forall x i j,
  order_aligned x i ->
  j < i ->
  Z.testbit x j = false.
Proof.
  unfold order_aligned, Z.divide.
  intros.
  destruct H.
  rewrite H.
  apply Z.mul_pow2_bits_low.
  omega.
Qed.

Lemma order_aligned_from_testbit:
  forall x i,
  (forall j, j < i -> Z.testbit x j = false) ->
  0 <= i ->
  order_aligned x i.
Proof.
  unfold order_aligned.
  intros.
  rewrite<- Z.mod_divide by pow_sign.
  apply Z.bits_inj_0.
  intros.
  rewrite Z.testbit_mod_pow2 by omega.
  destruct (n <? i) eqn: n_lt; auto.
  rewrite Z.ltb_lt in n_lt.
  rewrite H; auto.
Qed.

Lemma order_align_idemp:
  forall n order,
  order_aligned n order ->
  0 <= order ->
  order_align n order = n.
Proof.
  intros.
  apply order_aligned_b_true2 in H; auto.
  unfold order_aligned_b in H.
  apply Is_true_eq_true in H.
  apply Z.eqb_eq in H.
  auto.
Qed.

Lemma order_aligned_order_align:
  forall i sz,
  0 <= sz ->
  order_aligned (order_align i sz) sz.
Proof.
  intros.
  unfold order_align, order_aligned.
  rewrite<- Z.mod_divide by pow_sign.
  rewrite Zminus_mod_idemp_r.
  rewrite Z.sub_diag.
  rewrite Z.mod_0_l by pow_sign.
  auto.
Qed.

Lemma order_align_eq_div_mult:
  forall i sz,
  0 <= sz ->
  order_align i sz = (i / 2 ^ sz) * 2 ^ sz.
Proof.
  intros.
  unfold order_align.
  rewrite Zmod_eq_full by pow_sign.
  omega.
Qed.

Lemma order_align_compose:
  forall i order1 order2,
  0 <= order1 <= order2 ->
  order_align (order_align i order1) order2 =
  order_align i order2.
Proof.
  intros.
  repeat rewrite order_align_eq_div_mult by omega.
  pose (x := Z.pow_add_r 2 order1 (order2 - order1)).
  rewrite Zplus_minus in x.
  repeat rewrite x by omega.
  rewrite<- Z.div_div by pow_sign.
  rewrite Z.div_mul by pow_sign.
  rewrite Z.div_div by pow_sign.
  auto.
Qed.

Lemma order_align_le:
  forall i sz,
  0 <= sz ->
  order_align i sz <= i.
Proof.
  unfold order_align.
  intros.
  destruct (Z.mod_pos_bound i (2 ^ sz)).
    apply Z.pow_pos_nonneg; omega.
  omega.
Qed.

Lemma align_to_page_or_buddy1:
  forall i order pg,
  order_align i (order + 1) = pg ->
  order_aligned i order ->
  0 <= order ->
  i = pg \/ i = buddy pg order.
Proof.
  unfold order_aligned.
  intros.
  unfold buddy.
  pose (pg_al := order_aligned_b_true2 pg (order + 1)).
  apply Is_true_eq_true in pg_al;
    try (rewrite<- H; apply order_aligned_order_align);
    try omega.
  rewrite pg_al.
  rewrite order_align_eq_div_mult in H by omega.
  rewrite Z.pow_add_r in H by omega.
  unfold Z.divide in H0.
  destruct H0.
  rewrite H0 in H.
  rewrite<- Z.div_div in H by pow_sign.
  rewrite Z.div_mul in H by pow_sign.
  rewrite Z.pow_1_r in H.
  destruct (Z.Even_or_Odd x).
    unfold Z.Even in H2.
    destruct H2.
    rewrite Z.mul_comm in H2.
    rewrite H2 in *.
    rewrite Z.div_mul in H by omega.
    rewrite<- H.
    rewrite H0.
    rewrite (Z.mul_comm (2 ^ _) 2).
    rewrite (Z.mul_assoc).
    auto.
  unfold Z.Odd in H2.
  destruct H2.
  rewrite Z.mul_comm in H2.
  rewrite H2 in *.
  rewrite Z.div_add_l in H by omega.
  constructor 2.
  assert (1 / 2 = 0) by (cbv; auto).
  rewrite H3 in *.
  rewrite Z.add_0_r in *.
  rewrite<- H.
  rewrite H0.
  rewrite Z.mul_add_distr_r.
  rewrite Z.mul_1_l.
  rewrite (Z.mul_comm (2 ^ _) 2).
  rewrite Z.mul_assoc.
  omega.
Qed.

Lemma align_to_page_or_buddy:
  forall i order pg,
  order_align i (order + 1) = pg ->
  0 <= order ->
  order_align i order = pg \/ order_align i order = buddy pg order.
Proof.
  intros.
  pose (align_to_page_or_buddy1 (order_align i order) order pg).
  destruct o; try omega.
    rewrite order_align_compose by omega.
    auto.
  apply order_aligned_order_align.
  omega.
Qed.

Lemma order_aligned_plus:
  forall x y sz,
  order_aligned x sz ->
  order_aligned y sz ->
  order_aligned (x + y) sz.
Proof.
  unfold order_aligned.
  intros.
  auto using Z.divide_add_r.
Qed.

Lemma order_aligned_power:
  forall sz,
  order_aligned (2 ^ sz) sz.
Proof.
  unfold order_aligned.
  intros.
  apply Z.divide_refl.
Qed.

Lemma order_aligned_buddy:
  forall i sz,
  order_aligned i sz ->
  0 <= sz ->
  order_aligned (buddy i sz) sz.
Proof.
  unfold buddy.
  intros.
  destruct (order_aligned_b i (sz + 1)).
    apply order_aligned_plus; auto.
    apply order_aligned_power.
  rewrite<- Z.add_opp_r.
  apply order_aligned_plus; auto.
  unfold order_aligned.
  rewrite Z.divide_opp_r.
  apply Z.divide_refl.
Qed.

Lemma buddy_idemp_impossible:
  forall n sz,
  0 <= sz ->
  buddy n sz = n <-> False.
Proof.
  intros.
  unfold buddy.
  apply (Z.pow_pos_nonneg 2 sz) in H; try omega.
  destruct (order_aligned_b n (sz + 1)).
    constructor; intros; omega.
  constructor; intros; omega.
Qed.

Lemma buddy_involution_gt_case:
  forall n sz,
  0 <= sz ->
  order_aligned n sz ->
  order_aligned_b n (sz + 1) = false ->
  buddy (buddy n sz) sz = n.
Proof.
  intros.
  unfold buddy.
  rewrite H1.
  pose (buddy_higher_aligned n sz H H0 H1).
  unfold buddy in o.
  rewrite H1 in o.
  apply order_aligned_b_true2 in o; try omega.
  apply Is_true_eq_true in o.
  rewrite o.
  omega.
Qed.

