(* Definitions and lemmas about the buddy allocator example
   invariants, independent of the CN output. *)

Require Import ZArith Bool.
Require Import CN_Lemmas.Buddy_Aligned.

Open Scope Z.

(* n.b. this is used as a physical pointer offset *)
Definition page_size_of_order (order : Z) : Z :=
  2 ^ (order + 12).

Definition page_aligned (ptr order : Z) : Prop :=
  Z.divide (page_size_of_order order) ptr.

Definition no_order : Z := 4294967295.

Definition pages_no_overlap {A B : Type}
      (vmemmap : Z -> (Z * Z * A * B))
      (start_i end_i : Z) :=
    start_i <= end_i /\
    forall i j,
    start_i <= i /\ i < end_i ->
    let '(ord_i, _, _, _) := vmemmap i in
    ord_i <> no_order ->
    order_align j ord_i = i ->
    i <> j -> 
    start_i <= j /\ j < end_i /\
    let '(ord_j, _, _, _) := vmemmap j in
    ord_j = no_order.

Lemma page_size_of_order_mono:
  forall order1 order2,
  order1 <= order2 ->
  0 <= order1 ->
  page_size_of_order order1 <= page_size_of_order order2.
Proof.
  intros.
  unfold page_size_of_order.
  apply Z.pow_le_mono_r_iff; omega.
Qed.

Lemma page_size_of_order_times_4096:
  forall order, 0 <= order -> 2 ^ order * 4096 = page_size_of_order order.
Proof.
  unfold page_size_of_order.
  intros.
  rewrite Z.pow_add_r by omega.
  cbv; auto.
Qed.

Lemma page_aligned_times_4096:
  forall i order, 0 <= order ->
  order_aligned i order ->
  page_aligned (i * 4096) order.
Proof.
  unfold page_aligned, order_aligned.
  intros.
  rewrite<- page_size_of_order_times_4096 by auto.
  apply Z.mul_divide_cancel_r; auto.
  omega.
Qed.

Lemma pfn_add_sub_eq_pfn_times_4096:
  forall i order, 0 <= order ->
  i * 4096 + page_size_of_order order = buddy i order * 4096 \/
  i * 4096 - page_size_of_order order = buddy i order * 4096.
Proof.
  intros.
  unfold buddy.
  destruct (order_aligned_b i (order + 1)) eqn: al.
  rewrite Z.mul_add_distr_r, page_size_of_order_times_4096; auto.
  rewrite Z.mul_sub_distr_r, page_size_of_order_times_4096; auto.
Qed.

Lemma page_size_of_order_inc:
  forall order,
  0 <= order ->
  page_size_of_order (order + 1) = 2 * page_size_of_order order.
Proof.
  intros.
  unfold page_size_of_order.
  repeat rewrite Z.pow_add_r by omega.
  rewrite Z.pow_1_r.
  ring.
Qed.

Lemma page_size_of_order_inc2:
  forall order,
  0 <= order ->
  page_size_of_order (order + 1) = page_size_of_order order * 2.
Proof.
  intros.
  rewrite page_size_of_order_inc by omega.
  ring.
Qed.

Lemma page_size_of_order_pos:
  forall order, 0 <= order ->
  0 < page_size_of_order order.
Proof.
  intros.
  unfold page_size_of_order.
  apply Z.pow_pos_nonneg; omega.
Qed.

Ltac split_if nm :=
  match goal with |- context [if ?P then _ else _] =>
    destruct P eqn: nm
  end.

Lemma lxor_eq_if:
  forall i order,
  0 <= order ->
  Z.lxor i (2 ^ order) = (if Z.testbit i order
    then i - 2 ^ order
    else i + 2 ^ order).
Proof.
  intros.
  split_if testb.
  - rewrite<- Z.add_cancel_r with (p := 2 ^ order).
    rewrite Z.add_nocarry_lxor.
      rewrite Z.lxor_assoc, Z.lxor_nilpotent, Z.lxor_0_r.
      omega.
      apply Z.bits_inj_0.
      intros.
      rewrite Z.land_spec, Z.lxor_spec, Z.pow2_bits_eqb by omega.
      destruct (order =? n) eqn: x; try rewrite andb_false_r; auto.
      rewrite Z.eqb_eq in x.
      rewrite<- x.
      rewrite testb.
      auto.
  - rewrite<- Z.add_nocarry_lxor; auto.
    apply Z.bits_inj_0.
    intros.
    rewrite Z.land_spec, Z.pow2_bits_eqb by omega.
    destruct (order =? n) eqn: x; try rewrite andb_false_r; auto.
    rewrite Z.eqb_eq in x.
    rewrite<- x.
    rewrite testb.
    auto.
Qed.

Lemma lxor_eq_buddy:
  forall i order,
  0 <= order ->
  order_aligned i order ->
  Z.lxor i (2 ^ order) = buddy i order.
Proof.
  intros.
  unfold buddy.
  split_if al; rewrite lxor_eq_if by omega; split_if testb; auto.
  - apply Is_true_eq_left in al.
    apply order_aligned_b_true1 in al; try omega.
    rewrite order_aligned_imp_testbit_false with (i := order + 1)
      in testb; auto; try omega.
    discriminate testb.
  - apply eq_true_false_abs in al; try omega.
    apply Is_true_eq_true.
    apply order_aligned_b_true2; try omega.
    apply order_aligned_from_testbit; try omega.
    intros.
    destruct (Z.lt_ge_cases j order).
      apply order_aligned_imp_testbit_false with (i := order); auto.
    assert (j = order) by omega.
    rewrite H3.
    auto.
Qed.

Lemma lxor_eq_buddy_times_page:
  forall i order,
  0 <= order ->
  order_aligned i order ->
  Z.lxor (i * 4096) (4096 * 2 ^ order) / 4096 = buddy i order.
Proof.
  intros.
  assert (4096 = 2 ^ 12) by (cbv; auto).
  rewrite H1.
  rewrite<- Z.shiftl_mul_pow2 by omega.
  rewrite Z.mul_comm.
  rewrite<- Z.shiftl_mul_pow2 by omega.
  rewrite<- Z.shiftl_lxor.
  rewrite<- Z.shiftr_div_pow2 by omega.
  rewrite Z.shiftr_shiftl_l by omega.
  rewrite Z.sub_diag, Z.shiftl_0_r.
  apply lxor_eq_buddy; auto.
Qed.

Lemma lxor_lt_pow2:
  forall x y i,
  0 <= x -> 0 <= y ->
  x < 2 ^ i -> y < 2 ^ i ->
  0 < i ->
  Z.lxor x y < 2 ^ i.
Proof.
  intros.
  rewrite Z.le_lteq in H.
  rewrite or_comm in H.
  destruct H.
    rewrite<- H.
    auto.
  rewrite Z.le_lteq in H0.
  rewrite or_comm in H0.
  destruct H0.
    rewrite<- H0.
    rewrite Z.lxor_0_r.
    auto.
  assert (le_lx : 0 <= Z.lxor x y)
    by (rewrite Z.lxor_nonneg; omega).
  rewrite Z.le_lteq in le_lx.
  destruct le_lx; try omega.
  rewrite Z.log2_lt_pow2 by auto.
  eapply Z.le_lt_trans.
    apply Z.log2_lxor; try omega.
  apply Z.max_lub_lt_iff.
  rewrite Z.log2_lt_pow2 in * by omega.
  auto.
Qed.

Definition group_ok_inv start_n end_n o_max o_inval
    (orders : Z -> Z): Prop :=
  forall (i : Z) (ord : Z),
  start_n <= i /\ i < end_n ->
  0 < ord ->
  ord < o_max ->
  orders i <> o_inval ->
  order_align i ord = i \/
  order_align i ord < start_n \/
  orders (order_align i ord) < ord \/
  orders (order_align i ord) = o_inval.

Definition fun_upd {A B : Type} (eq : A -> A -> bool) (f : A -> B) x y z :=
  if eq x z then y else f z.

Lemma group_ok_inv_reduce:
  forall n order2 start_n end_n o_max o_inval orders,
  group_ok_inv start_n end_n o_max o_inval orders ->
  orders n <> o_inval ->
  (order2 < orders n \/ order2 = o_inval) ->
  o_max < o_inval ->
  group_ok_inv start_n end_n o_max o_inval (fun_upd Z.eqb orders n order2).
Proof.
  unfold group_ok_inv, fun_upd.
  intros.
  destruct (n =? i) eqn: eq_n_i.
    rewrite Z.eqb_eq in eq_n_i.
    rewrite eq_n_i in *.
    destruct (i =? order_align i ord) eqn: i_eq_align.
      rewrite Z.eqb_eq in i_eq_align.
      rewrite<- i_eq_align.
      auto.
    apply H; auto.
  destruct (n =? order_align i ord) eqn: eq_n_al.
    rewrite Z.eqb_eq in eq_n_al.
    rewrite eq_n_al in *.
    destruct (H i ord); auto.
    destruct H7; auto.
    destruct H7; try omega.
  apply H; auto.
Qed.


Lemma group_ok_inv_set:
  forall n order2 start_n end_n o_max o_inval orders,
  group_ok_inv start_n end_n o_max o_inval orders ->
  order_aligned n order2 ->
  ((* n is not not covered by a larger mapping *)
  forall order3, order2 < order3 ->
  order3 < o_max ->
  order_align n order3 = n \/
  order_align n order3 < start_n \/
  orders (order_align n order3) < order3 \/
  orders (order_align n order3) = o_inval
  ) ->
  ((* n is not covering a smaller val *)
  forall n2,
  start_n <= n2 < end_n ->
  order_align n2 order2 = n ->
  n < n2 ->
  orders n2 = o_inval
  ) ->
  o_max < o_inval ->
  group_ok_inv start_n end_n o_max o_inval (fun_upd Z.eqb orders n order2).
Proof.
  unfold group_ok_inv, fun_upd.
  intros.
  destruct (n =? i) eqn: eq_n_i.
    rewrite Z.eqb_eq in eq_n_i.
    rewrite eq_n_i in *.
    destruct (i =? order_align i ord) eqn: i_eq_align.
      rewrite Z.eqb_eq in i_eq_align.
      rewrite<- i_eq_align.
      auto.
    destruct (ord <=? order2) eqn: ord_le.
      rewrite Z.leb_le in ord_le.
      rewrite order_align_idemp; auto; try omega.
      eauto using order_aligned_sz_mono, Z.lt_le_incl.
    rewrite Z.leb_gt in ord_le.
    apply H1; omega.
  destruct (n =? order_align i ord) eqn: eq_n_al.
    rewrite Z.eqb_eq in eq_n_al.
    destruct (ord <=? order2) eqn: ord_le.
      rewrite Z.leb_le in ord_le.
      rewrite H2 in H7; try omega.
        rewrite<- (order_align_idemp n order2); auto; try omega.
        rewrite eq_n_al.
        rewrite order_align_compose; auto.
        omega.
      rewrite eq_n_al in *.
      rewrite Z.le_neq.
      rewrite Z.eqb_neq in eq_n_i.
      constructor; auto.
      apply order_align_le; omega.
    rewrite Z.leb_gt in ord_le.
    auto.
  apply H; auto.
Qed.

Lemma group_ok_inv_split:
  forall pg start_n end_n o_max o_inval orders,
  group_ok_inv start_n end_n o_max o_inval orders ->
  let order := orders pg in
  order_aligned pg order ->
  0 < order ->
  order < o_max ->
  o_max < o_inval ->
  start_n <= pg -> pg < end_n ->
  group_ok_inv start_n end_n o_max o_inval
    (fun_upd Z.eqb (fun_upd Z.eqb orders pg (order - 1))
      (buddy pg (order - 1)) (order - 1)).
Proof.
  intros.
  apply group_ok_inv_set; auto.
        apply group_ok_inv_reduce; auto; try omega.
      apply order_aligned_buddy; try omega.
      apply (order_aligned_sz_mono pg order); auto; omega.
    intros.
    rewrite<- (order_align_compose (buddy pg (order - 1)) order) by omega.
    rewrite align_buddy_eq by (auto; omega).
    unfold fun_upd.
    destruct (pg =? order_align pg order3) eqn: pg_eq_align; try omega.
    destruct (Z.lt_ge_cases (order_align pg order3) start_n); auto.
    destruct (H pg order3); try omega.
    rewrite H9 in *.
    rewrite Z.eqb_refl in *.
    discriminate pg_eq_align.
  intros.
  unfold fun_upd in *.
  destruct (pg =? n2) eqn: pg_eq_n2.
    rewrite Z.eqb_eq in pg_eq_n2.
    rewrite pg_eq_n2 in *.
    rewrite order_align_idemp in H7; try omega.
    apply order_aligned_sz_mono with (order1 := order); try omega.
    auto.
  pose (order_align_compose n2 (order - 1) order).
  rewrite H7 in e.
  rewrite align_buddy_eq in e by (auto; try omega).
  destruct (orders n2 =? o_inval) eqn: eq_cases.
    rewrite Z.eqb_eq in eq_cases; auto.
  rewrite Z.eqb_neq in eq_cases.
  destruct (H n2 order); auto; try omega.
    rewrite<- e in * by omega.
    rewrite Z.eqb_neq in pg_eq_n2.
    omega.
  rewrite<- e in * by omega.
  omega.
Qed.


Lemma group_ok_inv_0_order:
  forall start_n end_n o_max o_inval orders,
  (forall i, start_n <= i < end_n -> orders i = 0) ->
  group_ok_inv start_n end_n o_max o_inval orders.
Proof.
  unfold group_ok_inv.
  intros.
  destruct (Z.lt_ge_cases (order_align i ord) start_n).
    auto.
  rewrite H; auto.
  constructor; auto.
  apply Z.le_lt_trans with (m := i).
    apply order_align_le; omega.
  omega.
Qed.

Lemma order_aligned_triv_0:
  forall n, order_aligned n 0.
Proof.
  unfold order_aligned.
  intros.
  simpl.
  apply Z.divide_1_l.
Qed.

Lemma group_ok_inv_join:
  forall pg start_n end_n o_max o_inval orders,
  group_ok_inv start_n end_n o_max o_inval orders ->
  let order := orders pg in
  order_aligned pg (order + 1) ->
  orders (buddy pg order) = order ->
  order + 1 < o_max ->
  o_max < o_inval ->
  0 <= order ->
  start_n <= pg -> pg < end_n ->
  group_ok_inv start_n end_n o_max o_inval
    (fun_upd Z.eqb (fun_upd Z.eqb orders
            (buddy pg order) o_inval)
        pg (order + 1)).
Proof.
  intros.
  apply group_ok_inv_set; auto.
      apply group_ok_inv_reduce; auto.
      omega.
    intros.
    destruct (Z.lt_ge_cases order order3); try omega.
    unfold group_ok_inv in *.
    destruct (H pg order3); try omega.
    unfold fun_upd.
    split_if x; auto.
  intros.
  unfold fun_upd.
  split_if x; auto.
  destruct (orders n2 =? o_inval) eqn: is_inval.
    rewrite Z.eqb_eq in is_inval; auto.
  rewrite Z.eqb_neq in is_inval.  
  apply align_to_page_or_buddy in H8; try omega.
  destruct H8.
    rewrite Z.le_lteq in H4.
    destruct H4.
      destruct (H n2 order); try omega.
      rewrite H8 in *.
      omega.
    rewrite<- H4 in *.
    rewrite order_align_idemp in *
      by (try apply order_aligned_triv_0; omega).
    omega.
  rewrite Z.eqb_neq in x.
  rewrite Z.le_lteq in H4.
  destruct H4.
    destruct (H n2 order); try omega.
    rewrite H8 in *.
    destruct H10; try omega.
    apply (buddy_aligned_imp_le pg order) in H0; try omega.
  rewrite<- H4 in *.
  rewrite order_align_idemp in *
  by (try apply order_aligned_triv_0; omega).
  omega.
Qed.
