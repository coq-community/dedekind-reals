(** When doing classical analysis, discontinuous real functions are often
    defined by testing a comparison, like
    f x := if 0 < x then 1 else 0.
    
    This requires the following disjunction in sort Type,
    { x < y } + { ~(x < y) }.

    We prove here that it implies the limited principle of omniscience,
    so it is not constructive. The proof assigns a rational sequence
    to each boolean sequence un, as
    vn n := if un n then 2^{-n} else 0.
    The series vn is convergent, because bounded by the convergent
    series 2^{-n}. *)

Require Import Logic.ConstructiveEpsilon.
Require Import QArith.
Require Import Qabs.
Require Import Qpower.
Require Import Cut.
Require Import Cauchy.
Require Import MiscLemmas.

Local Open Scope R_scope.

(* The limited principle of omniscience *)
Definition LPO : Set
  := forall (un : nat -> bool),
    { exists n : nat, un n = true } + { forall n:nat, un n = false }.

(* The LPO actually gives n in sort Type *)
Lemma LPO_epsilon : LPO -> forall (un : nat -> bool),
    { n : nat | un n = true } + { forall n:nat, un n = false }.
Proof.
  intros. destruct (H un).
  - apply constructive_indefinite_ground_description_nat in e.
    destruct e. left. exists x. exact e.
    intros. destruct (un n). left. reflexivity.
    right. discriminate.
  - right. exact e.
Qed.

(* The LPO lifts to decidable propositions *)
Lemma LPO_dec : forall (P : nat -> Prop),
    (forall n:nat, { P n } + { ~P n })
    -> LPO
    -> { n : nat | P n } + { forall n:nat, ~P n }.
Proof.
  intros. destruct (LPO_epsilon H0 (fun n => if H n then true else false)).
  - destruct s. left. exists x. destruct (H x). exact p. discriminate.
  - right. intros n abs. specialize (e n). destruct (H n).
    discriminate. contradiction.
Qed.

Lemma DecOrderImpliesLPO : (forall x:R, { 0 < x } + { ~(0 < x) }) -> LPO.
Proof.
  intros decOrder un. 
  pose (fun n:nat => if un n then (/2)^(Z.of_nat n) else 0%Q) as vn.
  assert (CauchyQ (sum_f_Q0 vn)).
  { apply (Cauchy_series_maj _ (fun n:nat => (/2)^(Z.of_nat n))).
    intro n. unfold vn. destruct (un n). rewrite Qabs_pos.
    apply Qle_refl. apply Qpower_pos. discriminate.
    rewrite Qabs_pos. apply Qpower_pos. discriminate. apply Qle_refl.
    apply (Un_cv_cauchy _ 2). exact GeoHalfSeries. }
  destruct (decOrder (CauchyQ_R (sum_f_Q0 vn) H)) as [H0|H0].
  - left. destruct H0 as [q [qPos H0]].
    destruct H0 as [r [n [rPos H0]]].
    specialize (H0 n (le_refl _)). simpl in qPos.
    apply (Qlt_trans 0 (q+r)) in H0. apply Find_positive_in_sum in H0.
    destruct H0. exists x. unfold vn in H0.
    destruct (un x) eqn:des. reflexivity.
    exfalso. exact (Qlt_irrefl 0 H0).
    intros. unfold vn. destruct (un k). apply Qpower_pos. discriminate.
    discriminate. rewrite <- Qplus_0_r. apply Qplus_lt_le_compat.
    exact qPos. apply Qlt_le_weak. exact rPos. 
  - right. intro n. apply Rnot_lt_le in H0.
    unfold Rle, CauchyQ_R in H0; simpl in H0.
    destruct (un n) eqn:des. 2: reflexivity. exfalso.
    (* Above n, the sequence sum_f_Q0 v stays above 2^(-n) *)
    specialize (H0 ((/2)^(2 + Z.of_nat n))).
    apply (Qlt_not_le ((/2)^(2 + Z.of_nat n)) 0).
    2: apply Qpower_pos; discriminate.
    apply H0. exists ((/2)^(2+ Z.of_nat n)), n.
    split. apply Qpower_strictly_pos. reflexivity.
    intros.
    setoid_replace ((/ 2) ^ (2 + Z.of_nat n) + (/ 2) ^ (2 + Z.of_nat n))
      with ((/ 2) ^ (1 + Z.of_nat n)).
    apply (Qlt_le_trans _ ((/2) ^ Z.of_nat n)).
    do 2 rewrite Qinv_power.
    setoid_replace (/ 2 ^ (1 + Z.of_nat n)) with (/2 * / 2 ^ Z.of_nat n).
    rewrite <- (Qmult_lt_l _ _ (2 ^ Z.of_nat n)).
    rewrite Qmult_inv_r. field_simplify. reflexivity.
    apply Qpower_nonzero. intro abs. discriminate.
    apply Qpower_nonzero. intro abs. discriminate.
    apply Qpower_strictly_pos. reflexivity. 
    rewrite Qpower_plus. simpl. rewrite Qinv_mult_distr. reflexivity.
    intro abs. discriminate.
    apply (Qle_trans _ (vn n)).
    unfold vn. destruct (un n). apply Qle_refl. discriminate.
    apply (Qle_trans _ (sum_f_Q0 vn n)).
    apply pos_sum_le_last. intro k. unfold vn. destruct (un k).
    apply Qpower_pos. discriminate. apply Qle_refl. apply pos_sum_more.
    intro k. unfold vn. destruct (un k).
    apply Qpower_pos. discriminate. apply Qle_refl. exact H1.
    rewrite Qpower_plus. rewrite Qpower_plus. simpl. field.
    intro abs. discriminate. intro abs. discriminate.
Qed.
