(** Various lemmas that seem to be missing from the standard library. *)

Require Import QArith Qminmax.

Local Open Scope Q_scope.

Definition Qpositive := {q : Q & q > 0}.

Definition Q_of_Qpositive (q : Qpositive) := projT1 q.

Coercion Q_of_Qpositive : Qpositive >-> Q.

Definition Qnonnegative := {q : Q & q >= 0}.

Definition Q_of_Qnonnegative (q : Qnonnegative) := projT1 q.

Coercion Q_of_Qnonnegative : Qnonnegative >-> Q.

Definition Qinterval (q r : Q) := { s : Q | q <= s /\ s <= r }.

Definition Q_of_Qinterval a b (s : Qinterval a b) := projT1 s.

Coercion Q_of_Qinterval : Qinterval >-> Q.

Lemma Qopp_lt_compat : forall (p q : Q), p < q <-> -q < -p.
Proof.
  intros (a,b) (c,d).
  unfold Qlt. simpl.
  rewrite !Z.mul_opp_l. omega.
Defined.

Lemma Qplus_lt_lt_compat : forall (p q r s : Q), p < q -> r < s -> p + r < q + s.
Proof.
  auto using Qlt_le_weak, Qplus_lt_le_compat.
Qed.

Lemma Qmult_lt_positive : forall (p q : Q), 0 < p -> 0 < q -> 0 < p * q.
Proof.
  intros p q pPos qPos.
  rewrite <- (Qmult_0_l q) at 1.
  apply Qmult_lt_compat_r; assumption.
Qed.

Lemma Qopp_lt_shift_l : forall (p q : Q), -p < q <-> -q < p.
Proof.
  intros p q; split; intro H.
  - rewrite <- (Qopp_involutive p).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
  - rewrite <- (Qopp_involutive q).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
Qed.

Lemma Qopp_lt_shift_r : forall (p q : Q), p < -q <-> q < -p.
Proof.
  intros p q; split; intro H.
  - rewrite <- (Qopp_involutive p).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
  - rewrite <- (Qopp_involutive q).
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive.
    assumption.
Qed.

Lemma Qlt_minus_1 : forall q : Q, q + (-1#1) < q.
Proof.
  intro q.
  rewrite <- (Qplus_0_r q) at 2.
  apply Qplus_lt_r.
  compute; reflexivity.
Qed.

Lemma Qlt_plus_1 : forall q : Q, q < q + (1#1).
Proof.
  intro q.
  rewrite <- (Qplus_0_r q) at 1.
  apply Qplus_lt_r.
  compute; reflexivity.
Qed.

Lemma Qpower_strictly_pos : forall p n, 0 < p -> 0 < p^n.
Admitted.
