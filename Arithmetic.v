(** Real arithmetic. *)

Require Import MiscLemmas.
Require Import QArith QOrderedType.
Require Export Field.
Require Import Cut.

Local Open Scope Q_scope.

(** Addition. *)
Definition Rplus : R -> R -> R.
Admitted.

(** Multiplication. *)
Definition Rmult : R -> R -> R.
Admitted.

(** Opposite value, we do this one by hand as an illustration.
    We should really define it as an extension of [Qopp]. *)
Definition Ropp (x : R) : R.
Proof.
  refine {| lower := (fun q => upper x (-q)); upper := (fun r => lower x (-r)) |}.
  - intros ? ? H. rewrite H; tauto.
  - intros ? ? H. rewrite H; tauto.
  - destruct (upper_bound x) as [r H].
    exists (- r).
    rewrite (Qopp_involutive r); assumption.
  - destruct (lower_bound x) as [q H].
    exists (- q).
    rewrite (Qopp_involutive q); assumption.
  - intros q r H G.
    apply (upper_upper _ (- r) _); [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (upper_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_r; assumption.
    rewrite Qopp_involutive; assumption.
  - intros q r H G.
    apply (lower_lower _ _ (- q)) ; [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (lower_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_l; assumption.
    rewrite Qopp_involutive; assumption.
  - intros q.
    assert (H := disjoint x (- q)).
    tauto.
  - intros q r H.
    destruct (located x (-r) (-q)).
    + apply Qopp_lt_compat; rewrite 2 Qopp_involutive; assumption.
    + right; assumption.
    + left; assumption.
Defined.

Definition Rminus x y := Rplus x (Ropp y).

(** Notation for the ring structure. *)

Infix "+" := Rplus : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "-" := Rminus : R_scope.
Infix "*" := Rmult : R_scope.

(** The arithmetical operations are proper with respect to equality. *)

Instance Rplus_comp : Proper (Req ==> Req ==> Req) Rplus.
Admitted.

Instance Rmult_comp : Proper (Req ==> Req ==> Req) Rmult.
Admitted.

Instance Ropp_comp : Proper (Req ==> Req) Ropp.
Proof.
  intros x y [H G].
  split; intro q; simpl.
  - admit.
  - apply H.
Qed.

Local Open Scope R_scope.


(** Properties of addition. *)

Lemma Rplus_assoc (x y z : R) : (x + y) + z == x + (y + z).
Admitted.

Lemma Rplus_comm (x y : R) : x + y == y + x.
Admitted.

Lemma Rplus_0_l (x : R) : 0 + x == x.
Admitted.

Lemma Rplus_0_r (x : R) : x + 0 == x.
Admitted.

(** Properties of multiplication. *)

Lemma Rmult_assoc (x y z : R) : (x * y) * z == x * (y * z).
Admitted.

Lemma Rmult_comm (x y : R) : x * y == y * x.
Admitted.

Lemma Rmult_1_l (x : R) : 1 * x == x.
Admitted.

Lemma Rmult_1_r (x : R) : x * 1 == x.
Admitted.

(** Properties of opposite. *)

Lemma Ropp_involutive (x : R) : - (- x) == x.
Admitted.

Lemma Rpluss_opp_r (x : R) : x + (- x) == 0.
Admitted.

Lemma Rplus_opp_l (x : R) : (- x) + x == 0.
Admitted.

(* Distributivity *)

Lemma Qmult_plus_distr_r (x y z : R) : x * (y + z) == (x * y) + (x * z).
Admitted.

Lemma Qmult_plus_distr_l (x y z : R) : (x + y) * z == (x * z) + (y * z).
Admitted.

