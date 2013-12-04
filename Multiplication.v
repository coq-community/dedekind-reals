(** The multiplicative structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut Additive.

Local Open Scope Q_scope.

(** Multiplication. *)
Definition Rmult : R -> R -> R.
Proof.
  admit.
Defined.

Infix "*" := Rmult : R_scope.

Instance Rmult_comp : Proper (Req ==> Req ==> Req) Rmult.
Admitted.

Local Open Scope R_scope.

(** Properties of multiplication. *)

Lemma Rmult_assoc (x y z : R) : (x * y) * z == x * (y * z).
Admitted.

Lemma Rmult_comm (x y : R) : x * y == y * x.
Admitted.

Lemma Rmult_1_l (x : R) : 1 * x == x.
Admitted.

Lemma Rmult_1_r (x : R) : x * 1 == x.
Admitted.

(* Distributivity *)

Lemma Qmult_plus_distr_r (x y z : R) : x * (y + z) == (x * y) + (x * z).
Admitted.

Lemma Qmult_plus_distr_l (x y z : R) : (x + y) * z == (x * z) + (y * z).
Admitted.

(* Inverse. *)

Theorem R_field : forall x : R, x <> 0 -> { y | x * y == 1 }.
Proof.
  admit.
Qed.
