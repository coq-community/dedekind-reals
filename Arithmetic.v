(** Real arithmetic. *)

Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut.
Require Import QMetric.
Require Import Lipschitz.

Local Open Scope Q_scope.

(** Addition. *)
Definition Rplus : R -> R -> R.
Proof.
  pose (p := (fun u : Q * Q => fst u + snd u)).
  assert (Lplus : locally_lipschitz p).
  - exists (fun _ _ => 1).
    unfold p.
    intros [a b] s [q r] [u v] _ _.
    unfold ProductQMetric, distance, QMetric.
    ring_simplify.


    


  - apply (extend2 p).
  intros a b a' b' q r q' r'.
  split.
  - admit.
  - admit.
Defined.
    
(** Multiplication. *)
Definition Rmult : R -> R -> R.
Admitted.

(** Opposite value. *)
Definition Ropp : R -> R.
Admitted.

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
Admitted.

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
