(** The multiplicative structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut Additive.

Local Open Scope Q_scope.

(** Multiplication. *)

Let mult_lower (x y : R) (q : Q) :=
  exists a b c d : Q, lower x a /\ upper x b /\ lower y c /\ upper y d /\
                      q < a * c /\ q < a * d /\ q < b * c /\ q < b * d.

Let mult_upper (x y : R) (q : Q) :=
  exists a b c d : Q, lower x a /\ upper x b /\ lower y c /\ upper y d /\
                      a * c < q /\ a * d < q /\ b * c < q /\ b * d < q.

Let mult_lower_proper (x y : R) : Proper (Qeq ==> iff) (mult_lower x y).
Proof.
  intros q r Eqr ; split ; intros [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Eqr ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Eqr ; assumption.
Qed.

Let mult_upper_proper (x y : R) : Proper (Qeq ==> iff) (mult_upper x y).
Proof.
  admit.
Qed.

Definition Rmult : R -> R -> R.
Proof.
  intros x y.
  refine {|
      lower := mult_lower x y ;
      upper := mult_upper x y
    |}.
  - apply mult_lower_proper.
  - apply mult_upper_proper.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Defined.

Infix "*" := Rmult : R_scope.

Instance Rmult_comp : Proper (Req ==> Req ==> Req) Rmult.
Proof.
  intros x y Exy u v Euv.
  split ; intro q ; split ; intros [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Exy ; setoid_rewrite <- Euv ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Exy ; setoid_rewrite -> Euv ; assumption.
  - exists a, b, c, d ; setoid_rewrite <- Exy ; setoid_rewrite <- Euv ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Exy ; setoid_rewrite -> Euv ; assumption.
Qed.

(** Properties of multiplication. *)

Lemma Rmult_assoc (x y z : R) : ((x * y) * z == x * (y * z))%R.
Admitted.

Lemma Rmult_comm (x y : R) : (x * y == y * x)%R.
Proof.
  split ; intro q ; split ; intros [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
  - exists c, d, a, b ; repeat split ; auto ; setoid_rewrite Qmult_comm; assumption.
  - admit.
  - admit.
  - admit.
Qed.

Lemma Rmult_1_l (x : R) : (1 * x == x)%R.
Proof.
  split ; intro q ; split.
  - intros [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
    apply (lower_lower x q c) ; auto.
    admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma Rmult_1_r (x : R) : x * 1 == x.
Proof.
  (* Use Rmult_comm and Rmult_1_l. *)
  admit.
Qed.

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
