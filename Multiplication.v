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
  intros q r Eqr ; split ; intros [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Eqr ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Eqr ; assumption.
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
  - intros q r H K.
    unfold mult_lower.
    destruct K as [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
    exists a, b, c, d ; repeat split ; try transitivity r ; auto.
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
  - intros [a [b [c [d [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]]]].
    destruct (Q_dec c 0) as [[G|G]|G].
    + apply (lower_lower x q c) ; auto.
      transitivity (b * c) ; auto.
      setoid_replace c with (1 * c) at 2 ; [ idtac | (ring_simplify ; reflexivity) ].
      apply Qlt_mult_neg_r ; auto.
    + apply (lower_lower x q c) ; auto.
      transitivity (a * c) ; auto.
      setoid_replace c with (1 * c) at 2 ; [ idtac | (ring_simplify ; reflexivity) ].
      apply Qmult_lt_compat_r ; assumption.
    + rewrite G in * |- *.
      apply (lower_lower x q 0) ; auto.
      apply (Qlt_le_trans _ (a * 0)) ; auto.
      ring_simplify ; discriminate.
  - admit.
  - admit.
  - admit.
Qed.

Lemma Rmult_1_r (x : R) : (x * 1 == x)%R.
Proof.
  (* Use Rmult_comm and Rmult_1_l. *)
  admit.
Qed.

(* Distributivity *)

Lemma Qmult_plus_distr_r (x y z : R) : (x * (y + z) == (x * y) + (x * z))%R.
Admitted.

Lemma Qmult_plus_distr_l (x y z : R) : ((x + y) * z == (x * z) + (y * z))%R.
Admitted.

(* Inverse. *)

Theorem Rinv_apart_0 : forall x : R, ({ y | x * y == 1 } -> x ## 0)%R.
Proof.
  intros x [y E].
  admit.
Qed.


(* The inverse of a positive real. *)
Definition Rinv_pos : forall x : R, (0 < x -> R)%R.
Proof.
  intros x H.
  refine {|
      lower := (fun q => exists r, upper x r /\ q * r < 1) ;
      upper := (fun q => exists r, lower x r /\ 0 < r /\ 1 < q * r)
    |}.
  - admit.
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Defined.

Definition Rinv_neg : forall x : R, (x < 0 -> R)%R.
Proof.
  intros x H.
  refine {|
      lower := (fun q => exists r, upper x r /\ r < 0 /\ 1 < q * r) ;
      upper := (fun q => exists r, lower x r /\ q * r < 1)
    |}.
  - admit.
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
  - admit. 
Defined.

Theorem R_field : forall x : R, (x ## 0  -> { y | x * y == 1 })%R.
Proof.
  intros x [H|H].
  - exists (Rinv_neg x H).
    split ; intro q ; split.
    + intros [a [b [c [d [H1 [H2 [[r [R1 [R2 R3]]] [[s [S1 S2]] [H5 [H6 [H7 H8]]]]]]]]]]].
      admit.
    + admit.
    + admit.
    + admit.
  - exists (Rinv_pos x H).
    split ; intro q ; split.
    + intros [a [b [c [d [H1 [H2 [[r [R1 R2]] [[s [S1 [S2 S3]]] [H5 [H6 [H7 H8]]]]]]]]]]].      
    + admit.
    + admit.
    + admit.
Qed.

Theorem R_inv_apart_0 : forall x : R, ({y | x * y == 1} -> x ## 0)%R.
Proof.
  admit.
Qed.
