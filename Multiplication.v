(** The multiplicative structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut Additive MinMax.

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
  - destruct (lower_bound x) as [t P].
    destruct (lower_bound y) as [u S].
    destruct (upper_bound x) as [v K].
    destruct (upper_bound y) as [z M].
exists ((Qmin (Qmin (t*u) (t*z)) (Qmin (v*z) (v*u)))-1).
unfold mult_lower.
exists t,v,u,z ; repeat split.
+ assumption.
+ assumption.
+ assumption.
+ assumption.
+ destruct (Q.min_spec (Qmin (t * u) (t * z)) (Qmin (v * z) (v * u))) as [[G1 H1]|[G1 H1]].
destruct (Q.min_spec (t * u) (t * z)) as [[G2 H2]|[G2 H2]].
destruct (Q.min_spec (v * z) (v * u)) as [[G3 H3]|[G3 H3]].
* setoid_rewrite H1.
setoid_rewrite H2.
apply (Qlt_minus_1 (t*u)).
* setoid_rewrite H1.
setoid_rewrite H2.
apply (Qlt_minus_1 (t*u)).
* setoid_rewrite H1.
setoid_rewrite H2.
assert (W:=(Qlt_minus_1 (t*z))).
assert (E:=(Qlt_le_trans (t*z+(-1#1)) (t*z) (t*u) W G2)).
auto.
* setoid_rewrite H1.
destruct (Q.min_spec (v * z) (v * u)) as [[G3 H3]|[G3 H3]].
setoid_rewrite H3.
destruct (Q.min_spec (v * z) (t * u)) as [[G4 H4]|[G4 H4]].
assert (W:=(Qlt_minus_1 (v*z))).
assert (V:=(Qlt_trans (v*z+(-1#1)) (v*z) (t*u) W G4)).
assumption.
auto.
admit.
admit.
+ admit.
+ admit.
+ admit.
  - admit.
  - intros q r H K.
    unfold mult_lower.
    destruct K as [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
    exists a, b, c, d ; repeat split ; try transitivity r ; auto.
  - intros q K.
destruct K as [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
admit.
  - intros r q H K.
    unfold mult_upper.
    destruct K as [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
    exists a, b, c, d ; repeat split ; try transitivity r ; auto.
  - intros r H.
destruct H as [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
admit.
  - admit.
  - admit.
Defined.

Infix "*" := Rmult : R_scope.

Instance Rmult_comp : Proper (Req ==> Req ==> Req) Rmult.
Proof.
  intros x y Exy u v Euv.
  split ; intros q [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Exy ; setoid_rewrite <- Euv ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Exy ; setoid_rewrite -> Euv ; assumption.
Qed.

(** Properties of multiplication. *)

Lemma Rmult_assoc (x y z : R) : ((x * y) * z == x * (y * z))%R.
Admitted.

Lemma Rmult_comm (x y : R) : (x * y == y * x)%R.
Proof.
  split ; intros q [a [b [c [d [? [? [? [? [? [? [? ?]]]]]]]]]]].
  - exists c, d, a, b ; repeat split ; auto ; setoid_rewrite Qmult_comm; assumption.
  - exists c, d, a, b ; repeat split ; auto ; setoid_rewrite Qmult_comm; assumption.
Qed.
 
Lemma Rmult_1_l (x : R) : (1 * x == x)%R.
Proof.
  split ; intro q.
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
Qed.

Lemma Rmult_1_r (x : R) : (x * 1 == x)%R.
Proof.
  assert(H:= (Rmult_comm x 1)).
  rewrite H.
  apply Rmult_1_l.
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


(* The inverse of a real which is apart from zero. *)
Definition Rinv : forall x : R, (x ## 0 -> R)%R.
Proof.
  intros x H.
  refine {|
      lower := (fun q => (exists r, r < 0 /\ upper x r /\ 1 < q * r) \/
                         (exists r, lower x 0 /\ upper x r /\ q * r < 1)) ;
      upper := (fun q => (exists r, lower x r /\ upper x 0 /\ q * r < 1) \/
                         (exists r, 0 < r /\ lower x r /\ 1 < q * r))
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

(*
Theorem R_pos_field : forall x : R, (0 < x  -> { y | x * y == 1 })%R.
Proof.
  intros x H.
  - exists (Rinv_pos x H).
    split ; intro q ; split.
    + intros [a [b [c [d [H1 [H2 [[r [R1 [R2 R3]]] [[s [S1 [S2 S3]]] [H5 [H6 [H7 H8]]]]]]]]]]].
      simpl.
      destruct (Qlt_le_dec 0 c) as [G|G].
      * transitivity (a * c) ; auto.
        transitivity (c * r) ; auto.
        rewrite Qmult_comm.
        apply Qmult_lt_l ; auto.
        apply (lower_below_upper x) ; assumption.
      * transitivity (b * c) ; auto.
        apply (Qle_lt_trans _ 0) ; [idtac | reflexivity].
        setoid_replace 0 with (b * 0) ; [ idtac | (symmetry ; apply Qmult_0_r)].
        apply Qmult_le_compat_l ; auto.
        apply Qlt_le_weak, (lower_below_upper x) ; auto.
    + admit.
    + admit.
    + admit.
Qed.
*)

Lemma Qmult_le_neg_pos_pos : forall q r, q <= 0 -> 0 <= r -> q * r <= 0.
Proof.
  intros q r H G.
  setoid_replace 0 with (0 * r).
  + now apply Qmult_le_compat_r.
  + reflexivity.
Qed.

Theorem R_field : forall x : R, (x ## 0  -> { y | x * y == 1 })%R.
Proof.
  intros x H.
  exists (Rinv x H).
  split ; intro q.
  - intros [a [b [c [d [H1 [H2 [H3 [H4 [H5 [H6 [H7 H8]]]]]]]]]]].
    simpl.
    destruct H3 as [[r [R1 [R2 R3]]]|[r [R1 [R2 R3]]]] ;
    destruct H4 as [[s [S1 [S2 S3]]]|[s [S1 [S2 S3]]]].
    + destruct (Qlt_le_dec d 0) as [G|G].
      * transitivity (b * d) ; auto.
        transitivity (d * s) ; auto.
        setoid_rewrite (Qmult_comm d s).
        apply Qlt_mult_neg_r ; auto.
        apply (lower_below_upper x) ; auto.
      * transitivity (a * d); auto.
        apply (Qle_lt_trans _ 0) ; [ idtac | reflexivity ].
        apply Qmult_le_neg_pos_pos ; auto.
        apply Qlt_le_weak, (lower_below_upper x) ; auto.
    + exfalso.
      apply (Qlt_irrefl 0), (lower_below_upper x).
      * apply (lower_lower x 0 s) ; auto.
      * apply (upper_upper x r 0) ; auto.
   + exfalso.
     apply (Qlt_irrefl 0), (lower_below_upper x) ; auto.
   + destruct (Qlt_le_dec 0 c) as [G|G].
     * transitivity (a * c) ; auto.
       transitivity (c * r) ; auto.
       setoid_rewrite (Qmult_comm c r).
       apply Qmult_lt_compat_r ; auto.
       apply (lower_below_upper x) ; auto.
     * transitivity (b * c) ; auto.
       apply (Qle_lt_trans _ 0) ; [ idtac | reflexivity ].
       setoid_rewrite (Qmult_comm b c).
       apply Qmult_le_neg_pos_pos ; auto.
       apply Qlt_le_weak, (lower_below_upper x) ; auto.
  - admit.
Qed.

Theorem R_inv_apart_0 : forall x : R, ({y | x * y == 1} -> x ## 0)%R.
Proof.
  intros x [y [F G]].
  assert (H : 1#2 < 1) ; [ reflexivity | idtac ].
  destruct ((G (1#2)) H) as [a [b [c [d [L1 [L2 [L3 [L4 [L5 [L6 [L7 L8]]]]]]]]]]].
  destruct (Q_dec c 0) as [[?|?]|?].
  - left ; exists b ; split ; auto.
    simpl ; transitivity ((1 # 2) / c).
    + admit.
    + admit.
  - right ; exists a ; split ; auto.
    simpl. transitivity ((1 # 2) / c).
    + admit.
    + admit.
  - absurd (1 # 2 < 0).
    + discriminate.
    + setoid_replace 0 with (a * c) ; auto.
      setoid_rewrite q ; ring_simplify ; reflexivity.
Qed.
  