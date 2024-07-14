(* The lattice structure of the reals. *)

From Coq Require Import Setoid Morphisms.
From Coq Require Import QArith.
From Coq Require Import Qminmax.

From DedekindReals Require Import Cut MiscLemmas Additive Multiplication Order.

Local Open Scope R_scope.

(** A hack to be able to have proof-relevant unfinished constructions.
    When this file is cleaned up, remove this axiom and the tactic. *)
Axiom unfinished : forall (A : Type), A.
Ltac todo := apply unfinished.

Definition Rmin : R -> R -> R.
Proof.
  intros x y.
  refine {| lower := (fun q => lower x q /\ lower y q) ;
            upper := (fun q => upper x q \/ upper y q) |}.
  - intros ? ? E. rewrite E ; tauto.
  - intros ? ? E. rewrite E ; tauto.
  - destruct (lower_bound x) as [q qmaj].
    destruct (lower_bound y) as [r rmaj].
    exists (Qmin q r).
    split.
    + destruct (Q.min_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H. pose (lower_le x r q); auto.
    + destruct (Q.min_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H. pose (lower_lower y q r); auto.
      * setoid_rewrite H ; assumption.
  - destruct (upper_bound y) as [r ?].
    exists r.
    right.
    assumption.
  - intros q r H [A B].
    assert (C:=(lower_lower x q r H A)).
    assert (D:=(lower_lower y q r H B)).
    auto.
  - intros q [A B].
    assert (C:=(lower_open x q A)).
    destruct C as [r [T U]].
    assert (D:=(lower_open y q B)).
    destruct D as [s [M P]].
    exists (Qmin s r).
    repeat split.
    + destruct (Q.min_spec s r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H ; assumption.
    + destruct (Q.min_spec s r) as [[G H]|[G H]].
      * setoid_rewrite H. 
        assert (C:=(lower_lower x s r G U)).
        assumption.
      * setoid_rewrite H ; assumption.
    + destruct (Q.min_spec s r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H.
        assert (K:=(Qle_lteq r s)).
        rewrite K in G.
        destruct G as [G1 | G2].
        clear K.
        assert (C:=(lower_lower y r s G1 P)).
        assumption.
        clear K.
        setoid_rewrite G2.
        assumption.
  - intros q r H [A | B].
    assert (C:=(upper_upper x q r H A)).
    left.
    assumption.
    assert (D:=(upper_upper y q r H B)).
    right.
    assumption.
  - intros r [A | B].
    + assert (C:=(upper_open x r A)).
      destruct C as [q [T U]].
      exists q.
      split.
      assumption.
      left ; assumption.
    + assert (C:=(upper_open y r B)).
      destruct C as [q [T U]].
      exists q.
      split.
      assumption.
      right ; assumption.
  - intro.
    apply neg_false.
    split.
    + intros [[lx ly] [ux | uy]].
      pose (disjoint x q); auto.
      pose (disjoint y q); auto.
    + tauto.
  - intros q r T.
    assert (H:=(located x q r T)).
    assert (K:=(located y q r T)).
    tauto.
Defined.

Definition Rmax : R -> R -> R.
Proof.
  intros x y.
  refine {| lower := (fun q => lower x q \/ lower y q) ;
            upper := (fun q => upper x q /\ upper y q) |}.
  - intros ? ? E. rewrite E ; tauto.
  - intros ? ? E. rewrite E ; tauto.
  - destruct (lower_bound x) as [q ?].
    exists q.
    left ; assumption.
  - destruct (upper_bound x) as [q qmaj].
    destruct (upper_bound y) as [r rmaj].
    exists (Qmax q r).
    split.
    + destruct (Q.max_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H. pose (upper_upper x q r); auto.
      * setoid_rewrite H ; assumption.
    + destruct (Q.max_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H. pose (upper_le y r q); auto.
  - intros q r H [A | B].
    + assert (C:=(lower_lower x q r H A)).
      left ; assumption.
    + assert (D:=(lower_lower y q r H B)).
      right ; assumption.
  - intros q [A | B].
    + assert (C:=(lower_open x q A)).
      destruct C as [r0 [T U]].
      exists r0.
      split.
      assumption.
      left ; assumption.
    + assert (C:=(lower_open y q B)).
      destruct C as [r0 [T U]].
      exists r0.
      split.
      assumption.
      right ; assumption.
  - intros q r H [A B].
    assert (C:=(upper_upper x q r H A)).
    assert (D:=(upper_upper y q r H B)).
    auto.
  - intros r [A B].
    assert (C:=(upper_open x r A)).
    destruct C as [q [T U]].
    assert (D:=(upper_open y r B)).
    destruct D as [s [M P]].
    exists (Qmax s q).
    repeat split.
    + destruct (Q.max_spec s q) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H ; assumption.
    + destruct (Q.max_spec s q) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H.
        pose (upper_le x q s U G); auto.
    + destruct (Q.max_spec s q) as [[G H]|[G H]].
      * setoid_rewrite H.
        pose (upper_upper y s q G P); auto.
      * setoid_rewrite H ; assumption.
  - intro.
    apply neg_false.
    split.
    + intros [[lx | ly] [ux  uy]].
      pose (disjoint x q); auto.
      pose (disjoint y q); auto.
    + tauto.
  - intros q r T.
    assert (H:=(located x q r T)).
    assert (K:=(located y q r T)).
    tauto.
Qed.

(** The lattice structure of [R] with respect to [Rmin] and [Rmax]. *)

Theorem Rmin_spec (x y z : R) : z <= Rmin x y <-> z <= x /\ z <= y.
Proof.
unfold Rle.
split.
- intro.
split.
+ intros q A.
assert (C:=(H q A)).
destruct C.
assumption.
+ intros q A.
assert (C:=(H q A)).
destruct C.
assumption.
- intros [H1 H2].
intros q A.
assert (C1:=(H1 q A)).
assert (C2:=(H2 q A)).
firstorder.
Qed.

Theorem Rmin_lower_l (x y : R) : Rmin x y <= x.
Proof.
  destruct (proj1 (Rmin_spec x y (Rmin x y)) (Rle_refl _)) ; assumption.
Qed.

Theorem Rmin_lower_r (x y : R) : Rmin x y <= y.
Proof.
  destruct (proj1 (Rmin_spec x y (Rmin x y)) (Rle_refl _)) ; assumption.
Qed.

Theorem Rmin_idempotent (x : R) : Rmin x x == x.
Proof.
  split.
  - apply Rmin_lower_l.
  - apply Rmin_spec ; split ; apply Rle_refl.
Qed.

Theorem Rmin_comm (x y : R) : Rmin x y == Rmin y x.
Proof.
  split ; apply Rmin_spec ; auto using Rmin_lower_l, Rmin_lower_r.
Qed.

Theorem Rmin_assoc (x y z : R) : Rmin x (Rmin y z) == Rmin (Rmin x y) z.
Proof.
  firstorder.
Qed.

Theorem Rmax_spec (x y z : R) : Rmax x y <= z <-> x <= z /\ y <= z.
Proof.
  todo.
Qed.

Theorem Rmax_upper_l (x y : R) : x <= Rmax x y.
Proof.
  apply (Rmax_spec x y  (Rmax x y)), Rle_refl.
Qed.

Theorem Rmax_upper_r (x y : R) : y <= Rmax x y.
Proof.
  apply (Rmax_spec x y (Rmax x y)), Rle_refl.
Qed.

Theorem Rmax_idempotent (x : R) : Rmax x x == x.
Proof.
  split.
  - apply (Rmax_spec x x x) ; split ; apply Rle_refl.
  - apply Rmax_upper_l.
Qed.

Theorem Rmax_comm (x y : R) : Rmax x y == Rmax y x.
Proof.
  split ; apply Rmax_spec ; auto using Rmax_upper_l, Rmax_upper_r.
Qed.

Theorem Rmax_assoc (x y z : R) : Rmax x (Rmax y z) == Rmax (Rmax x y) z.
Proof.
  split.
  - apply Rmax_spec.
    split.
    + assert(A:=(Rmax_upper_l x y)).
      assert(B:=(Rmax_upper_l (Rmax x y) z)).
      assert(C:=(Rle_trans x (Rmax x y) (Rmax (Rmax x y) z) A B)).
      assumption.
    + apply Rmax_spec ; split.
      * assert(A:=(Rmax_upper_r x y)).
        assert(B:=(Rmax_upper_l (Rmax x y) z)).
        assert(C:=(Rle_trans y (Rmax x y) (Rmax (Rmax x y) z) A B)).
        assumption.
      * assert(A:=(Rmax_upper_r (Rmax x y) z)) ; assumption.
  - apply Rmax_spec ; split.
    + apply Rmax_spec ; split.
      * assert(A:=(Rmax_upper_l x (Rmax y z))) ; assumption.
      * assert(A:=(Rmax_upper_l y z)).
        assert(B:=(Rmax_upper_r x (Rmax y z))).
        assert(C:=(Rle_trans y (Rmax y z) (Rmax x (Rmax y z) ) A B)).
        assumption.
    + assert(A:=(Rmax_upper_r y z)).
      assert(B:=(Rmax_upper_r x (Rmax y z))).
      assert(C:=(Rle_trans z (Rmax y z) (Rmax x (Rmax y z)) A B)).
      assumption.
Qed.

(* Distributivity of + over min and max. *)

Theorem Rmin_plus_distr_r (x y z : R) : Rmin (x + z) (y + z) == Rmin x y + z.
Proof.
  todo.
Qed.

Theorem Rmin_plus_distr_l (x y z : R) : Rmin (x + y) (x + z) == x + Rmin y z.
Proof.
  todo.
Qed.

Theorem Rmax_plus_distr_r (x y z : R) : Rmax (x + z) (y + z) == Rmax x y + z.
Proof.
  todo.
Qed.

Theorem Rmax_plus_distr_l (x y z : R) : Rmax (x + y) (x + z) == x + Rmax y z.
Proof.
  todo.
Qed.

(* Distributivity of * over min and max. *)

Theorem Rmin_mult_distr_r (x y z : R) : 0 < z -> Rmin (x * z) (y * z) == Rmin x y * z.
Proof.
  todo.
Qed.

Theorem Rmin_mult_distr_l (x y z : R) : 0 < x -> Rmin (x * y) (x * z) == x * Rmin y z.
Proof.
  todo.
Qed.

Theorem Rmax_mult_distr_r (x y z : R) : 0 < z -> Rmax (x * z) (y * z) == Rmax x y * z.
Proof.
  todo.
Qed.

Theorem Rmax_mult_distr_l (x y z : R) : 0 < x -> Rmax (x * y) (x * z) == x * Rmax y z.
Proof.
  todo.
Qed.

(* Opposite in relation to min and max. *)

Theorem Ropp_min (x y : R) : Rmin (-x) (-y) == - (Rmax x y).
Proof.
  todo.
Qed.

Theorem Ropp_max (x y : R) : Rmax (-x) (-y) == - (Rmin x y).
Proof.
  todo.
Qed.
