(* The lattice structure of the reals. *)

Require Import Setoid Morphisms.
Require Import QArith.
Require Import Qminmax.

Require Import Cut MiscLemmas Order.

Local Open Scope R_scope.

Definition Rmin : R -> R -> R.
Proof.
  intros x y.
  refine {| lower := (fun q => lower x q /\ lower y q) ;
            upper := (fun q => upper x q \/ upper y q) |}.
  - intros ? ? E. rewrite E ; tauto.
  - intros ? ? E. rewrite E ; tauto.
  - destruct (lower_bound x) as [q ?].
    destruct (lower_bound y) as [r ?].
    exists (Qmin q r).
    split.
    + destruct (Q.min_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H. auto using (lower_le x r q).
    + destruct (Q.min_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H. auto using (lower_lower y q r).
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
      auto using (disjoint x q).
      auto using (disjoint y q).
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
  - destruct (upper_bound x) as [q ?].
    destruct (upper_bound y) as [r ?].
    exists (Qmax q r).
    split.
    + destruct (Q.max_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H. auto using (upper_upper x q r).
      * setoid_rewrite H ; assumption.
    + destruct (Q.max_spec q r) as [[G H]|[G H]].
      * setoid_rewrite H ; assumption.
      * setoid_rewrite H. auto using (upper_le y r q).
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
        auto using (upper_le x q s U G).
    + destruct (Q.max_spec s q) as [[G H]|[G H]].
      * setoid_rewrite H.
        auto using (upper_upper y s q G P).
      * setoid_rewrite H ; assumption.
  - intro.
    apply neg_false.
    split.
    + intros [[lx | ly] [ux  uy]].
      auto using (disjoint x q).
      auto using (disjoint y q).
    + tauto.
  - intros q r T.
    assert (H:=(located x q r T)).
    assert (K:=(located y q r T)).
    tauto.
Qed.

(** The lattice structure of [R] with respect to [Rmin] and [Rmax]. *)

Theorem Rmin_spec (x y z : R) : z <= Rmin x y <-> z <= x /\ z <= y.
Proof.
split.
- intro.
split.
+ admit.
+ admit.
- intros [H1 H2].
admit.
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
  assert (H:=(Rmin_lower_l x x)).
  assert (K:=proj2 (Rmin_spec x x x)).
  firstorder.
Qed.

Theorem Rmin_comm (x y : R) : Rmin x y == Rmin y x.
Proof.
  destruct (proj1 (Rmin_spec x y (Rmin x y)) (Rle_refl _)).
  destruct (proj1 (Rmin_spec y x (Rmin y x)) (Rle_refl _)).
  firstorder.
Qed.

Theorem Rmin_assoc (x y z : R) : Rmin x (Rmin y z) == Rmin (Rmin x y) z.
Proof.
  admit.
Qed.

Theorem Rmax_spec (x y z : R) : Rmax x y <= z <-> x <= z /\ y <= z.
Proof.
  admit.
Qed.

Theorem Rmax_upper_l (x y : R) : x <= Rmax x y.
Proof.
  destruct (proj1 (Rmax_spec x y (Rmax x y)) (Rle_refl _)) ; assumption.
Qed.

Theorem Rmax_upper_r (x y : R) : y <= Rmax x y. (* Tu je bilo prej Rmax_lower_r /.../ y <= Rmin x y.*)
Proof.
  destruct (proj1 (Rmax_spec x y (Rmax x y)) (Rle_refl _)) ; assumption.
Qed.

Theorem Rmax_idempotent (x : R) : Rmax x x == x.
Proof.
  assert (H:=(Rmax_upper_l x x)).
  assert (K:=proj2 (Rmax_spec x x x)).
  firstorder.
Qed.

Theorem Rmax_comm (x y : R) : Rmax x y == Rmax y x.
Proof.
  destruct (proj1 (Rmax_spec x y (Rmax x y)) (Rle_refl _)).
  destruct (proj1 (Rmax_spec y x (Rmax y x)) (Rle_refl _)).
  admit. (* Zakaj tu firstorder odpove, pri Rmin_comm pa deluje? *)
Qed.

Theorem Rmax_assoc (x y z : R) : Rmax x (Rmax y z) == Rmax (Rmax x y) z.
Proof.
  admit.
Qed.
