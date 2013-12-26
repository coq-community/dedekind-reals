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
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
  - admit.
Defined.

Definition Rmax : R -> R -> R.
Proof.
  intros x y.
  refine {| lower := (fun q => lower x q \/ lower y q) ;
            upper := (fun q => upper x q /\ upper y q) |}.
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
Qed.

(** The lattice structure of [R] with respect to [Rmin] and [Rmax]. *)

Theorem Rmin_spec (x y z : R) : z <= Rmin x y <-> z <= x /\ z <= y.
Proof.
  admit.
Qed.

Theorem Rmin_lower_l (x y : R) : Rmin x y <= x.
Proof.
  destruct (proj1 (Rmin_spec x y (Rmin x y)) (Rle_refl _)) ; assumption.
Qed.

Theorem Rmin_lower_r (x y : R) : Rmin x y <= y.
Proof.
  admit.
Qed.

Theorem Rmin_idempotent (x : R) : Rmin x x == x.
Proof.
  admit.
Qed.

Theorem Rmin_comm (x y : R) : Rmin x y == Rmin y x.
Proof.
  admit.
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

Theorem Rax_lower_r (x y : R) : y <= Rmin x y.
Proof.
  admit.
Qed.

Theorem Rmax_idempotent (x : R) : Rmax x x == x.
Proof.
  admit.
Qed.

Theorem Rmax_comm (x y : R) : Rmax x y == Rmax y x.
Proof.
  admit.
Qed.

Theorem Rmax_assoc (x y z : R) : Rmax x (Rmax y z) == Rmax (Rmax x y) z.
Proof.
  admit.
Qed.
