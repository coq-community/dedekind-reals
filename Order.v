(* The order relations < and <=. *)

Require Import Morphisms Setoid.
Require Import QArith.
Require Import Cut.
Require Import Additive Multiplication.

Local Open Scope R_scope.

(* Properties of < *)

Theorem Rlt_irrefl : forall (x : R), ~ (x < x).
Proof.
  intros x [q [H1 H2]].
  auto using (disjoint x q).
Qed.

Theorem Rlt_trans : forall (x y z : R), x < y -> y < z -> x < z.
Proof.
  intros x y z [q [Q1 Q2]] [r [R1 R2]].
  unfold Rlt.
  assert(A:=(lower_below_upper y q r Q2 R1)).
  exists q.
  split.
  assumption.
  assert(B:=(lower_lower z q r A R2)).
  assumption.
Qed.

Theorem Rlt_asymm : forall x y : R, ~ (x < y /\ y < x).
Proof.
  intros x y [G H].
  apply (Rlt_irrefl x).
  apply (Rlt_trans x y x) ; assumption.
Qed.

Theorem Rlt_linear : forall (x y z : R), x < y -> x < z \/ z < y.
Proof.
  intros x y z [q [Q1 Q2]].
  destruct (upper_open x q Q1) as [s [S1 S2]].
  destruct (located z s q S1) as [L|L].
  - left ; exists s ; auto.
  - right ; exists q ; auto.
Qed.

(* Properties of apartness ## *)

Theorem Rneq_symm : forall x y : R, x ## y -> y ## x.
Proof.
  intros x y.
  unfold Rneq ; intro A.
  tauto.
Qed.

Theorem Rneq_irrefl : forall x : R, x ## x -> False.
Proof.
  intros x [A1|A2]; auto using (Rlt_irrefl x).
Qed.

Theorem Rnew_contrans : forall x y z : R, x ## y -> ((x ## z) + (y ## z))%type.
Proof.
  admit.
Qed.


(* Properties of <= *)

Theorem Rle_refl : forall (x : R), x <= x.
Proof.
  intros ? ? ? ; assumption.
Qed.

Theorem Rle_trans : forall (x y z : R), x <= y -> y <= z -> x <= z.
Proof.
  admit.
Qed.

Theorem Rle_antisym : forall (x y : R), x <= y -> y <= x -> x == y.
Proof.
  admit.
Qed.

(* Relationship between < and <=. *)

Theorem Rlt_le_weak : forall (x y : R), x < y -> x <= y.
Proof.
  intros x y [q [Q1 Q2]].
  unfold Rle.
  intros s H.
  assert(A:=(lower_below_upper x s q H Q1)).
  assert(B:=(lower_lower y s q A Q2)).
  assumption.
Qed.

Theorem Rnot_lt_le : forall (x y : R), ~ (x < y) <-> y <= x.
Proof.
  admit.
Qed.

Theorem Rlt_le_trans : forall (x y z : R), x < y -> y <= z -> x < z.
Proof.
  admit.
Qed.

Theorem Rle_lt_trans : forall (x y z : R), x <= y -> y < z -> x < z.
Proof.
  admit.
Qed.

(* Compatibility of < and <= with additive structure. *)

Theorem R0_lt_1 : 0 < 1.
Proof.
  admit.
Qed.

Theorem Rplus_lt_compat_r : forall (x y z : R),  x < y <-> x + z < y + z.
Proof.
  admit.
Qed.

Theorem Rplus_lt_compat_l : forall (x y z : R),  y < z <-> x + y < x + z.
Proof.
  admit.
Qed.

Theorem Rplus_le_compat_r : forall (x y z : R),  x <= y <-> x + z <= y + z.
Proof.
  admit.
Qed.

Theorem Rplus_le_compat_l : forall (x y z : R),  y <= z <-> x + y <= x + z.
Proof.
  admit.
Qed.

Theorem Rplus_positive : forall (x y : R), 0 < x + y -> 0 < x \/ 0 < y.
Proof.
  admit.
Qed.

(* Compatibility of < and <= with multiplicative structure. *)

Theorem Rmult_le_compat_r : forall (x y z : R), 0 <= z -> x <= y -> x * z <= y * z.
Proof.
  admit.
Qed.

Theorem Rmult_le_compat_l : forall (x y z : R), 0 <= x -> y <= z -> x * y <= x * z.
Proof.
  admit.
Qed.

Theorem Rmult_lt_compat_r : forall (x y z : R), 0 < z -> (x < y <-> x * z < y * z).
Proof.
  admit.
Qed.

Theorem Rmult_lt_compat_l : forall (x y z : R), 0 < x -> (y < z <-> x * y < x * z).
Proof.
  admit.
Qed.
