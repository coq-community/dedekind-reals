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
  admit.
Qed.

Theorem Rlt_linear : forall (x y z : R), x < y -> x < z \/ z < y.
Proof.
  admit.
Qed.

(* Properties of <> *)

Theorem Rneq_symm : forall x y : R, x <> y -> y <> x.
Proof.
  admit.
Qed.

Theorem Rneq_irrefl : forall x : R, ~ (x <> x).
Proof.
  admit.
Qed.

Theorem Rnew_contrans : forall x y z : R, x <> y -> x <> z \/ y <> z.
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
  admit.
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
