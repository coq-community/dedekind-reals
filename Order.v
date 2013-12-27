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

Theorem Req_neq: forall x y:R, {x==y} + {x##y}.
Admitted.

Theorem Rnew_contrans : forall x y z : R, x ## y -> ((x ## z) + (y ## z))%type.
Proof.
  intros.
  destruct (Req_neq x z).
  - destruct r as [H1 H2].
    right.
    admit.  (*first order can solve this*)
  - left; assumption.
Qed.



(* Properties of <= *)

Theorem Rle_refl : forall (x : R), x <= x.
Proof.
  intros ? ? ? ; assumption.
Qed.

Theorem Rle_trans : forall (x y z : R), x <= y -> y <= z -> x <= z.
Proof.
  unfold Rle.
  intros.
  apply H0.
  apply H.
  apply H1.
Qed.

Theorem R_covered: forall (x:R)(q:Q), {lower x q} + {upper x q}.
Admitted.

Theorem Rle_antisym : forall (x y : R), x <= y -> y <= x -> x == y.
Proof.
  unfold Rle.
  intros.
  unfold Req.
  split.
  - split; auto.
  - split. 
    + destruct (R_covered y q); [idtac|auto].
      assert (lower x q); [auto using H0 | idtac].
      assert (~(upper x q)); [ auto using (disjoint x q)|tauto].
    + destruct (R_covered x q); [idtac|auto].
      assert (lower y q); [auto using H0 | idtac].
      assert (~(upper y q)); [ auto using (disjoint y q)|tauto].
    
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
  intros.
  split.
  - unfold Rlt, Rle.
    intros.
    destruct (R_covered x q); [assumption|idtac].
    destruct H.
    exists q; split; assumption.
  - unfold Rlt, Rle.
    intros.
    admit.
Qed.

Theorem Rlt_le_trans : forall (x y z : R), x < y -> y <= z -> x < z.
Proof.
  unfold Rlt, Rle.
  intros.
  destruct H as [q [H1 H2]].
  exists q.
  split; [assumption | auto using H0].
Qed.

Theorem Rle_lt_trans : forall (x y z : R), x <= y -> y < z -> x < z.
Proof.
  unfold Rlt, Rle.
  intros.
  destruct H0 as [q [H1 H2]].
  exists q; split; [idtac|assumption].
  destruct (R_covered x q); [idtac|assumption].
  assert (lower y q); [auto using H|idtac].
  exfalso. 
  apply (disjoint y q).
  split; assumption.
Qed.

(* Compatibility of < and <= with additive structure. *)

Theorem R0_lt_1 : 0 < 1.
Proof.
  unfold Rlt.
  exists (1#2)%Q.
  split. 
  assert (0<(1#2))%Q; [reflexivity | auto].
  assert ((1#2)<1)%Q; [reflexivity | auto]. 
Qed.

Theorem Rplus_lt_compat_r : forall (x y z : R),  x < y <-> x + z < y + z.
Proof.
  unfold Rlt.
  split;intros;destruct H as [q [H1 H2]].
  - admit.
  - admit.
Qed.

Theorem Rplus_lt_compat_l : forall (x y z : R),  y < z <-> x + y < x + z.
Proof.
  intros.
  rewrite (Rplus_comm x y).
  rewrite (Rplus_comm x z).
  apply (Rplus_lt_compat_r y z x).
Qed.

Theorem Rplus_le_compat_r : forall (x y z : R),  x <= y <-> x + z <= y + z.
Proof.
  unfold Rle.
  split; intros.
  - admit.
  - admit.
Qed.

Theorem Rplus_le_compat_l : forall (x y z : R),  y <= z <-> x + y <= x + z.
Proof.  
  intros.
  admit.
Qed.

Theorem Rplus_positive : forall (x y : R), 0 < x + y -> 0 < x \/ 0 < y.
Proof.
  unfold Rlt.
  intros.
  destruct H as [q [H1 H2]].
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
