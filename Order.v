(* The order relations < and <=. *)

Require Import Morphisms Setoid.
Require Import QArith.
Require Import Cut.
Require Import Additive Multiplication.
Require Import Archimedean.

Local Open Scope R_scope.

(** A hack to be able to have proof-relevant unfinished constructions.
    When this file is cleaned up, remove this axiom and the tactic. *)
Axiom unfinished : forall (A : Type), A.
Ltac todo := apply unfinished.

(* Properties of < *)

Theorem Rlt_irrefl : forall (x : R), ~ (x < x).
Proof.
  intros x [q [H1 H2]].
  pose (disjoint x q); auto.
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
  intros x [A1|A2]; pose (Rlt_irrefl x); auto.
Qed.

Theorem Rnew_contrans : forall x y z : R, x ## y -> ((x ## z) \/ (y ## z)).
Proof.
  intros. destruct H.
  - destruct (Rlt_linear x y z H). left. left. apply H0.
    right. right. apply H0.
  - destruct (Rlt_linear y x z H). right. left. apply H0.
    left. right. apply H0.
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

Theorem Rle_antisym : forall (x y : R), x <= y -> y <= x -> x == y.
Proof.
  intros x y H G.
  split ; assumption.
Qed.

(* Relationship between < and <=. *)

Theorem Rlt_le_weak : forall (x y : R), x < y -> x <= y.
Proof.
  intros x y [q [Q1 Q2]].
  intros s H.
  apply (lower_lower y s q) ; auto.
  apply (lower_below_upper x) ; auto.
Qed.

Theorem Rnot_lt_le : forall (x y : R), ~ (x < y) <-> y <= x.
Proof.
  intros x y.
  split.
  - intros H q G.
    destruct (lower_open y q G) as [r [? ?]].
    unfold Rlt in H.
    destruct (located x q r) ; auto.
    elim H.
    exists r ; auto.
  - intros H abs. pose proof (Rlt_le_weak x y abs).
    pose proof (Rle_antisym x y H0 H). rewrite H1 in abs.
    apply (Rlt_irrefl y abs).
Qed.

Theorem Rlt_le_trans : forall (x y z : R), x < y -> y <= z -> x < z.
Proof.
  intros x y z [q [? ?]] ?.
  exists q ; auto.
Qed.

Theorem Rle_lt_trans : forall (x y z : R), x <= y -> y < z -> x < z.
Proof.
  intros x y z ? [q [? ?]].
  exists q.
  split ; auto.
  apply Rle_equiv in H ; auto.
Qed.

(* Compatibility of < and <= with additive structure.

   This compatibility is equivalent to
   the density of Q in R, because of the case :
      forall (r : Q) (x : R),
         Qlt 0 r -> Rlt x (x + R_of_Q r)
   where Rlt means the existence of a rational number
   between x and x+r. *)

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
  split.
  - intros [q maj].
    (* Get another rational number between r1 and r2 *)
    destruct (upper_open x q) as [t H]. apply maj.
    (* approximate r *)
    destruct (archimedean z (q-t)) as [h [u H0]].
    rewrite <- (Qlt_minus_iff t q). apply H.
    exists (q+h)%Q. split.
    + destruct (upper_open x t). apply H.
      exists x0,u. split. 2: split. 2: apply H1. 2: apply H0.
      apply (Qlt_trans _ (t+u)). apply Qplus_lt_l. apply H1.
      apply (Qplus_lt_l _ _ (-t-h)). ring_simplify.
      destruct H0,H2. ring_simplify in H3. rewrite <- (Qplus_comm q).
      apply H3.
    + destruct (lower_open y q). apply maj.
      exists x0,h. split. apply Qplus_lt_l. apply H1.
      split. apply H1. apply H0.
  - intros [q [[a [b H]] [c [d H0]]]].
    destruct H,H0,H1,H2.
    pose proof (Qlt_trans (a+b) q (c + d) H H0).
    clear H. clear H0. clear q.
    pose proof (lower_below_upper z d b H4 H3).
    clear H4. clear H3. clear z.
    exists a. split. apply H1. apply (lower_le y a c).
    apply H2. apply Qlt_le_weak.
    rewrite <- (Qplus_lt_l _ _ b). apply (Qlt_trans _ (c+d) _ H5).
    apply Qplus_lt_r. apply H.
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
  split.
  - intros H. rewrite <- Rnot_lt_le. intro abs.
    apply Rplus_lt_compat_r in abs. rewrite <- Rnot_lt_le in H.
    contradiction.
  - intros. rewrite <- Rnot_lt_le in H. rewrite <- Rnot_lt_le.
    intro abs. apply (Rplus_lt_compat_r _ _ z) in abs. contradiction.
Qed.

Theorem Rplus_le_compat_l : forall (x y z : R),  y <= z <-> x + y <= x + z.
Proof.  
  intros. rewrite Rplus_comm. rewrite <- (Rplus_comm z).
  apply Rplus_le_compat_r.
Qed.

Theorem Rplus_positive : forall (x y : R), 0 < x + y -> 0 < x \/ 0 < y.
Proof.
  unfold Rlt.
  intros.
  destruct H as [q [H1 H2]]. destruct H2 as [r [s H2]].
  destruct (Qlt_le_dec 0 r).
  - left. exists r. split. apply q0. apply H2.
  - right. exists s. split. 2: apply H2. destruct H2.
    apply (Qplus_lt_r _ _ (-r)) in H.
    ring_simplify in H. apply (Qlt_trans 0 ((-1 # 1) * r + q)).
    2: apply H. rewrite <- (Qplus_0_r 0).
    rewrite <- (Qplus_comm q). apply Qplus_lt_le_compat.
    apply H1. apply (Qplus_le_r _ _ r). ring_simplify. apply q0.
Qed.

(* Compatibility of < and <= with multiplicative structure. *)

Theorem Rmult_le_compat_r : forall (x y z : R), 0 <= z -> x <= y -> x * z <= y * z.
Proof.
  todo.
Qed.

Theorem Rmult_le_compat_l : forall (x y z : R), 0 <= x -> y <= z -> x * y <= x * z.
Proof.
  todo.
Qed.

Theorem Rmult_lt_compat_r : forall (x y z : R), 0 < z -> (x < y <-> x * z < y * z).
Proof.
  todo.
Qed.

Theorem Rmult_lt_compat_l : forall (x y z : R), 0 < x -> (y < z <-> x * y < x * z).
Proof.
  todo.
Qed.
