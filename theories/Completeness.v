(* Dedekind completeness: any cut of real numbers determines a real.
   In other words, if we perform the Dedekind construction on R we just
   get R back. 
*)

From Coq Require Import Morphisms.
From Coq Require Import QArith.
From DedekindReals Require Import Cut Order.

Local Open Scope R_scope.

(* We define the cuts on reals by mimicking the definition of cuts on rationals. *)
Structure RCut := {
  r_lower : R -> Prop;
  r_upper : R -> Prop;
  r_lower_proper : Proper (Req ==> iff) r_lower;
  r_upper_proper : Proper (Req ==> iff) r_upper;
  r_lower_bound : exists x : R, r_lower x;
  r_upper_bound : exists x : R, r_upper x;
  r_lower_lower : forall x y, x < y -> r_lower y -> r_lower x;
  r_lower_open : forall x, r_lower x -> exists y, x < y /\ r_lower y;
  r_upper_upper : forall x y, x < y -> r_upper x -> r_upper y;
  r_upper_open : forall y, r_upper y -> exists x,  x < y /\ r_upper x;
  r_disjoint : forall x, ~ (r_lower x /\ r_upper x);
  r_located : forall x y, x < y -> r_lower x \/ r_upper y
}.

Definition RCut_eq (c d : RCut) :=
  (forall x, r_lower c x <-> r_lower d x) /\ (forall x, r_upper c x <-> r_upper d x).

Lemma RCut_eq_refl : forall c:RCut, RCut_eq c c.
Proof.
  intro c. split; intro; tauto.
Qed.

Lemma RCut_eq_sym : forall c d:RCut, RCut_eq c d -> RCut_eq d c.
Proof.
  intro.
  intros y H.
  unfold RCut_eq.
  destruct H.
  split.
  + intro x0.
    apply iff_sym.
    apply H.
  + intro x0.
    apply iff_sym.
    apply H0.
Qed.

Lemma RCut_eq_trans : forall c d e:RCut,
    RCut_eq c d -> RCut_eq d e -> RCut_eq c e.
Proof.
  intro.
  intros y z A B.
  destruct A as [A1 A2].
  destruct B as [B1 B2].
  unfold RCut_eq.
  split.
  + intro.
    eauto using iff_trans.
  + intro.
    eauto using iff_trans.
Qed.

Add Parametric Relation : RCut RCut_eq
    reflexivity proved by RCut_eq_refl
    symmetry proved by RCut_eq_sym
    transitivity proved by RCut_eq_trans
      as RCut_eq_rel.

(* Every real determines a real cut. *)
Definition RCut_of_R : R -> RCut.
Proof.
  intro x.
  refine {| r_lower := (fun y => y < x) ; r_upper := (fun z => x < z) |}.
  - intros u v Euv.
    split ; intro H.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite -> Euv ; assumption.
  - intros u v Euv.
    split ; intro H.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite -> Euv ; assumption.
  - destruct (lower_bound x) as [y P].
    exists y.
    destruct (lower_open x y P) as [m [M1 M2]].
    exists m ; auto using M1.
  - destruct (upper_bound x) as [y P].
    exists y.
    destruct (upper_open x y P) as [m [M1 M2]].
    exists m ; auto using M1.
  - intros a b A B.
    apply (Rlt_trans a b x A B).
  - intros z [q [A B]].
    exists q.
    split.
    + destruct (upper_open z q A) as [r [S T]].
      exists r ; auto.
    + destruct (lower_open x q B) as [r [S T]].
      exists r ; auto.
  - intros a b A B.
    apply (Rlt_trans x a b B A).
  - intros y [q [H K]].
    exists q.
    split.
    + destruct (lower_open y q K) as [r [S T]].
      exists r ; auto.
    + destruct (upper_open x q H) as [r [S T]].
      exists r ; auto.
  - auto using Rlt_asymm.
  - auto using Rlt_linear.
Defined.

(* Every real cut determines a real. *)
Definition R_of_RCut : RCut -> R.
Proof.
  intro c.
  refine {| lower := (fun q => exists x, r_lower c x /\ lower x q) ;
            upper := (fun q => exists y, r_upper c y /\ upper y q)
         |}.
  - intros q r E.
    split.
    + intros [x [? G]].
      exists x.
      rewrite E in G.
      auto.
    + intros [x [? G]].
      exists x.
      rewrite <- E in G.
      auto.
  - intros q r E.
    split.
    + intros [x [? G]].
      exists x.
      rewrite E in G.
      auto.
    + intros [x [? G]].
      exists x.
      rewrite <- E in G.
      auto.
  - destruct (r_lower_bound c) as [x ?].
    destruct (lower_bound x) as [q ?].
    exists q, x ; auto.
  - destruct (r_upper_bound c) as [x ?].
    destruct (upper_bound x) as [q ?].
    exists q, x ; auto.
  - intros q r A [x [C D]].
    exists x.
    split ; auto.
    apply (lower_lower x q r) ; assumption.
  - intros q [x [C D]].
    destruct (lower_open x q D) as [r [F G]].
    exists r.
    split ; auto.
    exists x ; auto.
  - intros q r A [x [C D]].
    exists x.
    split ; auto.
    apply (upper_upper x q r) ; assumption.
  - intros r [y [C D]].
    destruct (upper_open y r D) as [q [F G]].
    exists q.
    split ; auto.
    exists y ; auto.
  - intros q [[x [H1 H2]] [y [G1 G2]]].
    absurd (r_lower c x /\ r_upper c x).
    + apply r_disjoint.
    + split ; auto.
      apply (r_upper_upper c y x) ; auto.
      exists q ; auto.
  - intros q r H.
    assert (G : ((q + q + r) * (1#3) < (q + r + r) * (1#3))%R).
    + exists ((q + r) * (1#2)) ; split.
      * apply (Qmult_lt_r _ _ (6#1)); [reflexivity | idtac].
        apply (Qplus_lt_r _ _ (- (3#1) * q - (2#1) * r)).
        now ring_simplify.
      * apply (Qmult_lt_r _ _ (6#1)); [reflexivity | idtac].
        apply (Qplus_lt_r _ _ (- (2#1) * q - (3#1) * r)).
        now ring_simplify.
    + destruct (r_located c ((q + q + r) * (1#3)) ((q + r + r) * (1#3)) G).
      * left; exists ((q + q + r) * (1#3)) ; split ; auto.
        apply (Qmult_lt_r _ _ (3#1)); [reflexivity | idtac].
        apply (Qplus_lt_r _ _ (- (2#1) * q)).
        now ring_simplify.
      * right ; exists ((q + r + r) * (1#3)) ; split ; auto.
        apply (Qmult_lt_r _ _ (3#1)); [reflexivity | idtac].
        apply (Qplus_lt_r _ _ (- (2#1) * r)).
        now ring_simplify.
Defined.

(* The passage from real cuts to reals to real cuts is identity,
   which shows that every real cut is determined by a real, i.e.,
   we have Dedekind completeness. *)
Theorem dedekind_complete :
  forall c : RCut, RCut_eq c (RCut_of_R (R_of_RCut c)).
Proof.
  intro c ; split ; intro x ; split ; intro H.
  - destruct (r_lower_open c x H) as [y [[q [? ?]] ?]].
    exists q ; split ; auto.
    exists y ; auto.
  - destruct H as [q [? [y [? ?]]]].
    apply (r_lower_lower c x y) ; auto.
    exists q ; split ; auto.
  - destruct (r_upper_open c x H) as [y [[q [? ?]] ?]].
    exists q ; split ; auto.
    exists y ; auto.
  - destruct H as [q [[y [? ?]] G2]].
    apply (r_upper_upper c y x).
    + exists q ; auto.
    + assumption.
Qed.

