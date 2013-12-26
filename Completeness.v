
(* Dedekind completeness: any cut of real numbers determines a real.
   In other words, if we perform the Dedekind construction on R we just
   get R back. 
*)

Require Import Morphisms Setoid SetoidClass.
Require Import QArith.
Require Import Cut Order.

Local Open Scope R_scope.

Structure RCut := {
  r_lower : R -> Prop;
  r_upper : R -> Prop;
  r_lower_proper : Proper (Req ==> iff) r_lower;
  r_upper_proper : Proper (Req ==> iff) r_upper;
  r_lower_bound : {x : R | r_lower x};
  r_upper_bound : {x : R | r_upper x};
  r_lower_lower : forall x y, x < y -> r_lower y -> r_lower x;
  r_lower_open : forall x, r_lower x -> exists y, x < y /\ r_lower y;
  r_upper_upper : forall x y, x < y -> r_upper x -> r_upper y;
  r_upper_open : forall y, r_upper y -> exists x,  x < y /\ r_upper x;
  r_disjoint : forall x, ~ (r_lower x /\ r_upper x);
  r_located : forall x y, x < y -> r_lower x \/ r_upper y
}.

Definition RCut_eq (c d : RCut) :=
  (forall x, r_lower c x <-> r_lower d x) /\ (forall x, r_upper c x <-> r_upper d x).

Instance RCut_Setoid : Setoid RCut := {| equiv := RCut_eq |}.
Proof.
  split.
  - intro.
    unfold RCut_eq.
    split ; intro ; tauto.
  - intro.
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
  - intro.
    intros y z A B.
    destruct A as [A1 A2].
    destruct B as [B1 B2].
    unfold RCut_eq.
    split.
    + intro.
      eauto using iff_trans.
    + intro.
      eauto using iff_trans.
Defined.

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

Definition R_of_RCut : RCut -> R.
Proof.
  intro c.
  refine {| lower := (fun q => exists x, r_lower c x /\ lower x q) ;
            upper := (fun q => exists y, r_upper c y /\ upper y q)
         |}.
  - intro.
    intros.
    split.
    + intro.
      destruct H0.
      exists x0.
      rewrite H in H0.
      assumption.
    + intro.
      destruct H0.
      exists x0.
      assert (H1:=Qeq_sym x y H).
      rewrite H1 in H0.
      assumption.
  - intro.
    intros.
    split.
    + intro.
      destruct H0.
      exists x0.
      rewrite H in H0.
      assumption.
    + intro.
      destruct H0.
      exists x0.
      assert (H1:=Qeq_sym x y H).
      rewrite H1 in H0.
      assumption.
  - destruct (r_lower_bound c) as [x H].
    destruct (lower_bound x) as [q P].
    exists q, x ; auto.
  - destruct (r_upper_bound c) as [x H].
    destruct (upper_bound x) as [q P].
    exists q, x ; auto.
  - intros q r A [x[C D]].
    exists x.
    split.
    + assumption.
    + assert (J:=(lower_lower x q r A D)).
      assumption.
  - intros q [x[C D]].
    assert(E:=(lower_open x q D)).
    destruct E as [r [F G]].
    exists r.
    split.
    + assumption.
    + exists x.
      split ; assumption.
  - intros q r A [x[C D]].
    exists x.
    split.
    + assumption.
    + assert (J:=(upper_upper x q r A D)).
      assumption.
  - intros r [y[C D]].
    assert(E:=(upper_open y r D)).
    destruct E as [q [F G]].
    exists q.
    split.
    + assumption.
    + exists y.
      split ; assumption.
  - intro.
    apply neg_false.
    split.
    + intros [ [x[X1 X2]] [y[Y1 Y2]] ].
      admit.
    + intro.
      tauto.
  - intros q r H.
    admit.
Defined.

Theorem dedekind_complete :
  forall c : RCut, (c == RCut_of_R (R_of_RCut c))%type.
Proof.
  intro c.
  split ; intro x ; split ; intro H.
  - destruct (r_lower_open c x H) as [y [[q [? ?]] ?]].
    exists q ; split ; auto.
    exists y ; auto.
  - destruct H as [q [? [y [? ?]]]].
    apply (r_lower_lower c x y) ; auto.
    exists q ; split ; auto.
  - admit.
  - admit.
Qed.