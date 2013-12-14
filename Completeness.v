(* Dedekind completeness: any cut of real numbers determines a real.
   In other words, if we perform the Dedekind construction on R we just
   get R back. *)

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
  r_located : forall x y, x < y -> {r_lower x} + {r_upper y}
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
  - intro.
    intros.
    split.
    + intro.
      rewrite H in H0.
      assumption.
    + intro.
      rewrite H.
      assumption.
  - intro.
    intros.
    split.
    + intro.
      rewrite H in H0.
      assumption.
    + intro.
      rewrite H.
      assumption.
  - assert(H:=(lower_bound x)).
    firstorder.
    unfold Rlt.
    exists x0.
    assert (M:=(lower_open x x0 p)).
    destruct M as [m [M1 M2]].
    exists m.
    split.
    + auto using M1.
    + assumption.
  - assert(H:=(upper_bound x)).
    firstorder.
    unfold Rlt.
    exists x0.
    assert (M:=(upper_open x x0 p)).
    destruct M as [m [M1 M2]].
    exists m.
    split.
    + auto using M1.
    + assumption.
  - intros a b A B.
    apply (Rlt_trans a b x A B).
  - intros z [q [A B]].
    unfold Rlt.
    exists q.
    split.
    + destruct (upper_open z q A) as [r [S T]].
      exists r.
      split.
      * assumption.
      * auto using S.
    + destruct (lower_open x q B) as [r [S T]].
      exists r.
      split.
      * assumption.
      * auto using S.
  - intros a b A B.
    apply (Rlt_trans x a b B A).
  - intros y [q [H K]].
    exists q.
    unfold Rlt.
    split.
    + destruct (lower_open y q K) as [r [S T]].
      exists r.
      split.
      * auto using S.
      * assumption.
    + destruct (upper_open x q H) as [r [S T]].
      exists r.
      split.
      * auto using S.
      * assumption.
  - intro.
    apply neg_false.
    unfold Rlt.
    split.
    + intros [[q [P1 P2]] [r [S1 S2]]].
      assert (H:=(lower_below_upper x q r P2 S1)).
      assert (H1:=(lower_lower x0 q r H S2)).
      auto using (disjoint x0 q).
    + intro.
      tauto.
  - intros z y H.
assert (H1:=(Rlt_linear z y x H)).
admit.
Defined.


Definition R_of_RCut : RCut -> R.
Proof.
  intro c.
  refine {| lower := (fun q => exists x, r_lower c x /\ lower x q) ;
            upper := (fun q => exists y, r_upper c y /\ upper y q)
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

Theorem dedekind_complete :
  forall c : RCut, (c == RCut_of_R (R_of_RCut c))%type.
Proof.
  intro c.
  split ; intro x ; split ; intro H.
  - admit.
  - admit.
  - admit.
  - admit.
Qed.