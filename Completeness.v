(* Dedekind completeness: any cut of real numbers determines a real.
   In other words, if we perform the Dedekind construction on R we just
   get R back. *)

Require Import Morphisms Setoid SetoidClass.
Require Import QArith.
Require Import Cut.

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
  - admit.
  - admit.
  - admit.
Defined.

(* Every real determines a real cut. *)
Definition RCut_of_R : R -> RCut.
Proof.
  intro x.
  refine {| r_lower := (fun y => y < x) ; r_upper := (fun z => x < z) |}.
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