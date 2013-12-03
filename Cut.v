(** The definition of Dedekind cuts. *)

Require Import QArith QOrderedType.
Require Import Morphisms SetoidClass.
Require Import MiscLemmas.

(** A Dedekind cut is represented by the predicates [lower] and [upper]. *)
Structure R := {
  lower : Q -> Prop;
  upper : Q -> Prop;
  lower_proper : Proper (Qeq ==> iff) lower;
  upper_proper : Proper (Qeq ==> iff) upper;
  lower_bound : {q : Q | lower q};
  upper_bound : {r : Q | upper r};
  lower_lower : forall q r, q < r -> lower r -> lower q;
  lower_open : forall q, lower q -> exists r, q < r /\ lower r;
  upper_upper : forall q r, q < r -> upper q -> upper r;
  upper_open : forall r, upper r -> exists q,  q < r /\ upper q;
  disjoint : forall q, ~ (lower q /\ upper q);
  located : forall q r, q < r -> {lower q} + {upper r}
}.

Instance R_lower_proper (x : R) : Proper (Qeq ==> iff) (lower x) := lower_proper x.
Instance R_upper_proper (x : R) : Proper (Qeq ==> iff) (upper x) := upper_proper x.

(** Strict order. *)
Definition Rlt (x y : R) := exists q, upper x q /\ lower y q.

(** Non-strict order. *)
Definition Rle (x y : R) := forall q, lower x q -> lower y q.

(** Equality. *)
Definition Req (x y : R) :=
  (forall q, lower x q <-> lower y q) /\ (forall q, upper x q <-> upper y q).

(** Apartness. *)
Definition Rneq (x y : R) := Rlt x y \/ Rlt y x.

Infix "<=" := Rle : R_scope.
Infix "<" := Rlt : R_scope.
Infix "==" := Req : R_scope.
Infix "=/=" := Rneq (at level 70, no associativity) : R_scope.

Delimit Scope R_scope with R.

Instance Proper_Req : Equivalence Req.
Proof.
  unfold Req.
  split.
  - intros x ; tauto.
  - intros x y [H1 H2] ; split ; intro q.
    + split; apply H1.
    + split; apply H2.
  - intros x y z [G1 G2] [H1 H2].
    split ; intro q ;
    pose (H1' := H1 q) ; pose (H2' := H2 q) ;
    pose (G1' := G1 q) ; pose (G2' := G2 q) ;
    tauto.
Qed.

Instance Setoid_R : Setoid R := {| equiv := Req |}.

Instance Setoid_R_power (n : nat) : Setoid R^^n.
Proof.
  induction n.
  - exact Setoid_R.
  - exists (fun xs ys => fst xs == fst ys /\ snd xs == snd ys).
    split.
    + intros xs ; split ; reflexivity.
    + intros xs ys [H1 H2] ; split ; symmetry ; assumption.
    + intros xs ys zs [H1 H2] [G1 G2] ; split ;
      [ transitivity (fst ys) | transitivity (snd ys) ] ; assumption.
Defined.

(* A lower bound is smaller than an upper bound. *)
Lemma lower_below_upper (x : R) (q r : Q) : lower x q -> upper x r -> q < r.
Proof.
  intros Lq Ur.
  destruct (Q_dec q r) as [[E1 | E2] | E3].
  - assumption.
  - exfalso. apply (disjoint x r).
    auto using (lower_lower x r q).
  - exfalso. apply (disjoint x r).
    split; [idtac | assumption].
    rewrite <- E3; assumption.
Qed.

Local Open Scope Q_scope.

(** Injection of rational numbers into reals. *)
Definition Q_inject : Q -> R.
Proof.
  intro s.
  refine {| lower := (fun q => (q < s)) ; upper := (fun r => (s < r)) |}.
  - intros ? ? E. rewrite E. tauto.
  - intros ? ? E. rewrite E. tauto.
  - exists (s + (-1#1)) ; apply Qlt_minus_1.
  - exists (s + 1) ; apply Qlt_plus_1.
  - intros q r ? ? ; apply (Qlt_trans _ r); assumption.
  - intros q H.
    exists ((q + s) * (1#2)). split.
    + apply (Qmult_lt_r _ _ (2#1)); [reflexivity | idtac].
      apply (Qplus_lt_r _ _ (-q)).
      ring_simplify.
      exact H.
    + apply (Qmult_lt_r _ _ (2#1)); [reflexivity | idtac].
      apply (Qplus_lt_r _ _ (-s)).
      ring_simplify.
      exact H.
  - intros. apply (Qlt_trans _ q); assumption.
  - intros r H.
    exists ((s + r) * (1#2)). split.
    + apply (Qmult_lt_r _ _ (2#1)); [reflexivity | idtac].
      apply (Qplus_lt_r _ _ (-r)).
      ring_simplify.
      exact H.
    + apply (Qmult_lt_r _ _ (2#1)); [reflexivity | idtac].
      apply (Qplus_lt_r _ _ (-s)).
      ring_simplify.
      exact H.
  - intros q [H G].
    apply (Qlt_irrefl q).
    transitivity s; assumption.
  - intros q r H.
    destruct (Qlt_le_dec q s) as [G | G].
    + left; assumption.
    + right. apply (Qle_lt_trans _ q); assumption.
Defined.

Instance Q_inject_proper : Proper (Qeq ==> Req) Q_inject.
Proof.
  intros s t E.
  unfold Req, Rle.
  simpl; split; intro; rewrite E; tauto.
Qed.

Coercion Q_inject : Q >-> R.

(** Definition of common constants. *)
Definition Rzero : R := Q_inject 0.
Definition Zone : R := Q_inject 1.

Notation "0" := (Rzero) : R_scope.
Notation "1" := (Zone) : R_scope.

Local Open Scope R_scope.
