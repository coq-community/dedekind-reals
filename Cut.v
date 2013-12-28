(** The definition of Dedekind cuts. *)

Require Import QArith QOrderedType.
Require Import Morphisms SetoidClass.
Require Import MiscLemmas.

(** A Dedekind cut is represented by the predicates [lower] and [upper],
    satisfying a number of conditions. *)
Structure R := {
  (* The cuts are represented as propositional functions, rather than subsets,
     as there are no subsets in type theory. *)
  lower : Q -> Prop;
  upper : Q -> Prop;
  (* The cuts respect equality on Q. *)
  lower_proper : Proper (Qeq ==> iff) lower;
  upper_proper : Proper (Qeq ==> iff) upper;
  (* The cuts are inabited. *)
  lower_bound : {q : Q | lower q};
  upper_bound : {r : Q | upper r};
  (* The lower cut is a lower set. *)
  lower_lower : forall q r, q < r -> lower r -> lower q;
  (* The lower cut is open. *)
  lower_open : forall q, lower q -> exists r, q < r /\ lower r;
  (* The upper cut is an upper set. *)
  upper_upper : forall q r, q < r -> upper q -> upper r;
  (* The upper cut is open. *)
  upper_open : forall r, upper r -> exists q,  q < r /\ upper q;
  (* The cuts are disjoint. *)
  disjoint : forall q, ~ (lower q /\ upper q);
  (* There is no gap between the cuts. *)
  located : forall q r, q < r -> lower q \/ upper r
}.

(** Strict order. *)
Definition Rlt (x y : R) := exists q : Q, upper x q /\ lower y q.

(** Non-strict order. *)
Definition Rle (x y : R) := forall q, lower x q -> lower y q.

(** Non-strict order in terms of upper cuts, and a proof they are
    equivalent. *)

Definition Rle_upper (x y : R) := forall q, upper y q -> upper x q.

Lemma Rle_equiv (x y : R) : Rle x y <-> Rle_upper x y.
Proof.
  split.
  - intros ? q Uyq.
    destruct (upper_open y q Uyq) as [r [G ?]].
    destruct (located x _ _ G) ; auto.
    exfalso ; apply (disjoint y r) ; auto.
  - intros ? q Lxq.
    destruct (lower_open x q Lxq) as [r [G ?]].
    destruct (located y _ _ G) ; auto.
    exfalso ; apply (disjoint x r) ; auto.
Qed.

(** Equality. *)
Definition Req (x y : R) := Rle x y /\ Rle y x.

(** Equality in terms of upper cuts, and a proof they are equivalent. *)
Definition Req_upper (x y : R) := Rle_upper x y /\ Rle_upper y x.

Lemma Req_equiv (x y : R) : Req x y <-> Req_upper x y.
Proof.
  unfold Req, Req_upper.
  split ; intros [? ?] ; split ; apply Rle_equiv ; assumption.
Qed.

(** We explain to Coq how to derive automatically that [lower] and [upper].
    This way [lower] and [upper] will behave with respect to [setoid_rewrite]. *)
Instance R_lower_proper : Proper (Req ==> Qeq ==> iff) lower.
Proof.
  intros x y [Exy1 Exy2] q r Eqr ; split ; intro H.
  - apply Exy1, (lower_proper x q r) ; assumption.
  - apply Exy2, (lower_proper y q r) ; assumption.
Qed.

Instance R_upper_proper : Proper (Req ==> Qeq ==> iff) upper.
Proof.
  intros x y [Exy1 Exy2] q r Eqr.
  apply Rle_equiv in Exy1.
  apply Rle_equiv in Exy2.
  split ; intro H.
  - apply Exy2, (upper_proper x q r) ; assumption.
  - apply Exy1, (upper_proper y q r) ; assumption.
Qed.

(** Apartness. *)
Definition Rneq (x y : R) := (Rlt x y \/ Rlt y x)%type.

(** We introduce notation for equality, order and apartness. We put the notation
    in the scope [R_scope] which can then be opened whenever needed. *)
Infix "<=" := Rle : R_scope.
Infix "<" := Rlt : R_scope.
Infix "==" := Req : R_scope.
Infix "##" := Rneq (at level 70, no associativity) : R_scope.

(** This allows us to write [(....)%R] to indicate that notation in a given expression
    should be understood as taking place in R_scope. *)

Delimit Scope R_scope with R.

Local Open Scope R_scope.

(** Equality on R is an equivalence relation. *)
Instance Equivalence_Req : Equivalence Req.
Proof.
  split.
  - intros x ; split ; intro q ; tauto.
  - intros x y [H1 H2] ; split ; intro q.
    + apply H2.
    + apply H1.
  - intros x y z [G1 G2] [H1 H2].
    split ; intro q ;
    pose (H1' := H1 q) ; pose (H2' := H2 q) ;
    pose (G1' := G1 q) ; pose (G2' := G2 q) ;
    tauto.
Qed.

(** This defines Req as the default equality on R. *)
Instance Setoid_R : Setoid R := {| equiv := Req |}.

(** We also prove that < and <= respect equality. *)

Instance Rlt_proper : Proper (Req ==> Req ==> iff) Rlt.
Proof.
  intros x y Exy z w Ezw ; split ; intros [q [H1 H2]].
  - exists q ; split.
    + rewrite <- Exy ; assumption.
    + rewrite <- Ezw ; assumption.
  - exists q ; split.
    + rewrite -> Exy ; assumption.
    + rewrite -> Ezw ; assumption.
Qed.
  
(* A lower bound is smaller than an upper bound. *)
Lemma lower_below_upper (x : R) (q r : Q) : lower x q -> upper x r -> (q < r)%Q.
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

(* The lower cut is closed for [Rle]. *)
Lemma lower_le (x : R) (q r : Q) : lower x r -> (q <= r)%Q -> lower x q.
Proof.
  intros H G.
  destruct (proj1 (Qle_lteq q r) G) as [E|E].
  + apply (lower_lower x q r) ; assumption.
  + rewrite E ; assumption.
Qed.

(* The upper cust is closed for [Rle]. *)
Lemma upper_le (x : R) (q r : Q) : upper x q -> (q <= r)%Q -> upper x r.
Proof.
  intros H G.
  destruct (proj1 (Qle_lteq q r) G) as [E|E].
  + apply (upper_upper x q r) ; assumption.
  + rewrite <- E ; assumption.
Qed.

(** Injection of rational numbers into reals. *)
Definition R_of_Q : Q -> R.
Proof.
  intro s.
  refine {| lower := (fun q => (q < s)%Q) ; upper := (fun r => (s < r)%Q) |}.
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

(** The injection of Q into R respects equality. *)
Instance R_of_Q_proper : Proper (Qeq ==> Req) R_of_Q.
Proof.
  intros s t E.
  unfold Req, Rle.
  simpl; split; intro; rewrite E; tauto.
Qed.

(** We declare that [R_of_Q] can be used automatically to coerce
    rational numbers to real numbers. *)
Coercion R_of_Q : Q >-> R.

(** Definition of common constants. *)
Definition Rzero : R := R_of_Q 0.
Definition Zone : R := R_of_Q 1.

Notation "0" := (Rzero) : R_scope.
Notation "1" := (Zone) : R_scope.
