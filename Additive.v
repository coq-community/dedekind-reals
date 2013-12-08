(** The additive structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut.

Local Open Scope Q_scope.

(** Addition. *)
Definition Rplus : R -> R -> R.
Proof.
  intros x y.
  refine {|
      lower := (fun q => exists r s, q < r + s /\ lower x r /\ lower y s) ;
      upper := (fun q => exists r s, r + s < q /\ upper x r /\ upper y s)
    |}.
  - intros u v Euv.
    split ; intros [r [s [H1 [H2 H3]]]] ; exists r, s ; split ; auto.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite Euv ; assumption.
  - intros u v Euv.
    split ; intros [r [s [H1 [H2 H3]]]] ; exists r, s ; split ; auto.
    + setoid_rewrite <- Euv ; assumption.
    + setoid_rewrite Euv ; assumption.
  - destruct (lower_bound x) as [q H].
    destruct (lower_bound y) as [r G].
    exists (q + r).
    destruct (lower_open x q H) as [q' [Lqq' H']].
    destruct (lower_open y r G) as [r' [Lrr' G']].
    exists q', r' ; split ; auto.
    apply Qplus_lt_lt_compat ; assumption.
  - admit. (* similar to previous case *)
  - intros q r Lqr [r' [s' [H1 [H2 H3]]]].
    exists r', s' ; split ; auto.
    transitivity r ; assumption.
  - intros q [r [s [H1 [H2 H3]]]].
    exists ((q + r + s) * (1#2)) ; split.
    + admit.
    + exists r, s ; split ; auto.
      admit.
  (* the next two cases are similar to the previous two cases. *)
  - admit.
  - admit.
  - intros q [[r [s [H1 [H2 H3]]]] [r' [s' [G1 [G2 G3]]]]].
    apply (Qlt_irrefl q).
    transitivity (r + s) ; auto.
    transitivity (r' + s') ; auto.
    apply Qplus_lt_lt_compat ; [apply (lower_below_upper x) | apply (lower_below_upper y) ] ; auto.
  - intros q r Lqr.
    admit.
Defined.

(** Opposite value. *)
Definition Ropp : R -> R.
Proof.
  intro x.
  refine {| lower := (fun q => upper x (-q)); upper := (fun r => lower x (-r)) |}.
  - intros ? ? H. rewrite H; tauto.
  - intros ? ? H. rewrite H; tauto.
  - destruct (upper_bound x) as [r H].
    exists (- r).
    rewrite (Qopp_involutive r); assumption.
  - destruct (lower_bound x) as [q H].
    exists (- q).
    rewrite (Qopp_involutive q); assumption.
  - intros q r H G.
    apply (upper_upper _ (- r) _); [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (upper_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_r; assumption.
    rewrite Qopp_involutive; assumption.
  - intros q r H G.
    apply (lower_lower _ _ (- q)) ; [idtac | assumption].
    apply Qopp_lt_compat.
    rewrite 2 Qopp_involutive; assumption.
  - intros q H.
    destruct (lower_open x (-q)) as [s [G1 G2]]; [assumption | idtac].
    exists (-s); split.
    apply Qopp_lt_shift_l; assumption.
    rewrite Qopp_involutive; assumption.
  - intros q.
    assert (H := disjoint x (- q)).
    tauto.
  - intros q r H.
    destruct (located x (-r) (-q)).
    + apply Qopp_lt_compat; rewrite 2 Qopp_involutive; assumption.
    + right; assumption.
    + left; assumption.
Defined.

Definition Rminus x y := Rplus x (Ropp y).

(** Notation for the ring structure. *)

Infix "+" := Rplus : R_scope.
Notation "- x" := (Ropp x) : R_scope.
Infix "-" := Rminus : R_scope.

(** The arithmetical operations are proper with respect to equality. *)

Instance Rplus_comp : Proper (Req ==> Req ==> Req) Rplus.
Admitted.

Instance Ropp_comp : Proper (Req ==> Req) Ropp.
Admitted.

Local Open Scope R_scope.


(** Properties of addition. *)

Lemma Rplus_assoc (x y z : R) : (x + y) + z == x + (y + z).
Proof.
  split.
  - intro q ; split ; intro H.
    + destruct H as [s [r [G1 [[s' [r' [K1 [K2 K3]]]] G3]]]].
      exists s', (r + r')%Q ; split.
      * assert(B:=Qplus_assoc s' r' r).
        assert(C:=(Qplus_comm r r')).
        rewrite C.
        rewrite B.
        rewrite G1.
        apply Qplus_lt_l.
        assumption.
      * split.
        assumption.
        admit.
    + admit.
  - intro q ; split ; intro H.
    + admit.
    + admit.
Qed.

Lemma Rplus_comm (x y : R) : x + y == y + x.
Proof.
  split ; intro q ; split ; intros [r [s [G1 [G2 G3]]]] ; exists s, r ; split ; auto ;
  setoid_rewrite (Qplus_comm s r) ; assumption.
Qed.

Lemma Rplus_0_l (x : R) : 0 + x == x.
Proof.
  split ; intro q ; split.
  - intros [r [s [H1 [H2 H3]]]].
    apply (lower_lower x q s) ; auto.
    admit. (* use the fact that r < 0 *)
  - intro H.
    destruct (lower_open x q H) as [r [G1 G2]].
    exists ((q - r) * (1#2))%Q, r ; split.
    + admit.
    + split ; auto.
      admit. (* This just says (q - r) * (1#2) < 0 *)
  - admit.
  - admit.
Qed.

Lemma Rplus_0_r (x : R) : x + 0 == x.
Admitted.

(** Properties of opposite. *)

Lemma Ropp_involutive (x : R) : - (- x) == x.
Proof.
  split ; intro q ; split ; intro H ; simpl in * |- * ;
  rewrite Qopp_opp in * |- * ; assumption.
Qed.

Lemma Rpluss_opp_r (x : R) : x + (- x) == 0.
Proof.
  split ; intro q ; split ; intro H.
   - destruct H as [r [s [G1 [G2 G3]]]].
     apply (lower_lower 0 q (r + s)); auto.
     admit.
  - admit.
  - admit.
  - admit.
Qed.

Lemma Rplus_opp_l (x : R) : (- x) + x == 0.
Proof.
  admit. (* Use Rplus_comm here. *)
Qed.
