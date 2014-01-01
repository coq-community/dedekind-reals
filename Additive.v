(** The additive structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut.
Require Import Archimedean.

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
  - destruct (upper_bound x) as [q H].
    destruct (upper_bound y) as [r G].
    exists (q+r).
    destruct (upper_open x q H) as [q' [Lqq' H']].
    destruct (upper_open y r G) as [r' [Lrr' G']].
    exists q', r';split; auto.
    apply Qplus_lt_lt_compat ; assumption.
  - intros q r Lqr [r' [s' [H1 [H2 H3]]]].
    exists r', s' ; split ; auto.
    transitivity r ; assumption.
  - intros q [r [s [H1 [H2 H3]]]].
    exists ((q + r + s) * (1#2)) ; split.
    + apply (Qle_lt_trans q  ((q+q)*(1#2)) ((q + r + s) * (1 # 2))). 
      ring_simplify; apply Qle_refl.
      apply Qmult_lt_compat_r; [reflexivity | idtac].
       apply (Qplus_lt_r _ _ (-q)); ring_simplify; assumption.
    + exists r, s ; split ; auto.
      setoid_replace (r+s) with ((r+s+r+s)*(1#2)).
      apply Qmult_lt_compat_r. reflexivity.
      destruct (Qplus_lt_l q (r+s) (r+s)) .
      setoid_replace (q+r+s) with (q+(r+s)); [idtac | ring]. 
      setoid_replace (r+s+r+s) with (r+s+(r+s)); [auto | ring].
      ring_simplify; ring. 
  - intros q r Lqr [r' [s' [H1 [H2 H3]]]].
    exists r', s'; split; auto.
    transitivity q; assumption.
  - intros q [r [s [H1 [H2 H3]]]].
    exists ((q + r + s) * (1#2)) ; split.
    +apply (Qlt_le_trans ((q + r + s) * (1 # 2)) ((q+q)*(1#2)) q). 
     apply Qmult_lt_compat_r; [reflexivity | idtac].
     destruct (Qplus_lt_r (r+s) q q).
     setoid_replace (q+r+s) with (q+(r+s)); [apply H0;assumption|idtac].
     ring_simplify; apply Qeq_refl.
     ring_simplify; apply Qle_refl.
    + exists r, s ; split ; auto.
      setoid_replace (r+s) with ((r+s+r+s)*(1#2)); [idtac|ring].
      apply Qmult_lt_compat_r; [reflexivity | idtac].
      destruct (Qplus_lt_l (r+s) q (r+s)) .
      apply (Qplus_lt_r _ _ (-r-s)); ring_simplify; assumption.
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
  - intros q [s [r [G1 [[s' [r' [K1 [K2 K3]]]] G3]]]].
    exists s', (r + r')%Q ; split.
    + rewrite (Qplus_comm r r').
      rewrite (Qplus_assoc s' r' r).
      rewrite G1.
      apply Qplus_lt_l.
      assumption.
    + split ; auto.
      destruct (lower_open z r) as [t [H1 H2]]. assumption. 
      exists r', t; split; auto.
      rewrite (Qplus_comm r r').
      apply Qplus_lt_r; auto.
  - intros q [x' [yz' [H [Hx [y' [z' [H1 [Hy Hz]]]]]]]].
    exists (x' + y')%Q, z' ; split.
    + transitivity (x' + yz')%Q ; auto.
      apply (Qplus_lt_r _ _ (-x')); ring_simplify; assumption. 
    + split ; auto.
      destruct (lower_open x x') as [t [G1 G2]] ; auto.
      exists t, y'; split; auto.
      apply Qplus_lt_l; auto.
Qed.

Lemma Rplus_comm (x y : R) : x + y == y + x.
Proof.
  split ; intros q [r [s [G1 [G2 G3]]]] ; exists s, r ; split ; auto ;
  setoid_rewrite (Qplus_comm s r) ; assumption.
Qed.

Lemma Rplus_0_l (x : R) : 0 + x == x.
Proof.
  split ; intros q.
  - intros [r [s [H1 [H2 H3]]]].
    apply (lower_lower x q s) ; auto.
    transitivity (r+s)%Q;auto.
    apply (Qplus_lt_r _ _ (-s)); ring_simplify.
    apply H2.
  - intro H.
    destruct (lower_open x q H) as [r [G1 G2]].
    exists ((q - r) * (1#2))%Q, r ; split.
    + setoid_replace ((q - r) * (1 # 2) + r)%Q with ((q + r) * (1 # 2));[idtac|ring].
      apply (Qle_lt_trans q ((q+q)*(1#2))_); [ring_simplify; apply Qle_refl| idtac ].
      apply Qmult_lt_compat_r; [reflexivity | idtac].
      apply Qplus_lt_r; assumption.
    + split ; auto.
      cut ((q - r) * (1#2)<0)%Q;auto.
      apply (Qplus_lt_r _ _ (r*(1#2))); ring_simplify.
      setoid_replace ((1#2)*q) with (q*(1#2)); [idtac|ring].
      setoid_replace ((1#2)*r) with (r*(1#2)); [idtac|ring].
      apply Qmult_lt_compat_r; [reflexivity| assumption].
Qed.

Lemma Rplus_0_r (x : R) : x + 0 == x.
Proof.
  setoid_rewrite Rplus_comm.
  apply Rplus_0_l.
Qed.

(** Properties of opposite. *)

Lemma Ropp_involutive (x : R) : - (- x) == x.
Proof.
  split ; intros q H ; simpl in * |- * ;
  rewrite Qopp_opp in * |- * ; assumption.
Qed.

Lemma Rpluss_opp_r (x : R) : x + (- x) == 0.
Proof.
  split ; intros q H.
   - destruct H as [r [s [G1 [G2 G3]]]].
     apply (lower_lower 0 q (r + s)); auto.
     apply (Qplus_lt_r _ _ (-s)); ring_simplify.
     apply (lower_below_upper x); [assumption|auto].
  - assert (-q>0)%Q; [apply (Qplus_lt_r _ _ q) ;ring_simplify; auto | idtac].  
    destruct (archimedean x (existT _ (-q)%Q H0)) as [a [b [A [B C]]]]. 
    exists a, (-b)%Q; split; [idtac | split; auto].
    apply (Qplus_lt_r _ _ (b-a-q)%Q) ;ring_simplify; auto.
    cut (upper x (--b)); [auto | rewrite Qopp_involutive; auto].
Qed.

Lemma Rplus_opp_l (x : R) : (- x) + x == 0.
Proof.
  rewrite Rplus_comm.
  apply Rpluss_opp_r.
Qed.
