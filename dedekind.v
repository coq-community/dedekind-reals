(** An attempt to formalize Dedekind reals in Coq. *)

Require Import QArith.
Require Import QOrderedType.
Require Import Morphisms Setoid.

Section Missing_Lemmas.

  Lemma Qopp_lt_compat : forall (p q : Q), p < q <-> -q < -p.
  Proof.
    intros (a,b) (c,d).
    unfold Qlt. simpl.
    rewrite !Z.mul_opp_l. omega.
  Defined.

  Lemma Qplus_lt_lt_compat : forall (p q r s : Q), p < q -> r < s -> p + r < q + s.
  Proof.
    auto using Qlt_le_weak, Qplus_lt_le_compat.
  Qed.

  Lemma Qmult_lt_positive : forall (p q : Q), 0 < p -> 0 < q -> 0 < p * q.
  Proof.
    intros p q pPos qPos.
    rewrite <- (Qmult_0_l q) at 1.
    apply Qmult_lt_compat_r; assumption.
  Qed.

  Lemma Qopp_lt_shift_l : forall (p q : Q), -p < q <-> -q < p.
  Proof.
    intros p q; split; intro H.
    - rewrite <- (Qopp_involutive p).
      apply Qopp_lt_compat.
      rewrite 2 Qopp_involutive.
      assumption.
    - rewrite <- (Qopp_involutive q).
      apply Qopp_lt_compat.
      rewrite 2 Qopp_involutive.
      assumption.
  Qed.

  Lemma Qopp_lt_shift_r : forall (p q : Q), p < -q <-> q < -p.
  Proof.
    intros p q; split; intro H.
    - rewrite <- (Qopp_involutive p).
      apply Qopp_lt_compat.
      rewrite 2 Qopp_involutive.
      assumption.
    - rewrite <- (Qopp_involutive q).
      apply Qopp_lt_compat.
      rewrite 2 Qopp_involutive.
      assumption.
  Qed.

  Lemma Qlt_minus_1 : forall q : Q, q + (-1#1) < q.
  Proof.
    intro q.
    rewrite <- (Qplus_0_r q) at 2.
    apply Qplus_lt_r.
    compute; reflexivity.
  Qed.

  Lemma Qlt_plus_1 : forall q : Q, q < q + (1#1).
  Proof.
    intro q.
    rewrite <- (Qplus_0_r q) at 1.
    apply Qplus_lt_r.
    compute; reflexivity.
  Qed.

End Missing_Lemmas.

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

Local Open Scope Q_scope.

Definition Req : R -> R -> Prop :=
  fun x y => (forall q, lower x q <-> lower y q) /\ (forall q, upper x q <-> upper y q).

Instance Proper_Req : Equivalence Req.
Proof.
  unfold Req.
  split.
  - unfold Reflexive. tauto.
  - intros x y [H G]. split; intro q.
    + destruct (H q); tauto.
    + destruct (G q); tauto. 
  - intros x y z [H1 H2] [G1 G2]. split; intro q.
    + destruct (H1 q); destruct (G1 q); tauto.
    + destruct (H2 q); destruct (G2 q); tauto.
Qed.

Lemma lower_below_upper (x : R) (q r : Q) : lower x q -> upper x r -> q < r.
Proof.
  intros Lq Ur.
  destruct (Q_dec q r) as [[E | E] | E].
  - assumption.
  - exfalso. apply (disjoint x r).
    auto using (lower_lower x r q).
  - exfalso. apply (disjoint x r).
    split; [idtac | assumption].
    rewrite <- E; assumption.
Qed.    

Definition Q_inject : Q -> R.
Proof.
  intro s.
  refine {| lower := (fun q => (q < s)) ; upper := (fun r => (s < r)) |}.
  - intros ? ? E. rewrite E. tauto.
  - intros ? ? E. rewrite E. tauto.
  - exists (s + (-1#1)); apply Qlt_minus_1.
  - exists (s + 1). apply Qlt_plus_1.
  - intros. apply (Qlt_trans _ r); assumption.
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
    absurd (s < s).
    apply Qlt_irrefl.
    transitivity q; assumption.
  - intros q r H.
    destruct (Qlt_le_dec q s) as [G | G].
    + left; assumption.
    + right. apply (Qle_lt_trans _ q); assumption.
Defined.

Instance Q_inject_proper : Proper (Qeq ==> Req) Q_inject.
Proof.
  intros s t E.
  unfold Req.
  simpl; split; intro; rewrite E; tauto.
Qed.

Coercion Q_inject : Q >-> R.

Definition zero : R := Q_inject 0.
Definition one : R := Q_inject 1.

Notation "0" := (zero) : R_scope.
Notation "1" := (one) : R_scope.

Local Open Scope R_scope.

Definition Ropp (x : R) : R.
Proof.
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

Instance Ropp_proper : Proper (Req ==> Req) Ropp.
Proof.
  unfold Req.
  intros x y [H G].
  split; intro q; simpl.
  - apply G.
  - apply H.
Qed.

(* It would be extremely painful to define maps on R by hand all the time.
   So instead we prove a lemma that will allow us to cover most cases. *)

Section LipschitzFunctions.

Definition is_lipschitz (f : Q -> Q) (l : Q) :=
  forall q r : Q, q < r -> l * (q - r) < f r - f q /\ f r - f q < l * (r - q).

Lemma lipschitz_positive (f : Q -> Q) (l : Q) : is_lipschitz f l -> l > 0.
Proof.
  intro H.
  assert (G : 0 < 1) ; [(compute ; reflexivity) | idtac].
  destruct (H (0#1) (1#1) G) as [K1 K2].
  apply (Qmult_lt_r _ _ (2#1)); [(compute; reflexivity) | idtac].
  apply (Qplus_lt_l _ _ (-l)).
  ring_simplify.
  transitivity (f 1%Q - f 0%Q).
  - ring_simplify in K1; assumption.
  - ring_simplify in K2; assumption.
Qed.

Definition extend (f : Q -> Q) (l : Q) : is_lipschitz f l -> R -> R.
Proof.
  intros L x.
  refine {|
    lower := fun q => exists d u, lower x d /\ upper x u /\ q + l * (u - d) < f d ;
    upper := fun r => exists d u, lower x d /\ upper x u /\ f u < r + l * (d - u) 
  |}.
  - intros a b E. split.
    + intros [d [u [H1 [H2 H3]]]].
      exists d. exists u. rewrite <- E. auto.
    + intros [d [u [H1 [H2 H3]]]].
      exists d. exists u. rewrite E. auto.
  - intros a b E. split.
    + intros [d [u [H1 [H2 H3]]]].
      exists d. exists u. rewrite <- E. auto.
    + intros [d [u [H1 [H2 H3]]]].
      exists d. exists u. rewrite E. auto.
  - destruct (lower_bound x) as (dx, Ldx).
    destruct (upper_bound x) as (ux, Udx).
    exists (f dx - l * (ux - dx) - 1).
    exists dx; exists ux.
    split; [assumption | (split ; [assumption | idtac])].
    ring_simplify.
    apply Qlt_minus_1.
  - destruct (lower_bound x) as (dx, Ldx).
    destruct (upper_bound x) as (ux, Udx).
    exists (f ux - l * (dx - ux) + 1).
    exists dx; exists ux.
    split; [assumption | (split ; [assumption | idtac])].
    ring_simplify.
    apply Qlt_plus_1.
  - intros q r H [dx [ux [G1 [G2 G3]]]].
    exists dx; exists ux.
    split; [assumption | (split ; [assumption | idtac])].
    transitivity (r + l * (ux - dx)).
    + apply Qplus_lt_l; assumption.
    + assumption.
  - intros q [dx [ux [G1 [G2 G3]]]].
    exists ((q + f dx - l * (ux - dx)) * (1#2)).
    split.
    + apply (Qmult_lt_r _ _ (2#1)); [(compute; auto) | idtac].
      apply (Qplus_lt_r _ _ (-q + l * (ux - dx))).
      ring_simplify.
      ring_simplify in G3.
      assumption.
    + exists dx; exists ux.
      split; [assumption | (split ; [assumption | idtac])].
      apply (Qmult_lt_r _ _ (2#1)); [(compute; auto) | idtac].
      apply (Qplus_lt_r _ _ (- f dx)).
      ring_simplify.
      setoid_replace (-2#2) with (-1#1); [idtac | reflexivity].
      ring_simplify in G3.
      assumption.
  - intros q r H [dx [ux [G1 [G2 G3]]]].
    exists dx; exists ux.
    split; [assumption | (split ; [assumption | idtac])].
    transitivity (q + l * (dx - ux)).
    + assumption.
    + apply Qplus_lt_l; assumption.
  - intros q [dx [ux [G1 [G2 G3]]]].
    exists ((q + f ux - l * (dx - ux)) * (1#2)).
    split.
    + apply (Qmult_lt_r _ _ (2#1)); [(compute; auto) | idtac].
      apply (Qplus_lt_r _ _ (-q + l * (dx - ux))).
      ring_simplify.
      ring_simplify in G3.
      assumption.
    + exists dx; exists ux.
      split; [assumption | (split ; [assumption | idtac])].
      apply (Qmult_lt_r _ _ (2#1)); [(compute; auto) | idtac].
      apply (Qplus_lt_r _ _ (- f ux)).
      ring_simplify.
      setoid_replace (-2#2) with (-1#1); [idtac | reflexivity].
      ring_simplify in G3.
      assumption.
  - intros q [[dx [ux [H1 [H2 H3]]]] [ex [vx [G1 [G2 G3]]]]].
    absurd (ux < ex).
    + auto using Qle_not_lt, Qlt_le_weak, (lower_below_upper x).
    + apply (Qplus_lt_l _ _ (- ux)).
      apply (Qmult_lt_r _ _ l); [exact (lipschitz_positive f l L) | idtac].
      apply (Qplus_lt_l _ _ (l * (dx - vx))).
      transitivity (f vx - f dx).
      * destruct (L dx vx (lower_below_upper x dx vx H1 G2)) as [K _].
        ring_simplify in K; ring_simplify; assumption.
      * apply Qopp_lt_compat, (Qplus_lt_r _ _ (q + l * (ex - vx) + f vx)).
        ring_simplify.
        assert (J := Qplus_lt_lt_compat _ _ _ _ H3 G3).
        ring_simplify in J.
        assumption.
  - intros q r H.
    admit.
Defined.
      

End LipschitzFunctions.
