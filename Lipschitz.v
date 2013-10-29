(* It would be extremely painful to define maps on R by hand all the time.
   So instead we prove a lemma that will allow us to cover most cases. *)

Require Import QArith.
Require Import Cut.
Require Import MiscLemmas.

Local Open Scope Q_scope.

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

