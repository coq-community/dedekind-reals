
Require Import QArith.
Require Import MiscLemmas.
Require Import Cut.

Local Open Scope Q_scope.

Definition straddle (x : R) (q : Qpositive) :=
  { l : Q &  { u : Q & lower x l /\ upper x u /\ u - l < q } }.

Definition two_thirds (q : Qpositive) : Qpositive.
Proof.
  exists ((2#3) * q).
  apply Qmult_lt_positive.
  - reflexivity.
  - destruct q; assumption.
Defined.

Definition two_thirds_pow (n : nat) (q : Qpositive) : Qpositive.
Proof.
  exists ((2#3)^(Z_of_nat n) * q).
  apply Qmult_lt_positive ; [idtac | (destruct q ; assumption)].
  apply Qpower_strictly_pos; reflexivity.
Defined.

Lemma trisect (x : R) (q : Qpositive) :
  straddle x q -> straddle x (two_thirds q).
Proof.
  intros [l [u [L [U H]]]].
  assert (G : ((2#1) * l + u) * (1#3) < ((2#1) * u + l) * (1#3)).
  - apply (Qmult_lt_r _ _ (1#3)); [reflexivity | idtac].
    apply (Qplus_lt_l _ _ (-l - u)).
    ring_simplify.
    apply (lower_below_upper x); assumption.
  - destruct (located x _ _ G) as [A | B].
    + exists (((2#1) * l + u) * (1#3)), u.
      split ; [assumption | split ; [assumption | idtac]].
      apply (Qmult_lt_r _ _ (3#2)) ; [reflexivity | idtac].
      simpl; ring_simplify.
      setoid_replace (-6 # 6) with (-1#1); [assumption | reflexivity].
    + exists l, (((2#1) * u + l) * (1#3)).
      split ; [assumption | split ; [assumption | idtac]].
      apply (Qmult_lt_r _ _ (3#2)) ; [reflexivity | idtac].
      simpl; ring_simplify.
      setoid_replace (-6 # 6) with (-1#1) ; [assumption | reflexivity].
Defined.

Lemma two_third_power_small :
  forall q : Qpositive, { n : nat | (2#3)^(Z_of_nat n) < q }.
Admitted.

Lemma archimedean (x : R) (q : Qpositive) : straddle x q.
Proof.
  destruct (lower_bound x) as [l Hl].
  destruct (upper_bound x) as [u Hu].
  assert (H : q / (u - l) > 0).
  - apply Qlt_shift_div_l.
    + apply (Qplus_lt_r _ _ l); ring_simplify.
      apply (lower_below_upper x); assumption.
    + ring_simplify. exact (projT2 q).
  - pose (r := existT _ (q / (u - l)) H : Qpositive).
    destruct (two_third_power_small r) as [n G].
    induction n.
    + exists l, u.
      split ; [assumption | split ; [assumption | idtac]].
      apply (Qmult_lt_r _ _ (/ (u - l))).
      * apply Qinv_lt_0_compat.
        apply (Qplus_lt_l _ _ l); ring_simplify.
        apply (lower_below_upper x); assumption.
      * setoid_rewrite (Qmult_inv_r (u - l)) ; [(simpl in G ; assumption) | idtac].
        apply Qnot_eq_sym, Qlt_not_eq.
        apply (Qplus_lt_r _ _ l); ring_simplify.
        apply (lower_below_upper x); assumption.
    + admit.
Qed.

