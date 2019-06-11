(* The Archimedean axiom.

   Let q be a positive rational number. Say that p pair of rationals (l, u) "straddle a
   real x with gap q" if l < x < u and u - l < q.

   The Archimdean axiom is equivalent to the statement that for every x and positive q we
   can find a straddling pair (u, l). In other words, this means we cna find arbitrarily
   good lower and upper rational approximations to x. *)

Require Import QArith.
Require Import MiscLemmas.
Require Import Cut.

Local Open Scope Q_scope.

(** A hack to be able to have proof-relevant unfinished constructions.
    When this file is cleaned up, remove this axiom and the tactic. *)
Axiom unfinished : forall (A : Type), A.
Ltac todo := apply unfinished.

Definition straddle (x : R) (q : Q) :=
  exists l u : Q, lower x l /\ upper x u /\ u - l < q.

Lemma straddle_monotone (x : R) (q r : Q) (G : q < r) :
  straddle x q -> straddle x r.
Proof.
  intros [l [u [? [? ?]]]].
  exists l, u ; repeat split ; auto.
  transitivity q ; auto.
Qed.

Lemma two_thirds_positive (q : Q) :
  0 < q -> 0 < (2#3) * q.
Proof.
  intro H.
  apply Qmult_lt_positive.
  - reflexivity.
  - assumption.
Qed.

Lemma two_thirds_pow_positive (n : nat) (q : Q) :
  0 < q -> 0 < ((2#3)^(Z.of_nat n) * q).
Proof.
  intro H.
  apply Qmult_lt_positive ; [idtac | (destruct q ; assumption)].
  apply Qpower_strictly_pos; reflexivity.
Defined.

Lemma trisect (x : R) (q : Q) :
  straddle x q -> straddle x ((2#3) * q).
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
      simpl ; ring_simplify.
      setoid_replace (-6 # 6) with (-1#1) ; [idtac | reflexivity].
      assumption.
    + exists l, (((2#1) * u + l) * (1#3)).
      split ; [assumption | split ; [assumption | idtac]].
      apply (Qmult_lt_r _ _ (3#2)) ; [reflexivity | idtac].
      simpl; ring_simplify.
      setoid_replace (-6 # 6) with (-1#1) ; [idtac | reflexivity].
      assumption.
Defined.

Lemma trisect_pow (x : R) (q : Q) (n : nat) :
  straddle x q -> straddle x ((2#3)^(Z.of_nat n) * q).
Proof.
  induction n.
  - intros [l [u [? [? ?]]]].
    exists l, u ; repeat split ; auto.
    simpl ; ring_simplify ; assumption.
  - intro.
    cut (straddle x ((2#3) * ((2#3)^Z.of_nat n * q))).
    + todo.
    + auto using trisect.
Defined.

Lemma two_thirds_power_small (q r : Q) :
  0 < q -> 0 < r -> { n : nat | (2#3)^(Z_of_nat n) * q < r }.
Proof.
  todo.
Defined.

Lemma archimedean (x : R) (q : Q) : 0 < q -> straddle x q.
Proof.
  intro.
  destruct (lower_bound x) as [l Hl].
  destruct (upper_bound x) as [u Hu].
  assert (G : 0 < (2#1) * (u - l)).
  - apply (Qmult_lt_r _ _ (1#2)) ; [reflexivity | idtac].
    apply (Qplus_lt_r _ _ l) ; ring_simplify ; auto using (lower_below_upper x).
  - destruct (two_thirds_power_small ((2#1) * (u - l)) q G H) as [n K].
    apply (straddle_monotone _ _ _ K).
    apply trisect_pow.
    exists l, u ; repeat split ; auto.
    apply (Qplus_lt_r _ _ (l + l - u)) ; ring_simplify.
    apply (lower_below_upper x) ; auto.
Qed.
