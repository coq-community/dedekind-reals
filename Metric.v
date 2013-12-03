(** A simple theory of metric spaces with rational metric. 
    We need this for multivariable Lipschitz functions. *)

Require Import Setoid SetoidClass.
Require Import QArith Qabs.
Require Import MiscLemmas.

Class Metric A := {
  distance : A -> A -> Q ;
  distance_symmetric : forall x y, (distance x y == distance y x)%Q ;
  distance_nonnegative : forall x y, (0 <= distance x y)%Q ;
  distance_diag : forall x, (distance x x == 0)%Q ;
  distance_triangle : forall x y z, (distance x z <= distance x y + distance y z)%Q
}.

Instance Metric_Setoid A `{Metric A} : Setoid A :=
  {| equiv := fun (x y : A) => (distance x y == 0)%Q |}.
Proof.
  split.
  - intros ? ; apply distance_diag.
  - intros x y ?.
    transitivity (distance x y) ; auto using distance_symmetric.
  - intros x y z G1 G2.
    apply Qle_antisym ; [ idtac | apply distance_nonnegative ].
    setoid_replace 0 with (distance x y + distance y z) ; [ apply distance_triangle | idtac ].
    rewrite G1 ; rewrite G2 ; reflexivity.
Defined.

Lemma distance_leq_0_eq_0 A `(Metric A) (x y : A) :
  distance x y <= 0 -> (distance x y == 0)%Q.
Proof.
  intro E.
  apply Qle_antisym ; [ assumption | apply distance_nonnegative ].
Qed.

Lemma distance_0_eq A `(Metric A) (x y z : A) :
  (distance x y == 0)%Q -> (distance x z == distance y z)%Q.
Proof.
  intro Dxy.
  apply Qle_antisym.
  - apply (Qle_trans _ (distance x y + distance y z)) ; [ apply distance_triangle | idtac ].
    rewrite Dxy ; ring_simplify ; apply Qle_refl.
  - apply (Qle_trans _ (distance y x + distance x z)) ; [ apply distance_triangle | idtac ].
    rewrite (distance_symmetric y x) ; rewrite Dxy ; ring_simplify ; apply Qle_refl.
Qed.

Instance instance_distance_proper A `(Metric A):
  Proper (equiv ==> equiv ==> Qeq) distance.
Proof.
  unfold equiv, Metric_Setoid.
  intros x y Exy u v Euv.
  transitivity (distance x v) ; [ idtac | (apply distance_0_eq ; assumption) ].
  setoid_rewrite distance_symmetric at 1 2.
  apply distance_0_eq ; assumption.
Qed.

Instance QMetric : Metric Q := {| distance := fun q r => Qabs (q - r) |}.
Proof.
  - intros q r ; rewrite (Qabs_Qminus q r) ; reflexivity.
  - auto using Qabs_nonneg.
  - intros q ; setoid_replace (q - q) with 0 ; [reflexivity | (ring_simplify ; reflexivity)].
  - intros q r s.
    setoid_replace (q - s) with ((q - r) + (r - s)).
    + apply Qabs_triangle.
    + ring.
Defined.

(*
Instance ProdSetoid A B `{Setoid A} `{Setoid B} : Setoid (A * B).
Proof.
  exists (fun u v => (fst u == fst v) /\ (snd u == snd v)).
  split.
  - intros ? ; split ; reflexivity.
  - intros ? ? [? ?] ; split ; symmetry ; assumption.
  - intros [a1 b1] [a2 b2] [a3 b3] [? ?] [? ?] ; simpl in * |- * ; split.
    + transitivity a2 ; assumption.
    + transitivity b2 ; assumption.
Defined.

Lemma decompose_equal_pair {A} {B} `{Setoid A} `{Setoid B} :
  forall (u v : prod A B),  u == v -> fst u == fst v /\ snd u == snd v.
Proof.
  intros [u1 u2] [v1 v2] [E1 E2] ; split ; assumption.
Defined.
*)

Instance ProductMetric A B `{Metric A} `{Metric B} : Metric (A * B) :=
  {| distance := fun u v => distance (fst u) (fst v) + distance (snd u) (snd v) |}.
Proof.
  - intros [a1 b1] [a2 b2]; simpl.
    rewrite (distance_symmetric a1 a2) ;
    rewrite (distance_symmetric b1 b2) ;
    reflexivity.
  - intros [a1 b1] [a2 b2]; simpl.
    apply Qplus_nonneg_cone ; apply distance_nonnegative.
  - intros [a1 b1] ; rewrite 2 distance_diag; reflexivity.
  - intros [a1 b1] [a2 b2] [a3 b3]; simpl.
    apply (Qle_trans _ (distance a1 a2 + distance a2 a3 + distance b1 b3) _).
    + apply Qplus_le_l. apply distance_triangle.
    + apply (Qplus_le_l _ _ (- distance a1 a2 - distance a2 a3)).
      ring_simplify.
      apply distance_triangle.
Defined.

Instance UnitMetric : Metric unit := {| distance := fun _ _ => 0 |}.
Proof.
  - reflexivity.
  - intros ? ? ; apply Qle_refl.
  - intros ; reflexivity.
  - intros ? ? ? ; discriminate.
Defined.

(*
Instance PowerSetoid (n : nat) (A : Type) `{E : Setoid A} : Setoid A^^n.
Proof.
  induction n.
  - exact E.
  - exists (fun (a b : A^^(S n)) => fst a == fst b /\ snd a == snd b).
    split.
    + intros [xs x] ; split ; reflexivity.
    + intros [xs x] [ys y] [Hx Hy] ; split ; symmetry ; assumption.
    + intros [xs x] [ys y] [zs z] [Hxys Hxy] [Hyzs Hyz] ;
      split ; [transitivity ys | transitivity y] ; assumption.
Defined.
*)

Instance PowerMetric (n : nat) (A : Type) `(MA : Metric A) : Metric A^^n.
Proof.
  induction n.
  - exact MA.
  - exists distance.
    + apply distance_symmetric.
    + apply distance_nonnegative.
    + apply distance_diag.
    + apply distance_triangle.
Defined.

