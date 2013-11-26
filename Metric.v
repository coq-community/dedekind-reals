(** A simple theory of metric spaces with rational metric. 
    We need this for multivariable Lipschitz functions. *)

Require Import Setoid SetoidClass.
Require Import QArith Qabs.
Require Import MiscLemmas.

Class Metric A `{Setoid A} := {
  distance :> A -> A -> Q ;
  distance_proper : Proper (equiv ==> equiv ==> Qeq) distance ;
  distance_symmetric : forall x y, (distance x y == distance y x)%Q ;
  distance_nonnegative : forall x y, (0 <= distance x y)%Q ;
  distance_diag : forall x, (distance x x == 0)%Q ;
  distance_zero : forall x y, (distance x y == 0)%Q -> x == y ;
  distance_triangle : forall x y z, (distance x z <= distance x y + distance y z)%Q
}.

Instance instance_distance_proper A `(Setoid A) `(Metric A):
  Proper (equiv ==> equiv ==> Qeq) distance := distance_proper.

Instance Q_Qeq_Setoid : Setoid Q := {| equiv := Qeq ; setoid_equiv := Q_Setoid |}.

Instance QMetric : Metric Q.
Proof.
  refine {| distance := fun q r => Qabs (q - r) |}.
  - intros q r Eqr s t Est.
    rewrite Eqr; rewrite Est ; reflexivity.
  - intros q r ; rewrite (Qabs_Qminus q r) ; reflexivity.
  - auto using Qabs_nonneg.
  - intros q ; setoid_replace (q - q) with 0 ; [reflexivity | (ring_simplify ; reflexivity)].
  - intros q r H.
    apply (Qplus_inj_r _ _ (-r)).
    ring_simplify. apply Qabs_eq_0; assumption.
  - intros q r s.
    setoid_replace (q - s) with ((q - r) + (r - s)).
    + apply Qabs_triangle.
    + ring.
Defined.

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

Instance ProductMetric A B `{Metric A} `{Metric B} :
  Metric (A * B).
Proof.
  exists (fun u v => distance (fst u) (fst v) + distance (snd u) (snd v)).
  - intros [a1 b1] [a2 b2] E12 [a3 b3] [a4 b4] E34 ; simpl.
    destruct (decompose_equal_pair _ _ E12) as [E1 E2].
    destruct (decompose_equal_pair _ _ E34) as [E3 E4].
    simpl in * |- *.
    rewrite E1 ; rewrite E2 ; rewrite E3; rewrite E4 ; reflexivity.    
  - intros [a1 b1] [a2 b2]; simpl.
    rewrite (distance_symmetric a1 a2) ;
    rewrite (distance_symmetric b1 b2) ;
    reflexivity.
  - intros [a1 b1] [a2 b2]; simpl.
    apply Qplus_nonneg_cone ; apply distance_nonnegative.
  - intros [a1 b1] ; rewrite 2 distance_diag; reflexivity.
  - intros [a1 b1] [a2 b2] G ; split.
    + apply distance_zero, (Qplus_zero_nonneg _ (distance b1 b2)) ;
      try (apply distance_nonnegative) ; try assumption.
    + apply distance_zero, (Qplus_zero_nonneg (distance a1 a2) _) ;
      try (apply distance_nonnegative) ; try assumption.
  - intros [a1 b1] [a2 b2] [a3 b3]; simpl.
    apply (Qle_trans _ (distance a1 a2 + distance a2 a3 + distance b1 b3) _).
    + apply Qplus_le_l. apply distance_triangle.
    + apply (Qplus_le_l _ _ (- distance a1 a2 - distance a2 a3)).
      ring_simplify.
      apply distance_triangle.
Defined.

Instance UnitSetoid : Setoid unit.
Proof.
  exists (fun _ _ => True) ; split ; auto.
Defined.

Instance UnitMetric : Metric unit.
Proof.
  exists (fun _ _ => 0).
  - intros ? ? _ ? ? _ ; reflexivity.
  - reflexivity.
  - intros ? ? ; apply Qle_refl.
  - intros ; reflexivity.
  - intros ? ? _ ; exact I.
  - intros ? ? ? ; discriminate.
Defined.

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

Instance PowerMetric (n : nat) (A : Type) `{MA : Metric A} : Metric A^^n.
Proof.
  induction n.
  - exact MA.
  - exists distance.
    + intros ? ? ? ? ? ?. apply distance_proper ; assumption.
    + apply distance_symmetric.
    + apply distance_nonnegative.
    + apply distance_diag.
    + apply @distance_zero.
    + apply distance_triangle.
Defined.
