(** A simple theory of metric spaces with rational metric. 
    We need this for multivariable Lipschitz functions. *)

Require Import SetoidClass.
Require Import QArith Qabs.
Require Import MiscLemmas.

Class RationalMetric A `{Setoid A} := {
  distance :> A -> A -> Q ;
  distance_symmetric : forall x y, (distance x y == distance y x)%Q ;
  distance_nonnegative : forall x y, (0 <= distance x y)%Q ;
  distance_zero : forall x y, (distance x y == 0)%Q -> x == y ;
  distance_triangle : forall x y z, (distance x z <= distance x y + distance y z)%Q
}.

Instance Q_Qeq_Setoid : Setoid Q := {| equiv := Qeq ; setoid_equiv := Q_Setoid |}.

Instance QMetric : RationalMetric Q.
Proof.
  exists (fun q r => Qabs (q - r)).
  - intros q r ; rewrite (Qabs_Qminus q r) ; reflexivity.
  - intros q r ; apply Qabs_nonneg.
  - intros q r H.
    admit.
  - intros q r s.
    setoid_replace (q - s) with ((q - r) + (r - s)).
    + apply Qabs_triangle.
    + ring.
Defined.

Instance ProdSetoid A B `{Setoid A} `{Setoid B} : Setoid (prod A B).
Proof.
  exists (fun u v => (fst u == fst v) /\ (snd u == snd v)).
  split.
  - intros ? ; split ; reflexivity.
  - intros ? ? [? ?] ; split ; symmetry ; assumption.
  - intros [a1 b1] [a2 b2] [a3 b3] [? ?] [? ?] ; simpl in * |- * ; split.
    + transitivity a2 ; assumption.
    + transitivity b2 ; assumption.
Defined.

Instance ProductQMetric A B `{RA : RationalMetric A} `{RB : RationalMetric B} :
  RationalMetric (prod A B).
Proof.
  exists (fun u v => distance (fst u) (fst v) + distance (snd u) (snd v)).
  - intros [a1 b1] [a2 b2]; simpl.
    rewrite (distance_symmetric a1 a2) ;
    rewrite (distance_symmetric b1 b2) ;
    reflexivity.
  - intros [a1 b1] [a2 b2]; simpl.
    apply Qplus_nonneg_cone ; apply distance_nonnegative.
  - intros [a1 b1] [a2 b2] ; simpl; intro G.
    split.
    + apply distance_zero.
      apply (Qplus_zero_nonneg _ (distance b1 b2)).
      * apply distance_nonnegative.
      * apply distance_nonnegative.
      * assumption.
    + apply distance_zero.
      apply (Qplus_zero_nonneg (distance a1 a2) _).
      * apply distance_nonnegative.
      * apply distance_nonnegative.
      * assumption.
  - intros [a1 b1] [a2 b2] [a3 b3]; simpl.
    apply (Qle_trans _ (distance a1 a2 + distance a2 a3 + distance b1 b3) _).
    + apply Qplus_le_l. apply distance_triangle.
    + apply (Qplus_le_l _ _ (- distance a1 a2 - distance a2 a3)).
      ring_simplify.
      apply distance_triangle.
Defined.

