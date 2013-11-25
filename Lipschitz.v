(* It would be extremely painful to define maps on R by hand all the time.
   So instead we prove a lemma that will allow us to cover most cases. *)

Require Import Setoid Morphisms SetoidClass.

Require Import QArith Qminmax Qabs.
Require Import Cut.
Require Import MiscLemmas.
Require Import QMetric.

Record LocallyLipschitz
      {A B : Type} `{RA : RationalMetric A} `{RB : RationalMetric B}
      (f : A -> B) :=
{
  modulus :> A -> Q -> Q ;
  modulus_nonnegative : forall x q, 0 <= modulus x q ;
  modulus_monotone : forall x q r, 0 <= q -> 0 <= r -> q <= r -> modulus x q <= modulus x r ;
  lipschitz_condition :
    forall (x y : A) q,
      distance x y <= q -> distance (f x) (f y) <= modulus x q * distance x y
}.

Definition locally_lipschitz_constant
         {A} `{RationalMetric A} (x : A) : LocallyLipschitz (const x).
Proof.
  exists (fun _ _ => 0).
  - intros ? ; discriminate.
  - intros ? ? ? ? ; discriminate.
  - intros y z q _.
    unfold const ; rewrite distance_diag ; ring_simplify.
    discriminate.
Defined.

Ltac liptac :=
  assumption ||
  match goal with
    | [ |- 0 <= distance _ _ ] => apply distance_nonnegative
    | [ |- 0 <= modulus _ _ _ _] => apply modulus_nonnegative ; liptac
    | [ |- modulus ?f ?mf ?x _ <= modulus ?f ?mf ?x _] => apply modulus_monotone ; liptac
    | [ |- 0 <= ?a * ?b ] => apply Qmult_le_0_compat ; liptac
    | [ |- ?a * ?b <= ?c * ?d ] => apply Qmult_le_compat ; liptac
    | [ |- _ ] => idtac
  end.

Definition compose_LocallyLipschitz
         {A B C} `{EA : Setoid A} `{EB : Setoid B} `{EC : Setoid C}
         `{RA : RationalMetric A} `{RB : RationalMetric B} `{RC : RationalMetric C}
         (f : A -> B) (g : B -> C) (mf : LocallyLipschitz f) (mg : LocallyLipschitz g) :
  LocallyLipschitz (g o f).
Proof.
  exists (fun x q => mg (f x) (q * mf x q) * mf x q).
  - intros ; apply Qmult_le_0_compat ; apply modulus_nonnegative.
  - intros x q r Hq Hr G.
    apply Qmult_le_compat ; try (apply modulus_nonnegative) ;
    apply modulus_monotone ; auto using modulus_nonnegative.
    + apply Qmult_le_0_compat ; [assumption | apply modulus_nonnegative].
    + apply Qmult_le_0_compat ; [assumption | apply modulus_nonnegative].
    + apply Qmult_le_compat ; auto using modulus_monotone, modulus_nonnegative.
      * apply modulus_nonnegative.
      * apply modulus_monotone ; assumption.
  - intros x y q G.
    unfold compose.
    apply (Qle_trans _ (mg (f x) (mf x q * distance x y) * distance (f x) (f y))) ;
      [ repeat apply lipschitz_condition; assumption | idtac].
    setoid_rewrite <- Qmult_assoc.
    apply Qmult_le_compat.
    + apply modulus_monotone.
      * liptac.
      * liptac.
        apply (Qle_trans _ (distance x y)) ; [ apply distance_nonnegative | assumption ].
      * rewrite Qmult_comm at 1 ; apply Qmult_le_compat_r ; liptac.
    + apply distance_nonnegative.
    + liptac.
    + apply lipschitz_condition ; assumption.
Defined.

Definition extend {n : nat} (f : power1 n Q -> Q) `{LocallyLipschitz f} : power1 n R -> R.
Admitted.

Lemma extend_eq {n : nat} (f g : power1 n Q -> Q)
      `{mf : LocallyLipschitz f} `{mg : LocallyLipschitz g} :
  (forall u v : power1 n Q, f u == g u) ->
  (forall x y : power1 n R, @extend _ f mf x == @extend _ g mg y).
Admitted.

Definition Qplus' : Q * Q -> Q := fun u => fst u + snd u.
Hint Unfold Qplus'.

Definition Qplus_LocallyLipschitz : LocallyLipschitz Qplus'.
Proof.
  refine {| modulus := fun _ _ => 1 |}.
  - intros ; discriminate.
  - intros ; discriminate.
  - intros [a1 b1] [a2 b2] q _.
    unfold Qplus', QMetric, ProductMetric, distance, fst, snd.
    ring_simplify.
    setoid_replace (a1 + b1 - (a2 + b2)) with ((a1 - a2) + (b1 - b2)) ;
      [idtac | ring_simplify ; reflexivity].
    apply Qabs_triangle.
Defined.

Definition Qmult' : Q * Q -> Q := fun u => fst u * snd u.

Definition Qmult_LocallyLipschitz : LocallyLipschitz Qmult'.
Proof.
  refine {| modulus := fun u q => Qmax (Qabs (fst u)) (Qabs (snd u)) + q |}.
  - admit.
  - admit.
  - admit.
Defined.

Definition Qopp_LocallyLipschitz : LocallyLipschitz Qopp.
Proof.
  refine {| modulus := fun _ _ => 1 |}.
  - admit.
  - admit.
  - admit.
Defined.
