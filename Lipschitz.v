(* It would be extremely painful to define maps on R by hand all the time.
   So instead we prove a lemma that will allow us to cover most cases. *)

Require Import QArith Qminmax Qabs.
Require Import Cut.
Require Import MiscLemmas.
Require Import Setoid.

Local Open Scope Q_scope.

Definition locally_lipschitz_Q (f : Q -> Q) (l : Q -> Q -> Q) :=
  forall a b, forall (q r : Qinterval a b), 
    l a b * (q - r) <= f r - f q /\ f r - f q <= l a b * (r - q).

Definition lipschitz_extend (f : Q -> Q) l : locally_lipschitz_Q f l -> R -> R.
Proof.
  admit.
Defined.

Lemma lipschitz_extend_equality
      (f g : Q -> Q) lf lg (Lf : locally_lipschitz_Q f lf) (Lg : locally_lipschitz_Q g lg) :
  (forall q, f q == g q) -> (forall x, lipschitz_extend f lf Lf x == lipschitz_extend g lg Lg x)%R.
Admitted.

Definition locally_lipschitz2_Q (f : Q -> Q -> Q) (l : Q -> Q -> Q -> Q -> Q) :=
  forall a b a' b', forall (q r : Qinterval a b), forall (q' r' : Qinterval a' b'),
    l a b a' b' * ((q - r) + (q' - r')) <= f q r - f q' r' /\
    f q r - f q' r' <= l a b a' b' * ((r - q) + (r' - q')).

Definition lipschitz_extend2 (f : Q -> Q -> Q) l : locally_lipschitz2_Q f l -> (R -> R -> R).
Admitted.

Lemma lipschitz_extend2_equality
      (f g : Q -> Q -> Q) lf lg (Lf : locally_lipschitz2_Q f lf) (Lg : locally_lipschitz2_Q g lg) :
  (forall q r, f q r == g q r) ->
  (forall x y, lipschitz_extend2 f lf Lf x y == lipschitz_extend2 g lg Lg x y)%R.
Admitted.


