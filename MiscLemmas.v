(** Various lemmas that seem to be missing from the standard library. *)

Require Import QArith Qminmax Qabs.

Definition compose {A B C} (g : B -> C) (f : A -> B) := fun x => g (f x).
Hint Unfold compose.
Notation "g 'o' f" := (compose g f) (at level 40, left associativity).

Definition const A B (y : B) : A -> B := (fun x => y).

(* power1 n A is the (n+1)-fold power of A, for instance power1 3 A is A * A * A * A. *)
Fixpoint power1 (n : nat) (A : Type) : Type :=
  match n with
    | 0%nat => A
    | S m => (power1 m A * A)%type
  end.

Notation "A ^^ n" := (power1 n A) (at level 8, left associativity) : type_scope.

Local Open Scope Q_scope.

Definition Qpositive := {q : Q | q > 0}.

Coercion Q_of_Qpositive (u : Qpositive) := projT1 u.

Definition Qnonnegative := {q : Q | q >= 0}.

Coercion Q_of_Qnonnegative (q : Qnonnegative) := projT1 q.

Lemma Qeq_le (p q : Q) : p == q -> p <= q.
Proof.
  intro E.
  rewrite E.
  apply Qle_refl.
Defined.


Lemma Qopp_lt_compat : forall (p q : Q), p < q <-> -q < -p.
Proof.
  intros [a b] [c d].
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
  rewrite <- (Qmult_0_l q).
  apply Qmult_lt_compat_r; assumption.
Qed.

Lemma Qlt_mult_neg_r (q r s : Q) : s < 0 -> (q < r <-> r * s < q * s).
Proof.
  admit.
Qed.

Lemma Qlt_mult_neg_l (q r s : Q) : q < 0 -> (r < s <-> q * s < q * r).
Proof.
  admit.
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

Lemma Qplus_nonneg_cone : forall q r, 0 <= q -> 0 <= r -> 0 <= q + r.
Proof.
  intros q r G H.
  setoid_replace 0 with (0 + 0) ; [idtac | (compute; reflexivity)].
  apply Qplus_le_compat; assumption.
Qed.

Lemma Qplus_zero_nonneg : forall q r, 0 <= q -> 0 <= r -> q + r == 0 -> q == 0 /\ r == 0.
Proof.
  intros q r Pq Pr H.
  split.
  - apply Qle_antisym ; auto.
    setoid_rewrite <- H.
    setoid_replace q with (q + 0) at 1 ; [idtac | ring].
    apply Qplus_le_r; assumption.
  - apply Qle_antisym ; auto.
    setoid_rewrite <- H.
    setoid_replace r with (0 + r) at 1 ; [idtac | ring].
    apply Qplus_le_l; assumption.
Qed.

Require Import Qpower.

Lemma Qpower_zero: forall p, ~p == 0 -> p^0 == 1.
Proof.
intros p H.
compute ; auto.
Qed.

Lemma Qopp_nonzero : forall p, ~ p == 0 -> ~ (-p) == 0.
Proof.
  intros p A.
  destruct (Q_dec 0 p) as [ [ B | C ] | D ].
  - assert (E:= Qopp_lt_compat 0 p).
    firstorder.
  - assert (F:= Qopp_lt_compat p 0).
    firstorder.
  - assert (G:= Qeq_sym 0 p D).
    elim (A G).
Qed.

Lemma lt_from_le_nonzero: forall p, 0 <= p -> ~ p == 0 -> 0 < p.
Proof.
  intros p H G.
  destruct (Qlt_le_dec 0 p) as [K|L].
  - assumption.
  - absurd (p == 0) ; auto.
    apply Qle_antisym ; assumption.
Qed.

Lemma Qinv_gt_0_compat: forall a : Q, a < 0 -> / a < 0.
Proof.
  intros [[|n|n] d] Ha; assumption.
Qed.

Lemma Qinv_nonzero : forall p, ~ p == 0 -> ~ (/ p == 0).
Proof.
intros p H.
destruct (Q_dec 0 p) as [[A1|A2]|B].
- assert (F:= Qinv_lt_0_compat p A1).
  apply Qnot_eq_sym, (Qlt_not_eq 0 (/p) F).
- assert (F:= Qinv_gt_0_compat p A2).
  apply (Qlt_not_eq (/p) 0 F).
- assert (U := Qnot_eq_sym p 0 H).
  elim (U B).
Qed.

Lemma Qpower_nonzero : forall p n, ~ p==0 -> ~ p^n==0.
Proof.
intros p n G.
induction n.
- rewrite (Qpower_zero p).
  apply Q_apart_0_1.
  assumption.
- apply (Qpower_not_0_positive p p0 G).
- apply Qinv_nonzero, (Qpower_not_0_positive p p0 G).
Qed.

Lemma Qpower_strictly_pos : forall p n, 0 < p -> 0 < p^n.
Proof.
  intros p n G.
  apply lt_from_le_nonzero.
  - apply Qpower_pos, Qlt_le_weak; assumption.
  - apply Qpower_nonzero, Qnot_eq_sym, Qlt_not_eq ; assumption.
Qed.

Lemma Qabs_eq_0 : forall q, Qabs q == 0 -> q == 0.
Proof.
  intros q Hq.
  assert (Gq : Qabs q <= 0) ; [(rewrite Hq ; discriminate) | idtac].
  destruct (proj1 (Qabs_Qle_condition q 0) Gq).
  apply Qle_antisym; assumption.
Qed.

Lemma Qmult_le_compat_l : forall x y z, y <= z -> 0 <= x -> x*y <= x*z.
Proof.
  admit.
Qed.

Lemma Qmult_le_compat : forall q r s t,
  q <= r -> 0 <= s -> 0 <= q -> s <= t -> q * s <= r * t.
Proof.
  intros q r s t H1 H2 H3 H4.
  apply (Qle_trans _ (r * s)).
  - apply Qmult_le_compat_r ; assumption.
  - apply Qmult_le_compat_l.
    + assumption.
    + apply (Qle_trans _ q) ; assumption.
Qed.
