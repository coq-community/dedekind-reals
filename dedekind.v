(** An attempt to formalized Dedekind reals in Coq. *)

Require Import QArith.
Require Import QOrderedType.
Require Import Morphisms Setoid.

Structure R := {
  lower : Q -> Prop;
  upper : Q -> Prop;
  lower_bound : exists q : Q, lower q;
  upper_bound : exists r : Q, upper r;
  lower_lower : forall q r, q < r -> lower r -> lower q;
  lower_open : forall q, lower q -> exists r, q < r /\ lower r;
  upper_upper : forall q r, q < r -> upper q -> upper r;
  uper_open : forall r, upper r -> exists q, q < r /\ upper q;
  disjoint : forall q, ~ (lower q /\ upper q);
  located : forall q r, q < r -> lower q \/ upper r
}.

Local Open Scope Q_scope.

Definition Q_inject : Q -> R.
Proof.
  intro s.
  refine {| lower := (fun q => (q < s)) ; upper := (fun r => (s < r)) |}.
  - exists (s + (-1#1)).
    assert (E : s == s + 0). ring.
    rewrite E at 2.
    apply Qplus_lt_r.
    unfold Qlt. unfold Zlt. auto.
  - exists (s + 1).
    assert (E : s == s + 0); [ring | idtac].
    rewrite E at 1.
    apply Qplus_lt_r.
    unfold Qlt, Zlt; auto.
  - q_order.
  - intros q H.
    exists ((q + s) * (1#2)). split.
Admitted.

Definition neg (x : R) : R.
Proof.
  refine {| lower := (fun q => upper x (-q)); upper := (fun r => lower x (-r)) |}.
  - destruct (upper_bound x) as [r H].
    exists (- r).
    rewrite (Qopp_involutive r).
