(* The Archimedean axiom.

   Let q be a positive rational number. Say that p pair of rationals (l, u) "straddle a
   real x with gap q" if l < x < u and u - l < q.

   The Archimdean axiom is equivalent to the statement that for every x and positive q we
   can find a straddling pair (u, l). In other words, this means we cna find arbitrarily
   good lower and upper rational approximations to x. *)

From Coq Require Import QArith.
From DedekindReals Require Import MiscLemmas.
From DedekindReals Require Import Cut.

Local Open Scope Q_scope.

Definition straddle (x : R) (q : Q) :=
  exists l u : Q, lower x l /\ upper x u /\ u - l < q.

Lemma straddle_monotone (x : R) (q r : Q) (G : q < r) :
  straddle x q -> straddle x r.
Proof.
  intros [l [u [? [? ?]]]].
  exists l, u ; repeat split ; auto.
  transitivity q ; auto.
Qed.

Lemma propSwitch : forall (L U : nat -> Prop) (k : nat),
    (forall n:nat, L n \/ U (S n))
    -> L O
    -> U (S (S k))
    -> exists p:nat, L p /\ U (S (S p)).
Proof.
  induction k.
  - intros. exists O. split; assumption.
  - intros. destruct (H (S k)).
    + clear IHk. exists (S k). split; assumption.
    + apply IHk. assumption. assumption. assumption.
Qed.

Definition DReal_approx (x : R) (eps : Q) :
  Qlt 0 eps -> exists q:Q, lower x q /\ upper x (q+eps).
Proof.
  intro epsPos. pose proof (upper_le x) as uu.
  pose proof (lower_below_upper x) as bup.
  destruct x; simpl; simpl in uu, bup.
  destruct lower_bound as [q l], upper_bound as [r u].
  destruct ((r - q) * inject_Z 2 / eps) eqn:des.
  assert (Z.le 0 Qnum) as QnumPos.
  { assert (Qle 0 (Qnum # Qden)). rewrite <- des.
    apply Qmult_le_0_compat. apply Qmult_le_0_compat.
    apply (Qle_minus_iff q r). apply Qle_lteq. left.
    apply bup; assumption. unfold Qle. simpl. unfold Z.le.
    intro absurd. inversion absurd.
    apply Qle_lteq. left. apply Qinv_lt_0_compat. assumption.
    unfold Qle in H. simpl in H. rewrite Zmult_1_r in H. assumption. }
  destruct (propSwitch (fun n => lower (q + inject_Z (Z.of_nat n) * eps / inject_Z 2)%Q)
                        (fun n => upper (q + inject_Z (Z.of_nat n) * eps / inject_Z 2)%Q)
                        (Z.to_nat Qnum)) as [n H].
  - intro n. apply located. apply Qplus_lt_r. apply Qmult_lt_r.
    apply Qinv_lt_0_compat. unfold Qlt. simpl. unfold Z.lt. auto.
    apply Qmult_lt_r. assumption. rewrite <- Zlt_Qlt.
    apply inj_lt. apply Nat.le_refl.
  - simpl. rewrite Qmult_0_l. unfold Qdiv. rewrite Qmult_0_l.
    rewrite Qplus_0_r. assumption.
  - apply (uu r). exact u. rewrite <- Qplus_0_l. rewrite <- (Qplus_opp_r q).
    rewrite <- Qplus_assoc. apply Qplus_le_r. rewrite Qplus_comm.
    apply Qle_shift_div_l. unfold Qlt. unfold Z.lt. auto.
    setoid_replace ((r + - q) * inject_Z 2)%Q
      with (((r + - q) * inject_Z 2 / eps) * eps)%Q.
    2: field.
    apply Qmult_le_compat_r. unfold Qminus in des.
    rewrite des. apply (Qle_trans _ (Qnum # 1)).
    apply Z.mul_le_mono_nonneg_l. assumption.
    unfold Z.le. simpl. unfold Pos.compare. destruct Qden; discriminate.
    rewrite <- (Zle_Qle Qnum).
    replace (S (S (Z.to_nat Qnum))) with (plus 2 (Z.to_nat Qnum)).
    rewrite Nat2Z.inj_add. rewrite Z2Nat.id. rewrite <- (Zplus_0_l Qnum).
    rewrite Zplus_assoc. apply Zplus_le_compat_r. discriminate.
    assumption. reflexivity. apply Qlt_le_weak. apply epsPos.
    intro absurd. apply Qeq_sym in absurd. apply (Qlt_not_eq 0 eps); assumption.
  - exists (q + inject_Z (Z.of_nat n) * eps / inject_Z 2)%Q. split.
    apply H.
    setoid_replace (q + inject_Z (Z.of_nat n) * eps / inject_Z 2 + eps)%Q
      with (q + inject_Z (Z.of_nat (S (S n))) * eps / inject_Z 2)%Q.
    apply H. setoid_replace (inject_Z (Z.of_nat (S (S n))))
               with (inject_Z 2 + inject_Z (Z.of_nat n))%Q.
    field. replace (S (S n)) with (2 + n)%nat.
    rewrite (Nat2Z.inj_add 2 n). rewrite inject_Z_plus.
    reflexivity. reflexivity.
Qed.

Lemma archimedean : forall (x : R) (q : Q), 0 < q -> straddle x q.
Proof.
  intros.
  assert (Qlt 0 (q/2)).
  { rewrite <- (Qmult_0_l (/2)). unfold Qdiv. rewrite Qmult_lt_r.
    exact H. reflexivity. }
  destruct (DReal_approx x (q/2) H0). exists x0, (x0+(q/2)).
  repeat split. apply H1. apply H1. ring_simplify.
  unfold Qdiv. rewrite <- (Qmult_1_r q), <- Qmult_assoc.
  rewrite Qmult_lt_l. 2: exact H. reflexivity.
Qed.
