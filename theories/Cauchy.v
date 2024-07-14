(** The inclusion of Cauchy reals into Dedekind reals,
    and the proof that Dedekind reals are Cauchy-complete. *)

From Coq Require Import QArith.
From Coq Require Import Qabs.
From Coq Require Import Qpower.
From DedekindReals Require Import Cut.
From DedekindReals Require Import MiscLemmas.

Definition CauchyQ (un : nat -> Q) : Set
  := forall eps:Q,
    Qlt 0 eps
    -> { n:nat | forall i j:nat,
           le n i -> le n j -> Qlt (Qabs (un i - un j)) eps }.

Definition Un_cv_Q (un : nat -> Q) (l : Q) : Set
  := forall eps:Q,
    Qlt 0 eps
    -> { n:nat | forall i:nat,
           le n i -> Qlt (Qabs (un i - l)) eps }.

Lemma Un_cv_cauchy : forall (un : nat -> Q) (l : Q),
    Un_cv_Q un l -> CauchyQ un.
Proof.
  intros. intros q qPos. specialize (H (q/2)) as [k H].
  rewrite <- (Qmult_0_l (/2)). apply Qmult_lt_r.
  reflexivity. exact qPos.
  exists k. intros i j H0 H1.
  setoid_replace q with (q/2 + q/2). 2: field.
  setoid_replace (un i - un j) with ((un i - l) - (un j - l)).
  2: ring.
  apply (Qle_lt_trans _ (Qabs (un i - l) + Qabs (-(un j - l)))).
  apply Qabs_triangle. rewrite Qabs_opp. apply Qplus_lt_le_compat.
  - apply H. apply H0.
  - apply Qlt_le_weak. apply H. apply H1.
Qed.

Definition CauchyQ_lower (un : nat -> Q) (q : Q) : Prop
  := exists (r:Q) (n:nat), Qlt 0 r /\ forall i:nat, le n i -> Qlt (q+r) (un i).

Definition CauchyQ_upper (un : nat -> Q) (q : Q) : Prop
  := exists (r:Q) (n:nat), Qlt 0 r /\ forall i:nat, le n i -> Qlt (un i) (q-r).

Lemma CauchyQ_lower_open
  : forall (un : nat -> Q) (q : Q), CauchyQ_lower un q -> exists r : Q, q < r /\ CauchyQ_lower un r.
Proof.
  intros. destruct H as [r [n H]].
  exists (q+r/2). split.
  rewrite <- Qplus_0_r, <- Qplus_assoc, Qplus_lt_r, Qplus_0_l.
  rewrite <- (Qmult_0_l (/2)). apply Qmult_lt_r.
  reflexivity. apply H.
  exists (r/2), n. split.
  rewrite <- (Qmult_0_l (/2)). apply Qmult_lt_r.
  reflexivity. apply H.
  intros. rewrite <- Qplus_assoc.
  setoid_replace (r/2+r/2) with r. apply H. exact H0. field.
Qed.

Lemma CauchyQ_upper_open
  : forall (un : nat -> Q) (r : Q), CauchyQ_upper un r -> exists q : Q, q < r /\ CauchyQ_upper un q.
Proof.
  intros un q H. destruct H as [r [n H]].
  exists (q-r/2). split.
  unfold Qminus.
  rewrite <- (Qplus_0_r q), <- Qplus_assoc, <- (Qplus_lt_r _ _ (-q+r/2)).
  ring_simplify. rewrite <- (Qmult_0_l (/2)). apply Qmult_lt_r.
  reflexivity. apply H.
  exists (r/2), n. split.
  rewrite <- (Qmult_0_l (/2)). apply Qmult_lt_r.
  reflexivity. apply H.
  intros. unfold Qminus. rewrite <- Qplus_assoc.
  setoid_replace (-(r/2)+ -(r/2)) with (-r)%Q. apply H. exact H0. field.
Qed.

Lemma CauchyQ_located :
  forall (un : nat -> Q) (q r : Q),
    CauchyQ un -> q < r -> CauchyQ_lower un q \/ CauchyQ_upper un r.
Proof.
  intros un q r cau H. assert (Qlt 0 ((r-q)/4)).
  { unfold Qdiv. rewrite <- (Qmult_0_l (/4)).
    apply Qmult_lt_r. reflexivity.
    unfold Qminus. rewrite <- Qlt_minus_iff. exact H. }
  destruct (cau ((r-q)/4) H0) as [n nmaj].
  destruct (Qlt_le_dec (un n) ((q+r)/2)).
  - right. exists ((r-q)/4), n. split. exact H0. intros.
    specialize (nmaj n i (Nat.le_refl _) H1).
    rewrite <- (Qplus_lt_r _ _ (un n + - un i)). ring_simplify.
    apply (Qlt_le_trans _ ((q+r)/2) _ q0).
    rewrite <- (Qplus_le_r _ _ ((r-q)/4+-r)). ring_simplify.
    setoid_replace (un n + -1 * un i) with (un n - un i). 2: ring.
    apply Qlt_le_weak, Qabs_Qle_condition in nmaj.
    apply (Qle_trans _ (-((r-q)/4))). 2: apply nmaj.
    apply Qle_minus_iff.
    setoid_replace (- ((r - q) / 4) + - ((r - q) / 4 + -1 * r + (q + r) / 2))
      with 0.
    2: field. apply Qle_refl.
  - left. exists ((r-q)/4), n. split. exact H0. intros.
    specialize (nmaj n i (Nat.le_refl _) H1).
    rewrite <- (Qplus_lt_r _ _ (un n + - un i)). ring_simplify.
    apply (Qlt_le_trans _ ((q+r)/2)). 2: exact q0. clear q0.
    rewrite <- (Qplus_lt_r _ _ (-q-(r-q)/4)). ring_simplify.
    setoid_replace (un n + -1 * un i) with (un n - un i). 2: ring.
    apply (Qle_lt_trans _ (Qabs (un n - un i))). apply Qle_Qabs.
    apply (Qlt_le_trans _ ((r-q)/4) _ nmaj).
    apply Qle_minus_iff.
    setoid_replace (-1 * q + -1 * ((r - q) / 4) + (q + r) / 2 + - ((r - q) / 4))
      with 0.
    2: field. apply Qle_refl.
Qed.

Definition CauchyQ_R (un : nat -> Q) : CauchyQ un -> R.
Proof.
  intro cau. apply (Build_R (CauchyQ_lower un) (CauchyQ_upper un)).
  - unfold CauchyQ_lower. split. intros [r [n H0]].
    exists r, n. split. apply H0. intros. rewrite <- H. apply H0. exact H1.
    intros [r [n H0]].
    exists r, n. split. apply H0. intros. rewrite H. apply H0. exact H1.
  - unfold CauchyQ_upper. split. intros [r [n H0]].
    exists r, n. split. apply H0. intros. rewrite <- H. apply H0. exact H1.
    intros [r [n H0]].
    exists r, n. split. apply H0. intros. rewrite H. apply H0. exact H1.
  - destruct (cau 1) as [n nmaj]. reflexivity.
    exists (un n - 2), 1, n.
    split. reflexivity. intros. specialize (nmaj n i (Nat.le_refl _) H).
    rewrite <- (Qplus_lt_l _ _ (1-un i)). ring_simplify.
    apply (Qle_lt_trans _ (Qabs (un n - un i))). 2: exact nmaj.
    setoid_replace (un n + -1 * un i) with (un n - un i). 2: ring.
    apply Qle_Qabs.
  - destruct (cau 1) as [n nmaj]. reflexivity.
    exists (un n + 2), 1, n.
    split. reflexivity. intros. specialize (nmaj n i (Nat.le_refl _) H).
    rewrite Qabs_Qminus in nmaj.
    rewrite <- (Qplus_lt_l _ _ (-un n)). ring_simplify.
    apply (Qle_lt_trans _ (Qabs (un i - un n))). 2: exact nmaj.
    setoid_replace (un i + -1 * un n) with (un i - un n). 2: ring.
    apply Qle_Qabs.
  - intros. destruct H0 as [s [n [H0 H1]]].
    exists s, n. split. exact H0. intros.
    apply (Qlt_trans _ (r+s)). rewrite Qplus_lt_l. exact H. apply H1. exact H2.
  - apply CauchyQ_lower_open.
  - intros. destruct H0 as [s [n [H0 H1]]].
    exists s, n. split. exact H0. intros.
    apply (Qlt_trans _ (q-s) _ (H1 i H2)).
    unfold Qminus. rewrite Qplus_lt_l. exact H.
  - apply CauchyQ_upper_open.
  - intros q [[r [n H]] [s [m H0]]]. destruct H, H0.
    specialize (H1 (max n m) (Nat.le_max_l _ _)).
    specialize (H2 (max n m) (Nat.le_max_r _ _)).
    apply (Qlt_trans _ _ _ H1) in H2.
    unfold Qminus in H2. rewrite <- (Qplus_lt_r _ _ (s-q)) in H2.
    ring_simplify in H2. apply (Qlt_irrefl (s+r)).
    apply (Qlt_trans _ 0 _ H2). rewrite <- Qplus_0_r.
    apply Qplus_lt_le_compat. exact H0. apply Qlt_le_weak. exact H.
  - intros. apply CauchyQ_located. exact cau. exact H.
Defined.


Fixpoint sum_f_Q0 (f:nat -> Q) (N:nat) : Q :=
  match N with
    | O => f 0%nat
    | S i => sum_f_Q0 f i + f (S i)
  end.

Lemma sum_eq : forall (un vn : nat -> Q) (n : nat),
    (forall k:nat, un k == vn k)
    -> sum_f_Q0 un n == sum_f_Q0 vn n.
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. rewrite H. rewrite IHn. reflexivity. exact H.
Qed.

Lemma sum_Qle : forall (un vn : nat -> Q) (n : nat),
    (forall k:nat, Qle (un k) (vn k))
    -> Qle (sum_f_Q0 un n) (sum_f_Q0 vn n).
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. apply Qplus_le_compat. apply IHn. exact H.
    apply H.
Qed.

Lemma sum_assoc : forall (u : nat -> Q) (n p : nat),
    sum_f_Q0 u (S n + p)
    == Qplus (sum_f_Q0 u n) (sum_f_Q0 (fun k => u (S n + k)%nat) p).
Proof.
  induction p.
  - simpl. rewrite Nat.add_0_r. reflexivity.
  - simpl. rewrite Qplus_assoc. apply Qplus_comp. 2: reflexivity.
    rewrite Nat.add_succ_r.
    rewrite (sum_eq (fun k : nat => u (S (n + k))) (fun k : nat => u (S n + k)%nat)).
    rewrite <- IHp. reflexivity. intros. reflexivity.
Qed.

Lemma cond_pos_sum : forall (u : nat -> Q) (n : nat),
    (forall k:nat, Qle 0 (u k))
    -> Qle 0 (sum_f_Q0 u n).
Proof.
  induction n.
  - intros. apply H.
  - intros. simpl. apply (Qle_trans _ (sum_f_Q0 u n + 0)).
    rewrite Qplus_0_r. apply IHn. exact H.
    rewrite Qplus_le_r. apply H.
Qed.

Lemma pos_sum_more : forall (u : nat -> Q)
                            (n p : nat),
    (forall k:nat, Qle 0 (u k))
    -> le n p -> Qle (sum_f_Q0 u n) (sum_f_Q0 u p).
Proof.
  intros. destruct (Nat.le_exists_sub n p H0). destruct H1. subst p.
  rewrite Nat.add_comm.
  destruct x. rewrite Nat.add_0_r. apply Qle_refl. rewrite Nat.add_succ_r.
  replace (S (n + x)) with (S n + x)%nat. rewrite <- Qplus_0_r.
  rewrite sum_assoc. rewrite Qplus_le_r.
  apply cond_pos_sum. intros. apply H. auto.
Qed.

Lemma pos_sum_le_last : forall (un : nat -> Q) (n : nat),
    (forall k:nat, Qle 0 (un k))
    -> Qle (un n) (sum_f_Q0 un n).
Proof.
  destruct n.
  - intros. apply Qle_refl.
  - intros. rewrite <- Qplus_0_l. simpl. apply Qplus_le_compat.
    apply cond_pos_sum. exact H. apply Qle_refl.
Qed.

Fixpoint Find_positive_in_sum (un : nat -> Q) (n : nat)
  : (forall k:nat, Qle 0 (un k))
    -> Qlt 0 (sum_f_Q0 un n)
    -> exists k:nat, Qlt 0 (un k).
Proof.
  destruct n.
  - intros. exists O. exact H0.
  - intros. simpl in H0. destruct (Q_dec 0 (un (S n))). destruct s.
    + exists (S n). exact q.
    + exfalso. exact (Qle_not_lt 0 (un (S n)) (H (S n)) q).
    + rewrite <- q, Qplus_0_r in H0.
      destruct (Find_positive_in_sum un n H H0). exists x. exact H1.
Qed.

Lemma multiTriangleIneg : forall (u : nat -> Q) (n : nat),
    Qle (Qabs (sum_f_Q0 u n)) (sum_f_Q0 (fun k => Qabs (u k)) n).
Proof.
induction n.
  - apply Qle_refl.
  - simpl sum_f_Q0. apply (Qle_trans _ (Qabs (sum_f_Q0 u n) + Qabs (u (S n)))).
    apply Qabs_triangle. rewrite Qplus_le_l. apply IHn.
Qed.

Lemma Abs_sum_maj : forall (un vn : nat -> Q),
    (forall n:nat, Qle (Qabs (un n)) (vn n))
    -> forall n p:nat, (Qabs (sum_f_Q0 un n - sum_f_Q0 un p) <=
              sum_f_Q0 vn (Init.Nat.max n p) - sum_f_Q0 vn (Init.Nat.min n p))%Q.
Proof.
  intros. destruct (le_lt_dec n p).
  - destruct (Nat.le_exists_sub n p) as [k [maj _]]. assumption.
    subst p. rewrite max_r. rewrite min_l. rewrite Qabs_Qminus.
    destruct k. simpl plus. unfold Qminus. rewrite Qplus_opp_r.
    rewrite Qplus_opp_r. rewrite Qabs_pos. apply Qle_refl. apply Qle_refl.
    replace (S k + n)%nat with (S n + k)%nat.
    rewrite sum_assoc. rewrite sum_assoc.
    unfold Qminus. rewrite Qplus_comm.
    rewrite Qplus_assoc.
    setoid_replace (- sum_f_Q0 un n + sum_f_Q0 un n) with 0.
    2: ring. ring_simplify. rewrite Qplus_0_l.
    apply (Qle_trans _ (sum_f_Q0 (fun k0 : nat => Qabs (un (S n + k0)%nat)) k)).
    apply multiTriangleIneg. apply sum_Qle. intros.
    apply H. simpl. rewrite Nat.add_comm. reflexivity.
    assumption. assumption.
  - destruct (Nat.le_exists_sub p n) as [k [maj _]]. unfold lt in l.
    apply (Nat.le_trans p (S p)). apply le_S. apply Nat.le_refl. assumption.
    subst n. rewrite max_l. rewrite min_r.
    destruct k. simpl plus. unfold Qminus. rewrite Qplus_opp_r.
    rewrite Qplus_opp_r. rewrite Qabs_pos. apply Qle_refl. apply Qle_refl.
    replace (S k + p)%nat with (S p + k)%nat.
    rewrite sum_assoc. rewrite sum_assoc. ring_simplify.
    setoid_replace (sum_f_Q0 un p + sum_f_Q0 (fun k0 : nat => un (S p + k0)%nat) k - sum_f_Q0 un p)
      with (sum_f_Q0 (fun k0 : nat => un (S p + k0)%nat) k).
    2: ring.
    apply (Qle_trans _ (sum_f_Q0 (fun k0 : nat => Qabs (un (S p + k0)%nat)) k)).
    apply multiTriangleIneg. apply sum_Qle. intros.
    apply H. simpl. rewrite Nat.add_comm. reflexivity.
    apply (Nat.le_trans p (S p)). apply le_S. apply Nat.le_refl. assumption.
    apply (Nat.le_trans p (S p)). apply le_S. apply Nat.le_refl. assumption.
Qed.

(* The constructive analog of the least upper bound principle. *)
Lemma Cauchy_series_maj : forall (un vn : nat -> Q),
    (forall n:nat, Qabs (un n) <= vn n)
    -> CauchyQ (sum_f_Q0 vn)
    -> CauchyQ (sum_f_Q0 un).
Proof.
  intros. intros eps epsPos.
  destruct (H0 eps epsPos) as [n nmaj]. exists n. intros.
  apply (Qle_lt_trans _ (sum_f_Q0 vn (max i j) - sum_f_Q0 vn (min i j))).
  apply Abs_sum_maj. apply H.
  setoid_replace (sum_f_Q0 vn (max i j) - sum_f_Q0 vn (min i j))%Q
    with (Qabs (sum_f_Q0 vn (max i j) - (sum_f_Q0 vn (min i j)))).
  apply nmaj. apply (Nat.le_trans _ i). assumption. apply Nat.le_max_l.
  apply Nat.min_case. apply (Nat.le_trans _ i). assumption. apply Nat.le_refl.
  exact H2. rewrite Qabs_pos. reflexivity.
  apply (Qplus_le_l _ _ (sum_f_Q0 vn (Init.Nat.min i j))).
  ring_simplify. apply pos_sum_more.
  intros. apply (Qle_trans _ (Qabs (un k))). apply Qabs_nonneg.
  apply H. apply (Nat.le_trans _ i). apply Nat.le_min_l. apply Nat.le_max_l.
Qed.

Lemma GeoHalfSum : forall k:nat,
    sum_f_Q0 (fun n:nat => (/2)^(Z.of_nat n)) k == 2 - (/2)^(Z.of_nat k).
Proof.
  induction k.
  - reflexivity.
  - simpl. rewrite IHk. clear IHk.
    rewrite <- (Qplus_inj_l _ _ (Qpower_positive (/ 2) (Pos.of_succ_nat k)
                                +(/ 2) ^ Z.of_nat k -2)).
    ring_simplify.
    setoid_replace (Qpower_positive (/ 2) (Pos.of_succ_nat k))
      with ((/ 2) ^ Z.of_nat (S k)).
    2: reflexivity. rewrite Nat2Z.inj_succ. unfold Z.succ.
    rewrite Qpower_plus. field. intro abs. discriminate.
Qed.

Lemma TwoPowerBound : forall n:nat, Qlt (Z.of_nat n#1) (2^Z.of_nat n).
Proof.
  induction n. reflexivity.
  rewrite Nat2Z.inj_succ. unfold Z.succ. rewrite Qpower_plus.
  simpl. rewrite <- Qinv_plus_distr.
  setoid_replace (2 ^ Z.of_nat n * 2) with (2 ^ Z.of_nat n + 2 ^ Z.of_nat n).
  2: ring.
  apply Qplus_lt_le_compat. exact IHn.
  apply pow_Q1_Qle. discriminate.
  intro abs. discriminate.
Qed.

Lemma GeoHalfSeries : Un_cv_Q (sum_f_Q0 (fun n:nat => (/2)^(Z.of_nat n))) 2.
Proof.
  intros [a b] qPos. exists (Pos.to_nat b). intros.
  rewrite GeoHalfSum.
  setoid_replace (2 - (/ 2) ^ Z.of_nat i - 2) with (- (/ 2) ^ Z.of_nat i).
  2: ring. rewrite Qabs_opp.
  apply (Qlt_le_trans _ (1#b)). rewrite Qabs_pos.
  2: apply Qpower_pos; discriminate.
  rewrite Qinv_power. rewrite <- (Qmult_lt_l _ _ (2 ^ Z.of_nat i / (1#b))).
  field_simplify.
  setoid_replace (1 / (1 # b)) with (Z.of_nat (Pos.to_nat b) # 1).
  apply (Qlt_le_trans _ (2^Z.of_nat (Pos.to_nat b))).
  apply TwoPowerBound. apply pow_Q1_incr. discriminate. exact H.
  unfold Qeq; simpl. rewrite Z.mul_1_r, Pos.mul_1_r.
  rewrite positive_nat_Z. reflexivity.
  intro abs. discriminate. split.
  assert (~ 0 == 2 ^ Z.of_nat i). apply Qlt_not_eq.
  apply Qpower_strictly_pos. reflexivity. intro abs.
  symmetry in abs. contradiction.
  intro abs. discriminate.
  rewrite <- (Qmult_0_l (/(1#b))). apply Qmult_lt_r.
  unfold Qlt; simpl. rewrite Pos.mul_1_r. apply Pos2Z.pos_is_pos.
  apply Qpower_strictly_pos. reflexivity.
  unfold Qle; simpl. rewrite <- (Z.mul_1_l (Z.pos b)).
  rewrite Z.mul_assoc.
  apply Z.mul_le_mono_nonneg_r. apply Pos2Z.pos_is_nonneg.
  rewrite Z.mul_1_r. unfold Qlt in qPos; simpl in qPos.
  rewrite Z.mul_1_r in qPos. apply Z.le_succ_l in qPos.
  exact qPos.
Qed.
