(** The multiplicative structure of reals. *)

Require Import Setoid Morphisms SetoidClass.
Require Import MiscLemmas.
Require Import QArith QOrderedType Qminmax Qabs.
Require Import Cut Additive Archimedean.

Local Open Scope Q_scope.

(** A hack to be able to have proof-relevant unfinished constructions.
    When this file is cleaned up, remove this axiom and the tactic. *)
Axiom unfinished : forall (A : Type), A.
Ltac todo := apply unfinished.

(** Multiplication. *)

Definition Qmin4 (a b c d : Q) : Q
  := Qmin (Qmin a b) (Qmin c d).
Definition Qmax4 (a b c d : Q) : Q
  := Qmax (Qmax a b) (Qmax c d).

Add Parametric Morphism : Qmin4
    with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> Qeq
      as Qmin4_morph.
Proof.
  intros. unfold Qmin4. rewrite H. rewrite H0.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Add Parametric Morphism : Qmax4
    with signature Qeq ==> Qeq ==> Qeq ==> Qeq ==> Qeq
      as Qmax4_morph.
Proof.
  intros. unfold Qmax4. rewrite H. rewrite H0.
  rewrite H1. rewrite H2. reflexivity.
Qed.

Lemma Qmin4_opp : forall a b c d : Q,
    Qeq (Qmin4 (-a) (-b) (-c) (-d))
        (- Qmax4 a b c d).
Proof.
  assert (forall a b : Q, Qeq (Qmin (-a) (-b)) (- Qmax a b)).
  { intros. destruct (Qlt_le_dec a b). rewrite Q.min_r.
    rewrite Q.max_r. reflexivity. apply Qlt_le_weak. apply q.
    apply Qopp_le_compat. apply Qlt_le_weak. apply q.
    rewrite Q.min_l. rewrite Q.max_l. reflexivity. apply q.
    apply Qopp_le_compat. apply q. }
  intros. unfold Qmin4, Qmax4.
  rewrite H. rewrite H. apply H.
Qed.

Lemma Qmax4_opp : forall a b c d : Q,
    Qeq (Qmax4 (-a) (-b) (-c) (-d))
        (- Qmin4 a b c d).
Proof.
  assert (forall a b : Q, Qeq (Qmax (-a) (-b)) (- Qmin a b)).
  { intros. destruct (Qlt_le_dec a b). rewrite Q.max_l.
    rewrite Q.min_l. reflexivity. apply Qlt_le_weak. apply q.
    apply Qopp_le_compat. apply Qlt_le_weak. apply q.
    rewrite Q.min_r. rewrite Q.max_r. reflexivity.
    apply Qopp_le_compat. apply q. apply q. }
  intros. unfold Qmin4, Qmax4.
  rewrite H. rewrite H. apply H.
Qed.

Lemma Qpos_above_opp : forall q : Q,
    Qlt 0 q <-> Qlt (-q) q.
Proof.
  split.
  - intros. apply (Qplus_lt_r _ _ q). rewrite Qplus_opp_r.
    setoid_replace (q+q)%Q with ((1+1)*q)%Q. 2: ring.
    rewrite <- (Qmult_0_r (1+1)). rewrite Qmult_lt_l.
    apply H. reflexivity.
  - intros. apply (Qplus_lt_r _ _ q) in H. rewrite Qplus_opp_r in H.
    setoid_replace (q+q)%Q with ((1+1)*q)%Q in H. 2: ring.
    rewrite <- (Qmult_0_r (1+1)) in H. rewrite Qmult_lt_l in H.
    apply H. reflexivity.
Qed.

Lemma Qmin4_le_max4 : forall a b c d : Q,
    Qle (Qmin4 a b c d) (Qmax4 a b c d).
Proof.
  intros. unfold Qmin4, Qmax4.
  apply (Qle_trans _ (Qmin a b)). apply Q.le_min_l.
  apply (Qle_trans _ a). apply Q.le_min_l.
  apply (Qle_trans _ (Qmax a b)). apply Q.le_max_l.
  apply Q.le_max_l.
Qed.

Lemma Qmin4_flip : forall a b c d : Q,
    Qeq (Qmin4 a b c d) (Qmin4 a c b d).
Proof.
  intros. unfold Qmin4. rewrite Q.min_assoc.
  rewrite (Q.min_comm a b). rewrite <- (Q.min_assoc b a c).
  rewrite (Q.min_comm b). rewrite <- Q.min_assoc. reflexivity.
Qed.

Lemma Qmax4_flip : forall a b c d : Q,
    Qeq (Qmax4 a b c d) (Qmax4 a c b d).
Proof.
  intros.
  assert (Qeq (- Qmax4 a b c d) (- Qmax4 a c b d)).
  rewrite <- Qmin4_opp. rewrite <- Qmin4_opp.
  apply Qmin4_flip. apply Qopp_comp in H.
  rewrite Qopp_involutive in H. rewrite Qopp_involutive in H.
  apply H.
Qed.

Lemma plus_max4_distr_l : forall n m i j p : Q,
    Qeq (Qmax4 (p + n) (p + m) (p + i) (p + j)) (p + Qmax4 n m i j).
Proof.
  intros. unfold Qmax4.
  rewrite Q.plus_max_distr_l. rewrite Q.plus_max_distr_l.
  apply Q.plus_max_distr_l.
Qed.

Lemma plus_min4_distr_l : forall n m i j p : Q,
    Qeq (Qmin4 (p + n) (p + m) (p + i) (p + j)) (p + Qmin4 n m i j).
Proof.
  intros. unfold Qmin4.
  rewrite Q.plus_min_distr_l. rewrite Q.plus_min_distr_l.
  apply Q.plus_min_distr_l.
Qed.

(* The lower cut of the product of [x] and [y]. *)
Local Definition mult_lower (x y : R) (q : Q) :=
  exists a b c d : Q, lower x a /\ upper x b /\ lower y c /\ upper y d /\
                 q < Qmin4 (a*c) (a*d) (b*c) (b*d).

(* The upper cut of the product of [x] and [y]. *)
Local Definition mult_upper (x y : R) (q : Q) :=
  exists a b c d : Q, lower x a /\ upper x b /\ lower y c /\ upper y d /\
                 Qmax4 (a*c) (a*d) (b*c) (b*d) < q.

Definition mult_lower_proper (x y : R) : Proper (Qeq ==> iff) (mult_lower x y).
Proof.
  intros q r Eqr ; split ; intros [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Eqr ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Eqr ; assumption.
Qed.

Local Definition mult_upper_proper (x y : R) : Proper (Qeq ==> iff) (mult_upper x y).
Proof.
  intros q r Eqr ; split ; intros [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Eqr ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Eqr ; assumption.
Qed.

Lemma middle_between : forall q r : Q,
    Qlt q r -> (Qlt q ((q+r)*(1#2)) /\ Qlt ((q+r)*(1#2)) r).
Proof.
  split.
  - rewrite <- (Qmult_lt_r _ _ (2#1)). apply (Qplus_lt_r _ _ (-q)).
    ring_simplify. apply H. reflexivity.
  - rewrite <- (Qmult_lt_r _ _ (2#1)). apply (Qplus_lt_r _ _ (-r)).
    ring_simplify. apply H. reflexivity.
Qed.

Lemma mult_lower_open : forall (x y : R) (q : Q),
    mult_lower x y q -> exists r:Q, Qlt q r /\ mult_lower x y r.
Proof.
  intros. destruct H,H,H,H,H,H0,H1,H2.
  exists ((q + Qmin4 (x0 * x2) (x0 * x3) (x1 * x2) (x1 * x3))*(1#2))%Q.
  split. apply middle_between. apply H3.
  exists x0,x1,x2,x3. repeat split. apply H. apply H0. apply H1. apply H2.
  apply middle_between. apply H3.
Qed.

Lemma mult_upper_open : forall (x y : R) (q : Q),
    mult_upper x y q -> exists r:Q, Qlt r q /\ mult_upper x y r.
Proof.
  intros. destruct H,H,H,H,H,H0,H1,H2.
  exists ((Qmax4 (x0 * x2) (x0 * x3) (x1 * x2) (x1 * x3)+q)*(1#2))%Q.
  split. apply middle_between. apply H3.
  exists x0,x1,x2,x3. repeat split. apply H. apply H0. apply H1. apply H2.
  apply middle_between. apply H3.
Qed.

(* If we improve the left bound from a to e,
   then the left bound of the product improves. *)
Lemma mult_improve_left_bound
  : forall a b c d e : Q,
    Qlt c d
    -> Qlt e b
    -> Qle a e
    -> Qle (Qmin4 (a*c) (a*d) (b*c) (b*d))
          (Qmin4 (e*c) (e*d) (b*c) (b*d)).
Proof.
  intros. (* 4 cases, according to which is the second Qmin4. *)
  unfold Qmin4. destruct (Qlt_le_dec (Qmin (e * c) (e * d)) (Qmin (b * c) (b * d))).
  - rewrite (Q.min_l (Qmin (e * c) (e * d)) (Qmin (b * c) (b * d))).
    2: apply Qlt_le_weak; apply q.
    (* Because e * c < Qmin (b * c) (b * d), we exclude those last 2 cases. *)
    apply (Qle_trans _ (Qmin (a * c) (a * d))). apply Q.le_min_l.
    destruct (Qlt_le_dec (e * c) (e * d)).
    + (* e*c is the Qmin4, 0<e *)
      rewrite (Q.min_l (e * c) (e * d)).
      2: apply Qlt_le_weak; apply q0.
      rewrite (Q.min_l (e * c) (e * d)) in q.
      2: apply Qlt_le_weak; apply q0. 
      destruct (Qlt_le_dec c 0).
      * (* c<0 *) exfalso. apply Q.min_glb_lt_iff in q.
        destruct q. apply (Qlt_not_le _ _ H2).
        rewrite <- (Qopp_involutive). rewrite <- (Qopp_involutive (e*c)).
        apply Qopp_le_compat. apply Qopp_lt_compat in q1.
        apply (Qmult_lt_compat_r _ _ (-c) q1) in H0.
        apply Qlt_le_weak. ring_simplify. ring_simplify in H0. apply H0.
      * apply (Qle_trans _ (a*c)). apply Q.le_min_l.
        apply Qmult_le_compat_r. apply H1. apply q1.
    + (* e*d is the Qmin4, a<=e<=0 *)
      rewrite (Q.min_r (e * c) (e * d)). 2: apply q0.
      rewrite (Q.min_r (e * c) (e * d)) in q. 2: apply q0.
      apply Q.min_le_iff. right. destruct (Qlt_le_dec d 0).
      * (* c<d<0 *) exfalso. apply Q.min_glb_lt_iff in q. destruct q.
        apply (Qlt_not_le _ _ H3).
        rewrite <- (Qopp_involutive). rewrite <- (Qopp_involutive (e*d)).
        apply Qopp_le_compat. apply Qopp_lt_compat in q1.
        apply (Qmult_lt_compat_r _ _ (-d) q1) in H0.
        apply Qlt_le_weak. ring_simplify. ring_simplify in H0. apply H0.
      * apply Qmult_le_compat_r; assumption.
  - rewrite (Q.min_r (Qmin (e * c) (e * d)) (Qmin (b * c) (b * d))).
    2: apply q. apply Q.le_min_r.
Qed.

(* If we improve the right bound from b to e,
   then the right bound of the product improves. *)
Lemma mult_improve_right_bound
  : forall a b c d e : Q,
    Qlt c d
    -> Qlt a e
    -> Qle e b
    -> Qle (Qmax4 (a*c) (a*d) (e*c) (e*d))
          (Qmax4 (a*c) (a*d) (b*c) (b*d)).
Proof.
  intros. rewrite <- Qopp_involutive.
  rewrite <- (Qopp_involutive (Qmax4 (a * c) (a * d) (b * c) (b * d))).
  apply Qopp_le_compat. rewrite <- Qmin4_opp. rewrite <- Qmin4_opp.
  setoid_replace (- (a * c))%Q with (-a * c)%Q. 2: ring.
  setoid_replace (- (a * d))%Q with (-a * d)%Q. 2: ring.
  setoid_replace (- (b * c))%Q with (-b * c)%Q. 2: ring.
  setoid_replace (- (b * d))%Q with (-b * d)%Q. 2: ring.
  setoid_replace (- (e * c))%Q with (-e * c)%Q. 2: ring.
  setoid_replace (- (e * d))%Q with (-e * d)%Q. 2: ring.
  unfold Qmin4. rewrite Q.min_comm.
  rewrite (Q.min_comm (Qmin (- a * c) (- a * d))).
  apply mult_improve_left_bound. apply H.
  rewrite <- Qopp_lt_compat. apply H0.
  apply Qopp_le_compat. apply H1.
Qed.

(* If we improve the left bound from b to e,
   then the left bound of the product improves. *)
Lemma mult_improve_left_bound_reverse
  : forall a b c d e : Q,
    Qlt c d
    -> Qlt a e
    -> Qle e b
    -> Qle (Qmin4 (a*c) (a*d) (b*c) (b*d))
          (Qmin4 (a*c) (a*d) (e*c) (e*d)).
Proof.
  intros. (* 4 cases, according to which is the second Qmin4. *)
  unfold Qmin4. destruct (Qlt_le_dec (Qmin (a * c) (a * d)) (Qmin (e * c) (e * d))).
  - rewrite (Q.min_l (Qmin (a * c) (a * d)) (Qmin (e * c) (e * d))).
    2: apply Qlt_le_weak; apply q.
    apply Q.le_min_l.
  - rewrite (Q.min_r (Qmin (a * c) (a * d)) (Qmin (e * c) (e * d))).
    2: apply q.
    (* Because a * c < Qmin (e * c) (e * d), we exclude those last 2 cases. *)
    apply (Qle_trans _ (Qmin (b * c) (b * d))). apply Q.le_min_r.
    destruct (Qlt_le_dec (e * c) (e * d)).
    + (* e*c is the Qmin4, 0<e *)
      rewrite (Q.min_l (e * c) (e * d)).
      2: apply Qlt_le_weak; apply q0.
      rewrite (Q.min_l (e * c) (e * d)) in q.
      2: apply Qlt_le_weak; apply q0. 
      destruct (Qlt_le_dec 0 c).
      * (* 0<c *) exfalso. apply Q.min_glb_iff in q.
        destruct q. apply (Qle_not_lt _ _ H2).
        apply Qmult_lt_compat_r. apply q1. apply H0.
      * apply (Qle_trans _ (b*c)). apply Q.le_min_l.
        rewrite <- (Qopp_involutive). rewrite <- (Qopp_involutive (e*c)).
        apply Qopp_le_compat. apply Qopp_le_compat in q1.
        apply (Qmult_le_compat_r _ _ (-c)) in H1. 2: apply q1.
        ring_simplify. ring_simplify in H1. apply H1.
    + (* e*d is the Qmin4, a<=e<=0, d<=0 *)
      rewrite (Q.min_r (e * c) (e * d)). 2: apply q0.
      rewrite (Q.min_r (e * c) (e * d)) in q. 2: apply q0.
      apply Q.min_glb_iff in q. destruct q.
      apply Q.min_le_iff. right. destruct (Qlt_le_dec 0 d).
      * (* 0<d *) exfalso. apply (Qle_not_lt _ _ H3).
        apply Qmult_lt_r; assumption.
      * (* c<d<=0 *)
        rewrite <- (Qopp_involutive). rewrite <- (Qopp_involutive (e*d)).
        apply Qopp_le_compat. apply Qopp_le_compat in q.
        apply (Qmult_le_compat_r _ _ (-d)) in H1.
        2: apply q.
        ring_simplify. ring_simplify in H1. apply H1.
Qed.

Lemma mult_improve_right_bound_reverse
  : forall a b c d e : Q,
    Qlt c d
    -> Qlt e b
    -> Qle a e (* a <= e < b *)
    -> Qle (Qmax4 (e*c) (e*d) (b*c) (b*d))
          (Qmax4 (a*c) (a*d) (b*c) (b*d)).
Proof.
  intros. rewrite <- Qopp_involutive.
  rewrite <- (Qopp_involutive (Qmax4 (a * c) (a * d) (b * c) (b * d))).
  apply Qopp_le_compat. rewrite <- Qmin4_opp. rewrite <- Qmin4_opp.
  setoid_replace (- (a * c))%Q with (-a * c)%Q. 2: ring.
  setoid_replace (- (a * d))%Q with (-a * d)%Q. 2: ring.
  setoid_replace (- (b * c))%Q with (-b * c)%Q. 2: ring.
  setoid_replace (- (b * d))%Q with (-b * d)%Q. 2: ring.
  setoid_replace (- (e * c))%Q with (-e * c)%Q. 2: ring.
  setoid_replace (- (e * d))%Q with (-e * d)%Q. 2: ring.
  (* -b < -e <= -a *)
  unfold Qmin4. rewrite Q.min_comm.
  rewrite (Q.min_comm (Qmin (- e * c) (- e * d))). 
  apply (mult_improve_left_bound_reverse (-b) (-a) c d (-e)).
  apply H. rewrite <- Qopp_lt_compat. apply H0.
  apply Qopp_le_compat. apply H1.
Qed.

Lemma mult_improve_both_bounds
  : forall a b c d e f : Q,
    Qlt e f
    -> Qlt c d
    -> Qle a e
    -> Qle f b
    -> (Qle (Qmin4 (a*c) (a*d) (b*c) (b*d))
           (Qmin4 (e*c) (e*d) (f*c) (f*d))
       /\ Qle (Qmax4 (e*c) (e*d) (f*c) (f*d))
             (Qmax4 (a*c) (a*d) (b*c) (b*d))).
Proof.
  split.
  - apply (Qle_trans _ (Qmin4 (e * c) (e * d) (b * c) (b * d))).
    apply mult_improve_left_bound. apply H0.
    apply (Qlt_le_trans e f b H H2). apply H1.
    apply mult_improve_left_bound_reverse. apply H0.
    apply H. apply H2.
  - apply (Qle_trans _ (Qmax4 (e * c) (e * d) (b * c) (b * d))).
    apply mult_improve_right_bound. apply H0. apply H. apply H2.
    apply mult_improve_right_bound_reverse. apply H0.
    2: apply H1. apply (Qlt_le_trans e f b H H2).
Qed.

Lemma DReal_mult_disjoint : forall (x y : R) (q : Q),
    ~ (mult_lower x y q /\ mult_upper x y q).
Proof.
  intros x y q [low up].

  destruct low,H,H,H,H. destruct up,H1,H1,H1,H1.
  assert (Qmax x2 x6 < Qmin x3 x7)%Q.
  { apply (lower_below_upper y).
    apply Q.max_case. apply (lower_proper y). apply H0. apply H2.
    apply Q.min_case. apply (upper_proper y). apply H0. apply H2. }
  assert (Qmax x0 x4 < Qmin x1 x5)%Q.
  { apply (lower_below_upper x).
    apply Q.max_case. apply (lower_proper x). apply H. apply H1.
    apply Q.min_case. apply (upper_proper x). apply H0. apply H2. }
  
  apply (Qlt_irrefl q).
  apply (Qlt_le_trans q (Qmin4 (x0 * x2) (x0 * x3) (x1 * x2) (x1 * x3))).
  apply H0.
  apply (Qle_trans _ (Qmin4 (Qmax x0 x4 * x2) (Qmax x0 x4 * x3)
                            (Qmin x1 x5 * x2) (Qmin x1 x5 * x3))).
  apply mult_improve_both_bounds. apply H4.
  apply (lower_below_upper y). apply H0. apply H0.
  apply Q.le_max_l. apply Q.le_min_l.
  rewrite <- (Qmult_comm x2). rewrite <- (Qmult_comm x2).
  rewrite <- (Qmult_comm x3). rewrite <- (Qmult_comm x3).
  rewrite Qmin4_flip.
  apply (Qle_trans _ (Qmin4 (Qmax x2 x6 * Qmax x0 x4) (Qmax x2 x6 * Qmin x1 x5)
                            (Qmin x3 x7 * Qmax x0 x4) (Qmin x3 x7 * Qmin x1 x5))).
  apply mult_improve_both_bounds. 3: apply Q.le_max_l. 3: apply Q.le_min_l.
  apply H3. apply H4.
  
  (* Switch to the right side *)
  apply (Qle_trans _ (Qmax4 (Qmax x2 x6 * Qmax x0 x4) (Qmax x2 x6 * Qmin x1 x5)
                            (Qmin x3 x7 * Qmax x0 x4) (Qmin x3 x7 * Qmin x1 x5))).
  apply Qmin4_le_max4.
  apply (Qle_trans _ (Qmax4 (x6 * Qmax x0 x4) (x6 * Qmin x1 x5)
                            (x7 * Qmax x0 x4) (x7 * Qmin x1 x5))).
  apply mult_improve_both_bounds. 3: apply Q.le_max_r. 3: apply Q.le_min_r.
  apply H3. apply H4.
  rewrite (Qmult_comm x6). rewrite (Qmult_comm x6).
  rewrite (Qmult_comm x7). rewrite (Qmult_comm x7).
  rewrite Qmax4_flip.
  apply (Qle_trans _ (Qmax4 (x4 * x6) (x4 * x7)
                            (x5 * x6) (x5 * x7))).
  apply mult_improve_both_bounds. apply H4.
  apply (lower_below_upper y). apply H2. apply H2.
  apply Q.le_max_r. apply Q.le_min_r.
  apply Qlt_le_weak. apply H2.
Qed.

(* Strictly majorate the absolute value of x by a rational number. *)
Definition DReal_bound (x : R)
  : { q : Q | upper x q /\ upper (Ropp x) q }.
Proof.
  destruct (upper_bound x). destruct (lower_bound x).
  exists (Qmax (Qabs x0) (Qabs x1)). split.
  apply (upper_le x x0). apply u.
  apply (Qle_trans x0 (Qabs x0)). apply Qle_Qabs. apply Q.le_max_l.
  simpl. apply (lower_le x _ x1). apply l.
  apply (Qle_trans _ (-Qabs x1)). apply Qopp_le_compat.
  apply Q.le_max_r. rewrite <- (Qopp_involutive x1).
  apply Qopp_le_compat. rewrite Qabs_opp. apply Qle_Qabs.
Qed. 

Lemma DReal_mult_maj_base : 
  forall x y p : Q, Qle 0 p -> 
               Qle (Qmax4 0 x y (x + y + p) - Qmin4 0 x y (x + y + p))
                   (Qabs x + Qabs y + p)%Q.
Proof.
  intros.
  (* Finish by cases on which is the min and max *)
  unfold Qmin4, Qmax4. destruct (Qlt_le_dec 0 x).
  - (* 0 < x, all min max are known. *)
    rewrite (Q.max_r 0). rewrite (Q.min_l 0).
    2: apply Qlt_le_weak; apply q.
    2: apply Qlt_le_weak; apply q.
    rewrite Qabs_pos.
    2: apply Qlt_le_weak; apply q.
    assert (y <= x + y + p)%Q.
    { rewrite (Qplus_comm x y). rewrite <- (Qplus_0_r y).
      rewrite <- (Qplus_assoc y). rewrite <- Qplus_assoc.
      apply Qplus_le_r. rewrite Qplus_0_l. rewrite <- Qplus_0_l.
      apply Qplus_le_compat. apply Qlt_le_weak. apply q. apply H. }
    rewrite (Q.max_r y). 2: apply H0.
    rewrite (Q.min_l y). 2: apply H0.
    destruct (Qlt_le_dec 0 y).
    + rewrite Q.min_l. 2: apply Qlt_le_weak; apply q0.
      unfold Qminus. rewrite Qplus_0_r.
      apply Q.max_lub_iff. split. 
      rewrite <- Qplus_0_r. rewrite <- Qplus_assoc.
      rewrite <- Qplus_assoc. apply Qplus_le_r.
      rewrite Qplus_0_l. apply (Qle_trans _ (Qabs y + 0)).
      rewrite Qplus_0_r. apply Qabs_nonneg.
      apply Qplus_le_r. apply H.
      rewrite <- Qplus_assoc. rewrite <- (Qplus_assoc x).
      apply Qplus_le_r. apply Qplus_le_compat.
      apply Qle_Qabs. apply Qle_refl.
    + rewrite Q.min_r. 2: apply q0. rewrite Qabs_neg.
      2: apply q0. unfold Qminus. rewrite Qplus_comm.
      rewrite (Qplus_comm x (-y)). rewrite <- (Qplus_assoc _ x p).
      apply Qplus_le_r. apply Q.max_lub_iff. split.
      rewrite <- (Qplus_0_r x). rewrite <- Qplus_assoc.
      apply Qplus_le_r. rewrite Qplus_0_l. apply H.
      rewrite <- Qplus_assoc. apply Qplus_le_r.
      rewrite <- (Qplus_0_l p). rewrite Qplus_assoc.
      apply Qplus_le_l. rewrite Qplus_0_r. apply q0.
  - (* x <= 0 *)
    rewrite (Q.max_l 0). rewrite (Q.min_r 0).
    2: apply q. 2: apply q.
    rewrite Qabs_neg. 2: apply q.
    destruct (Qlt_le_dec y (x + y + p)).
    + rewrite (Q.max_r y). 2: apply Qlt_le_weak; apply q0. 
      rewrite (Q.min_l y). 2: apply Qlt_le_weak; apply q0. 
      destruct (Qlt_le_dec x y).
      * rewrite Q.min_l. 2: apply Qlt_le_weak; apply q1.
        unfold Qminus. rewrite Qplus_comm. rewrite <- (Qplus_assoc _ (Qabs y)).
        apply Qplus_le_r. apply Q.max_lub_iff. split.
        rewrite <- (Qplus_0_l 0). apply Qplus_le_compat.
        apply Qabs_nonneg. apply H.
        apply Qplus_le_l. rewrite <- (Qplus_0_l (Qabs y)).
        apply Qplus_le_compat. apply q. apply Qle_Qabs.
      * rewrite Q.min_r. 2: apply q1. rewrite Qabs_neg.
        2: apply (Qle_trans y x 0 q1 q).
        rewrite (Qplus_comm (-x -y) p). unfold Qminus.
        rewrite Qplus_assoc. apply Qplus_le_l. apply Q.max_lub_iff.
        split. rewrite <- Qle_minus_iff. apply (Qle_trans x 0 p q H).
        rewrite (Qplus_comm p). apply Qplus_le_l.
        apply (Qle_trans _ (0 + 0)). apply Qplus_le_compat.
        apply q. apply (Qle_trans y x 0 q1 q).
        rewrite Qplus_0_l. apply (Qopp_le_compat x 0); apply q.
    + rewrite (Q.max_l y). 2: apply q0. 
      rewrite (Q.min_r y). 2: apply q0.
      destruct (Qlt_le_dec x (x + y + p)).
      * rewrite Q.min_l. 2: apply Qlt_le_weak; apply q1.
        unfold Qminus. rewrite Qplus_comm. rewrite <- Qplus_assoc.
        apply Qplus_le_r. apply Q.max_lub_iff. split.
        rewrite <- (Qplus_0_r 0). apply Qplus_le_compat.
        apply Qabs_nonneg. apply H.
        apply (Qle_trans y (Qabs y + 0)). rewrite Qplus_0_r.
        apply Qle_Qabs. apply Qplus_le_r. apply H.
      * rewrite Q.min_r. 2: apply q1.
        setoid_replace (Qmax 0 y - (x + y + p))%Q
          with (-x + (Qmax 0 y - y - p))%Q.
        2: ring. rewrite <- Qplus_assoc. apply Qplus_le_r.
        assert (-p <= p)%Q.
        { apply (Qplus_le_r _ _ p). rewrite Qplus_opp_r.
          apply (Qle_trans 0 (0 + p)). rewrite Qplus_0_l. apply H.
          apply Qplus_le_l. apply H. }
        destruct (Qlt_le_dec 0 y). rewrite Q.max_r.
        unfold Qminus. rewrite Qplus_opp_r. apply Qplus_le_compat.
        apply Qabs_nonneg. apply H0. apply Qlt_le_weak. apply q2.
        rewrite Q.max_l. rewrite Qabs_neg.
        unfold Qminus. rewrite Qplus_0_l. apply Qplus_le_r. apply H0.
        apply q2. apply q2.
Qed.

Lemma DReal_mult_maj : forall (a b e : Q),
    Qle 0 e ->
    Qle (Qmax4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e))
         - Qmin4 (a * b) (a * (b + e)) ((a + e) * b) ((a + e) * (b + e)))
        ((Qabs a + Qabs b + e) * e).
Proof.
  intros.
  rewrite <- (Qplus_0_r (a*b)).
  setoid_replace (a*(b+e))%Q with (a*b + a*e)%Q. 2: ring.
  setoid_replace ((a+e)*b)%Q with (a*b + b*e)%Q. 2: ring.
  setoid_replace ((a+e)*(b+e))%Q with (a*b + (a*e + b*e + e*e))%Q. 2: ring.
  rewrite plus_max4_distr_l. rewrite plus_min4_distr_l.
  setoid_replace (a * b + Qmax4 0 (a * e) (b * e) (a * e + b * e + e * e)
                  - (a * b + Qmin4 0 (a * e) (b * e) (a * e + b * e + e * e)))%Q
    with (Qmax4 0 (a * e) (b * e) (a * e + b * e + e * e)
          - (Qmin4 0 (a * e) (b * e) (a * e + b * e + e * e)))%Q.
  2: ring.
  (* Get rid of the multiplications *)
  assert (Qle 0 (e*e)).
  { rewrite <- (Qmult_0_l e). apply Qmult_le_compat_r; apply H. }
  setoid_replace ((Qabs a + Qabs b + e) * e)%Q
    with (Qabs (a*e) + Qabs (b*e) + Qabs (e*e))%Q. 
  rewrite (Qabs_pos (e*e)). 2: apply H0.
  apply DReal_mult_maj_base. apply H0.
  rewrite Qabs_Qmult. rewrite Qabs_Qmult. rewrite Qabs_Qmult.
  rewrite (Qabs_pos e H). ring.
Qed.

(* Locate both factors to locate the multiplication. *)
Lemma DReal_locate_mult
  : forall (x y : R) (eta : Q),
    Qlt 0 eta
    -> exists (eps : Q) (a b : Q),
      Qlt 0 eps
      /\ lower x a /\ upper x (a+eps) /\ lower y b /\ upper y (b+eps)
      /\ Qlt (Qmax4 (a*b) (a*(b+eps)) ((a+eps)*b) ((a+eps)*(b+eps))
             - Qmin4 (a*b) (a*(b+eps)) ((a+eps)*b) ((a+eps)*(b+eps)))
            eta.
Proof.
  intros.
  destruct (DReal_bound x) as [mx mmx].
  destruct (DReal_bound y) as [my mmy].
  (* It is enough to locate both x and y within eps to
     locate the multiplication within eta. *)
  pose (Qmin 1 (eta / ((mx+(1+1)) + (my+1) + 1))) as eps.
  assert (0 < mx + (1 + 1) + (my + 1) + 1)%Q as denomPos.
  { rewrite <- (Qplus_0_r 0). apply Qplus_lt_le_compat. 
    2: discriminate.
    rewrite <- (Qplus_0_r 0). apply Qplus_lt_le_compat. 
    apply (Qlt_trans 0 (mx + 0)). 2: apply Qplus_lt_r; reflexivity.
    rewrite Qplus_0_r. apply Qpos_above_opp.
    apply (lower_below_upper x); apply mmx.
    apply (Qle_trans 0 (my + 0)). rewrite Qplus_0_r.
    apply Qlt_le_weak. apply Qpos_above_opp.
    apply (lower_below_upper y); apply mmy.
    apply Qplus_le_r. discriminate. }
  assert (Qlt 0 eps) as epsPos.
  { apply Q.min_glb_lt_iff. split. reflexivity.
    apply Qlt_shift_div_l. apply denomPos.
    rewrite Qmult_0_l. apply H. }
  destruct (DReal_approx x eps epsPos) as [a maja].
  destruct (DReal_approx y eps epsPos) as [b majb].
  exists eps, a, b. repeat split.
  apply epsPos. apply maja. apply maja. apply majb. apply majb.
  apply (Qle_lt_trans _ ((Qabs a + Qabs b + eps) * eps)).
  apply DReal_mult_maj. apply Qlt_le_weak. apply epsPos.
  apply (Qle_lt_trans _ ((Qabs a + Qabs b + 1) * eps)).
  apply Qmult_le_r. apply epsPos. apply Qplus_le_r.
  apply Q.le_min_l.
  apply (Qle_lt_trans _ ((Qabs a + Qabs b + 1) * eta / ((mx+(1+1)) + (my+1) + 1))).
  - unfold Qdiv. rewrite <- Qmult_assoc. apply Qmult_le_l.
    2: apply Q.le_min_r.
    rewrite <- (Qplus_0_l 0). rewrite <- (Qplus_comm 1).
    apply Qplus_lt_le_compat. reflexivity.
    rewrite <- (Qplus_0_l 0). apply Qplus_le_compat; apply Qabs_nonneg.
  - apply Qlt_shift_div_r. apply denomPos.
    rewrite Qmult_comm. apply Qmult_lt_l. apply H.
    apply Qplus_lt_l. apply Qplus_lt_le_compat.
    apply (Qle_lt_trans _ (mx + 1)). 2: apply Qplus_lt_r; reflexivity.
    + apply Qabs_Qle_condition. split. 
      simpl in mmx. apply (Qplus_le_l _ _ 1).
      setoid_replace (-(mx+1)+1)%Q with (-mx)%Q.
      2: ring. apply (Qle_trans _ (a+eps)). apply Qlt_le_weak. 
      apply (lower_below_upper x). apply mmx. apply maja.
      apply Qplus_le_r. apply Q.le_min_l. apply Qlt_le_weak.
      apply (lower_below_upper x). apply maja.
      apply (upper_le x mx). apply mmx.
      rewrite <- (Qplus_0_r mx). rewrite <- Qplus_assoc.
      apply Qplus_le_r. discriminate.
    + apply Qabs_Qle_condition. split. 
      simpl in mmy. apply (Qplus_le_l _ _ 1).
      setoid_replace (-(my+1)+1)%Q with (-my)%Q.
      2: ring. apply (Qle_trans _ (b+eps)). apply Qlt_le_weak. 
      apply (lower_below_upper y). apply mmy. apply majb.
      apply Qplus_le_r. apply Q.le_min_l. apply Qlt_le_weak.
      apply (lower_below_upper y). apply majb.
      apply (upper_le y my). apply mmy.
      rewrite <- (Qplus_0_r my). rewrite <- Qplus_assoc.
      apply Qplus_le_r. discriminate.
Qed.

Lemma DReal_mult_located : forall (x y : R) (q r : Q),
    Qlt q r
    -> mult_lower x y q \/ mult_upper x y r.
Proof.
  intros. assert (0 < (r - q)*(1#2))%Q as etaPos.
  { rewrite <- (Qmult_0_l (1#2)). apply Qmult_lt_r. reflexivity.
    unfold Qminus. rewrite <- Qlt_minus_iff. apply H. }
  destruct (DReal_locate_mult x y ((r-q)*(1#2)) etaPos)
    as [eps [a [b H0]]].
  destruct H0 as [epsPos [H0 [H1 [H2 [H3 H4]]]]].
  destruct (Qlt_le_dec (a*b) ((r+q)*(1#2))).
  - right. exists a, (a+eps)%Q, b, (b+eps)%Q. 
    repeat split. apply H0. apply H1. apply H2. apply H3.
    apply (Qle_lt_trans
             _ (Qmax4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps))
                - Qmin4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps))
                + a*b)).
    + rewrite <- Qplus_0_r. unfold Qminus.
      rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
      apply Qplus_le_r. rewrite Qplus_0_l.
      rewrite Qplus_comm. rewrite <- Qle_minus_iff.
      apply (Qle_trans _ (Qmin (a*b) (a*(b+eps)))); apply Q.le_min_l.
    + apply (Qlt_trans _ ((r-q)*(1#2) + a*b)).
      apply Qplus_lt_l. apply H4.
      apply (Qplus_lt_r _ _ ((r - q) * (1 # 2))) in q0.
      setoid_replace ((r - q) * (1 # 2) + (r + q) * (1 # 2))%Q with r in q0.
      apply q0. ring.
  - left. exists a, (a+eps)%Q, b, (b+eps)%Q. 
    repeat split. apply H0. apply H1. apply H2. apply H3.
    apply (Qlt_le_trans
             _ (Qmin4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps))
                - Qmax4 (a * b) (a * (b + eps)) ((a + eps) * b) ((a + eps) * (b + eps))
                + a*b)).
    + apply (Qle_lt_trans _ (-(r-q)*(1#2) + a*b)).
      apply (Qplus_le_r _ _ (-(r - q) * (1 # 2))) in q0.
      setoid_replace (-(r - q) * (1 # 2) + (r + q) * (1 # 2))%Q with q in q0.
      apply q0. ring.
      apply Qplus_lt_l. apply (Qopp_lt_compat) in H4.
      ring_simplify. ring_simplify in H4.
      rewrite (Qplus_comm (Qmin4 (a * b) (a * (b + eps))
                                 ((a + eps) * b) ((a + eps) * (b + eps)))). 
      apply H4.
    + rewrite <- (Qplus_0_r (Qmin4 (a * b) (a * (b + eps))
                                  ((a + eps) * b) ((a + eps) * (b + eps)))).
      unfold Qminus. rewrite <- Qplus_assoc. rewrite <- Qplus_assoc.
      apply Qplus_le_r. rewrite Qplus_0_l.
      apply (Qplus_le_r _ 0 (Qmax4 (a * b) (a * (b + eps))
                                   ((a + eps) * b) ((a + eps) * (b + eps)))).
      rewrite Qplus_assoc. rewrite Qplus_opp_r. rewrite Qplus_0_l.
      rewrite Qplus_0_r.
      apply (Qle_trans _ (Qmax (a*b) (a*(b+eps)))); apply Q.le_max_l.
Qed.

Definition Rmult : R -> R -> R.
Proof.
  intros x y. apply (Build_R (mult_lower x y) (mult_upper x y)).
  - apply mult_lower_proper.
  - apply mult_upper_proper.
  - destruct (lower_bound x), (upper_bound x), (lower_bound y), (upper_bound y).
    exists (Qmin4 (x0*x2) (x0*x3) (x1*x2) (x1*x3) - 1)%Q.
    exists x0,x1,x2,x3. repeat split. exact l. exact u. exact l0.
    exact u0. rewrite <- (Qplus_0_r (Qmin4 _ _ _ _)).
    unfold Qminus. rewrite <- Qplus_assoc. apply Qplus_lt_r. reflexivity.
  - destruct (lower_bound x), (upper_bound x), (lower_bound y), (upper_bound y).
    exists (Qmax4 (x0*x2) (x0*x3) (x1*x2) (x1*x3) + 1)%Q.
    exists x0,x1,x2,x3. repeat split. apply l. apply u. apply l0.
    apply u0. rewrite <- Qplus_0_r. rewrite <- Qplus_assoc.
    apply Qplus_lt_r. reflexivity.
  - intros. destruct H0, H0, H0, H0. exists x0,x1,x2,x3. repeat split.
    apply H0. apply H0. apply H0. apply H0.
    apply (Qlt_trans _ r _ H). apply H0.
  - apply mult_lower_open.
  - intros. destruct H0, H0, H0, H0. exists x0,x1,x2,x3. repeat split.
    apply H0. apply H0. apply H0. apply H0.
    apply (Qlt_trans _ q). apply H0. apply H.
  - apply mult_upper_open.
  - apply DReal_mult_disjoint.
  - apply DReal_mult_located.
Defined.

Infix "*" := Rmult : R_scope.

Instance Rmult_comp : Proper (Req ==> Req ==> Req) Rmult.
Proof.
  intros x y Exy u v Euv.
  split ; intros q [a [b [c [d H]]]].
  - exists a, b, c, d ; setoid_rewrite <- Exy ; setoid_rewrite <- Euv ; assumption.
  - exists a, b, c, d ; setoid_rewrite -> Exy ; setoid_rewrite -> Euv ; assumption.
Qed.

(** Properties of multiplication. *)

Lemma Rmult_comm (x y : R) : (x * y == y * x)%R.
Proof.
  split ; intros q [a [b [c [d [? [? [? ?]]]]]]].
  - exists c, d, a, b. repeat split. exact H1. apply H2. exact H.
    exact H0.
    rewrite (Qmult_comm c a), (Qmult_comm d a), (Qmult_comm c b),
    (Qmult_comm d b), Qmin4_flip. apply H2.
  - exists c, d, a, b. repeat split.
    exact H1. apply H2. exact H. exact H0.
    rewrite (Qmult_comm c a), (Qmult_comm d a), (Qmult_comm c b),
    (Qmult_comm d b), Qmin4_flip. apply H2.
Qed.

Definition shrink_factor (a b : Q)
  : Qlt a b -> { q : Q | Qlt 0 q /\ Qlt q 1 /\ Qlt a (q*b) }.
Proof.
  intros. destruct (Qlt_le_dec 0 a).
  - assert (Qlt 0 b).
    { apply (Qlt_trans _ a _ q). exact H. }
    exists ((a/b+1)*(1#2)). repeat split.
    rewrite <- (Qmult_0_l (1#2)). apply Qmult_lt_r.
    reflexivity.
    apply (Qlt_le_trans 0 (0+1)). reflexivity.
    apply Qplus_le_l. rewrite <- (Qmult_0_l (/b)).
    apply Qmult_le_r. apply Qinv_lt_0_compat. exact H0.
    apply Qlt_le_weak. exact q.
    apply middle_between.
    apply (Qmult_lt_l _ _ b). exact H0. field_simplify. exact H.
    intro abs. rewrite abs in H0. apply (Qlt_irrefl 0 H0).
    apply (Qmult_lt_r _ _ (/b)).
    apply Qinv_lt_0_compat. exact H0.
    rewrite <- Qmult_assoc. rewrite Qmult_inv_r, Qmult_1_r.
    apply middle_between.
    apply (Qmult_lt_l _ _ b). exact H0. field_simplify. exact H.
    intro abs. rewrite abs in H0. apply (Qlt_irrefl 0 H0).
    intro abs. rewrite abs in H0. apply (Qlt_irrefl 0 H0).
  - exists (1#2). repeat split. 
    destruct (Qlt_le_dec 0 b). apply (Qle_lt_trans _ ((1#2)*0)).
    rewrite Qmult_0_r. exact q. apply Qmult_lt_l.
    reflexivity. exact q0. apply (Qlt_le_trans a b _ H).
    rewrite <- (Qmult_le_l _ _ 2). field_simplify.
    rewrite <- (Qplus_le_l _ _ (-b)). ring_simplify. exact q0.
    reflexivity.
Qed.

Definition expand_factor (a b : Q)
  : Qlt a b -> { q : Q | Qlt 1 q /\ Qlt a (q*b) }.
Proof.
  intros. destruct (Qlt_le_dec b 0).
  - exists ((1+a/b)*(1#2)). split. apply middle_between.
    apply Qopp_lt_compat. apply (Qmult_lt_l _ _ (-b)). 
    apply (Qplus_lt_l _ _ b). ring_simplify. exact q.
    unfold Qdiv. field_simplify.
    unfold Qdiv. field_simplify. exact H.
    apply Qlt_not_eq. exact q.
    apply Qlt_not_eq. exact q.
    apply Qopp_lt_compat. apply (Qmult_lt_l _ _ (-/b)). 
    setoid_replace (-/b) with (/-b). 2: field.
    apply Qinv_lt_0_compat.
    apply (Qplus_lt_l _ _ b). ring_simplify. exact q.
    apply Qlt_not_eq. exact q.
    field_simplify.
    setoid_replace (((1 # 2) * b + (1 # 2) * a) / b)
      with ((1+a/b)*(1#2)).
    2: field.
    apply middle_between.
    apply Qopp_lt_compat. apply (Qmult_lt_l _ _ (-b)). 
    apply (Qplus_lt_l _ _ b). ring_simplify. exact q.
    field_simplify. unfold Qdiv. field_simplify. exact H.
    apply Qlt_not_eq. exact q.
    apply Qlt_not_eq. exact q.
    apply Qlt_not_eq. exact q.
    apply Qlt_not_eq. exact q.
    apply Qlt_not_eq. exact q.
  - exists 2. split. reflexivity. apply (Qlt_le_trans a b _ H).
    apply (Qplus_le_l _ _ (-b)). ring_simplify. exact q.
Qed.

Lemma Rmult_1_l (x : R) : (1 * x == x)%R.
Proof.
  split ; intro q.
  - intros [a [b [c [d [H1 [H2 [H3 [H4 H5]]]]]]]].
    destruct (Q_dec c 0) as [[G|G]|G].
    + apply (lower_lower x q c) ; auto.
      transitivity (b * c) ; auto.
      apply (Qlt_le_trans q _ (b*c) H5).
      apply (Qle_trans _ (Qmin (b*c) (b*d))).
      apply Q.le_min_r. apply Q.le_min_l.
      setoid_replace c with (1 * c) at 2 ; [ idtac | (ring_simplify ; reflexivity) ].
      apply Qlt_mult_neg_r ; auto.
    + apply (lower_lower x q c) ; auto.
      transitivity (a * c) ; auto.
      apply (Qlt_le_trans q _ (a*c) H5).
      apply (Qle_trans _ (Qmin (a*c) (a*d))).
      apply Q.le_min_l. apply Q.le_min_l.
      setoid_replace c with (1 * c) at 2 ; [ idtac | (ring_simplify ; reflexivity) ].
      apply Qmult_lt_compat_r ; assumption.
    + rewrite G in * |- *.
      apply (lower_lower x q 0) ; auto.
      apply (Qlt_le_trans _ (a * 0)) ; auto.
      ring_simplify.
      apply (Qlt_le_trans q _ _ H5).
      apply (Qle_trans _ (Qmin (b*0) (b*d))).
      apply Q.le_min_r. setoid_replace (b*0) with 0. apply Q.le_min_l.
      ring. ring_simplify. discriminate.
  - intros. destruct (upper_bound x), (lower_open x q H).
    destruct (shrink_factor q x1), (expand_factor q x1).
    apply H0. apply H0. apply H0.
    exists x2,x3,x1, (Qmax x0 (1+(/x2)*Qabs q)). repeat split.
    apply a. apply a0. apply H0. apply (upper_le x x0). apply u. apply Q.le_max_l.
    apply Q.min_glb_lt. apply Q.min_glb_lt. 3: apply Q.min_glb_lt.
    apply a. apply (Qlt_le_trans _ (x2*(1+(/x2)*Qabs q))).
    field_simplify. apply (Qle_lt_trans q (0+Qabs q)).
    rewrite Qplus_0_l. apply Qle_Qabs. apply Qplus_lt_l. apply a.
    destruct a. intro abs. rewrite abs in H1. exact (Qlt_irrefl 0 H1).
    apply Qmult_le_compat_l. apply Q.le_max_r.
    apply Qlt_le_weak. apply a. apply a0.
    apply (Qlt_le_trans _ (x3*x0)).
    apply (Qlt_trans _ (x3*x1)). apply a0.
    apply Qmult_lt_l. apply (Qlt_trans 0 1). reflexivity. apply a0.
    apply (lower_below_upper x). apply H0. exact u.
    apply Qmult_le_l. apply (Qlt_trans 0 1). reflexivity. apply a0.
    apply Q.le_max_l.
Qed.

Lemma Rmult_1_r (x : R) : (x * 1 == x)%R.
Proof.
  assert(H:= (Rmult_comm x 1)).
  rewrite H.
  apply Rmult_1_l.
Qed.

(* Distributivity *)

Lemma Ropp_mult_distr_l : forall r1 r2, (- (r1 * r2) == - r1 * r2)%R.
Proof.
  split.
  - intros q [a [b [c [d H]]]]. simpl. 
    exists (-b)%Q, (-a)%Q, c, d. repeat split.
    simpl. rewrite Qopp_involutive. apply H.
    simpl. rewrite Qopp_involutive. apply H.
    apply H. apply H.
    setoid_replace (-b*c) with (-(b*c)). 2: ring.
    setoid_replace (-b*d) with (-(b*d)). 2: ring.
    setoid_replace (-a*c) with (-(a*c)). 2: ring.
    setoid_replace (-a*d) with (-(a*d)). 2: ring.
    rewrite Qmin4_opp.
    rewrite <- (Qplus_lt_l _ _ (-q+Qmax4 (b * c) (b * d) (a * c) (a * d))).
    ring_simplify. unfold Qmax4. rewrite Q.max_comm.
    setoid_replace (-1 * q) with (-q). apply H. ring.
  - intros q [a [b [c [d H]]]]. simpl. simpl in H.
    exists (-b)%Q, (-a)%Q, c, d. repeat split.
    apply H. apply H. apply H. apply H.
    setoid_replace (-b*c) with (-(b*c)). 2: ring.
    setoid_replace (-b*d) with (-(b*d)). 2: ring.
    setoid_replace (-a*c) with (-(a*c)). 2: ring.
    setoid_replace (-a*d) with (-(a*d)). 2: ring.
    rewrite Qmax4_opp.
    rewrite <- (Qplus_lt_l _ _ (q+Qmin4 (b * c) (b * d) (a * c) (a * d))).
    ring_simplify. unfold Qmin4. rewrite Q.min_comm. apply H.
Qed.

Lemma Ropp_mult_distr_r : forall r1 r2, (- (r1 * r2) == r1 * -r2)%R.
Proof.
  intros. rewrite (Rmult_comm r1), (Rmult_comm r1).
  apply Ropp_mult_distr_l.
Qed.

Lemma Qmul_min_distr_l: forall n m p : Q,
    Qle 0 p -> (Qmin (p * n) (p * m) == (p * Qmin n m))%Q.
Proof.
  intros. destruct (Qlt_le_dec n m).
  rewrite Q.min_l. rewrite Q.min_l. reflexivity.
  apply Qlt_le_weak. exact q. apply Qmult_le_compat_l.
  apply Qlt_le_weak. exact q. exact H.
  rewrite Q.min_r. rewrite Q.min_r. reflexivity.
  exact q. apply Qmult_le_compat_l.
  exact q. exact H. 
Qed.

Lemma Rmult_plus_distr_r_le : forall (x y z : R), ((x * y) + (x * z) <= x * (y + z))%R.
Proof.
  intros x y z q [r [s [H [H0 H1]]]]. 
  destruct H0,H0,H0,H0,H0,H2,H3,H4.
  destruct H1,H1,H1,H1,H1,H6,H7,H8.
  pose (Qmax x0 x4) as a. pose (Qmin x1 x5) as b.
  exists a, b, (x2+x6), (x3+x7). repeat split.
  unfold a. apply Q.max_case.
  intros. apply (lower_proper x y0 x8). symmetry. exact H10. exact H11.
  apply H0. apply H1.
  apply Q.min_case.
  intros. apply (upper_proper x y0 x8). symmetry. exact H10. exact H11.
  exact H2. apply H6.
  apply sum_interval_lower; assumption.
  apply sum_interval_upper; assumption.
  apply (Qlt_le_trans _ (r+s) _ H). clear H. clear q.
  assert (r < Qmin4 (a*x2) (a*x3) (b*x2) (b*x3)).
  { apply (Qlt_le_trans _ _ _ H5). apply mult_improve_both_bounds.
    apply Q.min_glb_lt. apply Q.max_lub_lt.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper x); assumption.
    apply Q.max_lub_lt.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper y); assumption.
    apply Q.le_max_l. apply Q.le_min_l. }
  clear H5.
  assert (s < Qmin4 (a*x6) (a*x7) (b*x6) (b*x7)).
  { apply (Qlt_le_trans _ _ _ H9). apply mult_improve_both_bounds.
    apply Q.min_glb_lt. apply Q.max_lub_lt.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper x); assumption.
    apply Q.max_lub_lt.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper x); assumption.
    apply (lower_below_upper z); assumption.
    apply Q.le_max_r. apply Q.le_min_r. }
  clear H9.
  do 4 rewrite Qmult_plus_distr_r.
  apply (Qle_trans _ (Qmin4 (a * x2) (a * x3) (b * x2) (b * x3)
                      + Qmin4 (a * x6) (a * x7) (b * x6) (b * x7))).
  apply Qplus_le_compat; apply Qlt_le_weak; assumption.
  apply Q.min_glb_iff. split.
  apply Q.min_glb_iff. split.
  apply Qplus_le_compat. apply (Qle_trans _ (Qmin (a * x2) (a * x3))).
  apply Q.le_min_l. apply Q.le_min_l.
  apply (Qle_trans _ (Qmin (a * x6) (a * x7))).
  apply Q.le_min_l. apply Q.le_min_l.
  apply Qplus_le_compat. apply (Qle_trans _ (Qmin (a * x2) (a * x3))).
  apply Q.le_min_l. apply Q.le_min_r.
  apply (Qle_trans _ (Qmin (a * x6) (a * x7))).
  apply Q.le_min_l. apply Q.le_min_r.
  apply Q.min_glb_iff. split.
  apply Qplus_le_compat. apply (Qle_trans _ (Qmin (b * x2) (b * x3))).
  apply Q.le_min_r. apply Q.le_min_l.
  apply (Qle_trans _ (Qmin (b * x6) (b * x7))).
  apply Q.le_min_r. apply Q.le_min_l.
  apply Qplus_le_compat. apply (Qle_trans _ (Qmin (b * x2) (b * x3))).
  apply Q.le_min_r. apply Q.le_min_r.
  apply (Qle_trans _ (Qmin (b * x6) (b * x7))).
  apply Q.le_min_r. apply Q.le_min_r.
Qed.

Lemma Rmult_plus_distr_r (x y z : R) : (x * (y + z) == (x * y) + (x * z))%R.
Proof.
  split. 2: apply Rmult_plus_distr_r_le. 
  pose proof (Rmult_plus_distr_r_le x (y+z)%R (-z)%R).
  setoid_replace (y + z - z)%R with y in H. 
  apply (Rplus_le_compat_r (x*z)%R) in H.
  setoid_replace (x * (y + z) + x * - z + x * z)%R
    with (x * (y+z))%R in H. exact H.
  rewrite <- Ropp_mult_distr_r, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
  reflexivity. unfold Rminus.
  rewrite Rplus_assoc, Rplus_opp_r, Rplus_0_r. reflexivity.
Qed.

Lemma Rmult_plus_distr_l (x y z : R) : ((x + y) * z == (x * z) + (y * z))%R.
Proof.
  intros. rewrite Rmult_comm, (Rmult_comm x), (Rmult_comm y).
  apply Rmult_plus_distr_r.
Qed.

(* Associativity *)

Definition split_pos (x : R) :
  { ab : R*R | (x == fst ab - snd ab)%R /\ Rlt 0 (fst ab) /\ Rlt 0 (snd ab) }.
Proof.
  destruct (upper_bound x) as [q qmaj].
  exists (pair (1+Qabs q)%R (1+Qabs q - x)%R).
  simpl. split. unfold Rminus.
  rewrite Ropp_plus_distr, Ropp_involutive, <- Rplus_assoc, Rplus_opp_r, Rplus_0_l. 
  reflexivity.
  split. exists (1#2). split. reflexivity. simpl.
  exists (3#4), (-1#5). repeat split.
  apply (Qlt_le_trans _ 0). reflexivity. apply Qabs_nonneg.
  unfold Rminus. apply (Rplus_lt_reg_r x).
  rewrite Rplus_0_l, Rplus_assoc, Rplus_opp_l, Rplus_0_r.
  exists q. split. exact qmaj.
  exists (1#2), (Qabs q - (1#4)). split. 
  apply (Qle_lt_trans _ (Qabs q)). apply Qle_Qabs.
  apply (Qplus_lt_l _ _ (-Qabs q)). ring_simplify. reflexivity.
  split. reflexivity. simpl. unfold Qminus.
  rewrite <- (Qplus_0_r (Qabs q)), <- Qplus_assoc, Qplus_lt_r. reflexivity.
Qed.

Lemma mult_lower_pos : forall x y : R,
    Rlt 0 x
    -> Rlt 0 y
    -> (forall q:Q, mult_lower x y q
                    <-> exists r s :Q, Qlt 0 r /\ Qlt 0 s /\ lower x r /\ lower y s
                                       /\ q < r*s).
Proof.
  split.
  - intros [a [b [c [d H1]]]]. 
    destruct H,H0. exists (Qmax a x0), (Qmax c x1).
    split. apply (Qlt_le_trans _ x0). apply H. apply Q.le_max_r.
    split. apply (Qlt_le_trans _ x1). apply H0. apply Q.le_max_r.
    split. apply Q.max_case. intros. apply (lower_proper x x2).
    exact H2. exact H3. apply H1. apply H.
    split. apply Q.max_case. intros. apply (lower_proper y x2).
    exact H2. exact H3. apply H1. apply H0.
    apply (Qlt_le_trans _ (Qmin4 (a * c) (a * d) (b * c) (b * d))).
    apply H1. 
    apply (Qle_trans _ (Qmin4 (Qmax a x0 * c) (Qmax a x0 * d) (b * c) (b * d))).
    apply (mult_improve_left_bound a b c d (Qmax a x0)).
    apply (lower_below_upper y). apply H1. apply H1.
    apply (lower_below_upper x). apply Q.max_case. intros. apply (lower_proper x x2).
    exact H2. exact H3. apply H1. apply H. apply H1.
    apply Q.le_max_l. apply (Qle_trans _ (Qmax a x0 * c)).
    apply (Qle_trans _ (Qmin (Qmax a x0 * c) (Qmax a x0 * d))).
    apply Q.le_min_l. apply Q.le_min_l.
    apply Qmult_le_l. apply (Qlt_le_trans _ x0). apply H. apply Q.le_max_r.
    apply Q.le_max_l.
  - intros [r [s H1]]. destruct (upper_bound x), (upper_bound y).
    assert (r*s <= r*x1).
    { apply Qmult_le_l. apply H1.
      apply Qlt_le_weak, (lower_below_upper y). apply H1. exact u0. }
    exists r,x0,s,x1. repeat split. apply H1. exact u. apply H1. exact u0.
    apply (Qlt_le_trans _ (r*s)). apply H1.
    unfold Qmin4. rewrite Q.min_l. rewrite Q.min_l. apply Qle_refl.
    apply H2. apply (Qle_trans _ (r*s)). apply Q.le_min_l.
    apply Q.min_glb_iff. split.
    apply Qmult_le_r. apply H1.
    apply Qlt_le_weak, (lower_below_upper x). apply H1. exact u.
    apply (Qle_trans _ _ _ H2). apply Qmult_le_r.
    apply (Qlt_trans 0 s). apply H1. 
    apply (lower_below_upper y). apply H1. exact u0.
    apply Qlt_le_weak, (lower_below_upper x). apply H1. exact u.
Qed.

Lemma Rmult_lt_0_compat : forall r1 r2:R, (0 < r1 -> 0 < r2 -> 0 < r1 * r2)%R.
Proof.
  intros. destruct H,H0. exists (x*x0). split.
  simpl. rewrite <- (Qmult_0_l x0). apply Qmult_lt_r.
  apply H0. apply H. apply mult_lower_pos.
  exists x. exact H. exists x0. exact H0.
  destruct (lower_open r1 x). apply H.
  exists x1, x0. repeat split. apply (Qlt_trans _ x). apply H. apply H1.
  apply H0. apply H1. apply H0.
  apply Qmult_lt_r. apply H0. apply H1.
Qed.

Lemma Rmult_assoc_pos : forall (x y z : R),
    Rlt 0 x
    -> Rlt 0 y
    -> Rlt 0 z
    -> ((x * y) * z == x * (y * z))%R.
Proof.
  split.
  - intros q H2. apply mult_lower_pos in H2.
    3: exact H1. 2: exact (Rmult_lt_0_compat x y H H0).
    destruct H2 as [r [s [H2 [H3 [H4 H5]]]]].
    apply (mult_lower_pos x y H H0) in H4.
    destruct H4,H4. 
    apply mult_lower_pos. exact H. exact (Rmult_lt_0_compat y z H0 H1).
    exists x0, (x1*s). repeat split.
    apply H4. rewrite <- (Qmult_0_l s).
    apply Qmult_lt_r. exact H3. apply H4. apply H4.
    apply mult_lower_pos. exact H0. exact H1.
    destruct (lower_open y x1). apply H4.
    exists x2,s. repeat split. apply (Qlt_trans _ x1). apply H4. apply H6.
    exact H3. apply H6. apply H5. apply Qmult_lt_r. exact H3. apply H6.
    apply (Qlt_trans _ (r*s)). apply H5.
    apply (Qlt_le_trans _ ((x0*x1)*s)).
    apply Qmult_lt_r. exact H3. apply H4. rewrite Qmult_assoc. apply Qle_refl.
  - intros q H2. apply mult_lower_pos in H2.
    2: exact H. 2: exact (Rmult_lt_0_compat y z H0 H1).
    destruct H2 as [r [s [H2 [H3 [H4 [H5 H6]]]]]].
    apply (mult_lower_pos y z H0 H1) in H5.
    destruct H5,H5. 
    apply mult_lower_pos. 2: exact H1. exact (Rmult_lt_0_compat x y H H0).
    exists (r*x0), x1. repeat split.
    2: apply H5. rewrite <- (Qmult_0_l x0).
    apply Qmult_lt_r. apply H5. exact H2.
    apply mult_lower_pos. exact H. exact H0.
    destruct (lower_open y x0). apply H5.
    exists r,x2. repeat split. exact H2. apply (Qlt_trans _ x0).
    apply H5. apply H7.
    exact H4. apply H7. apply Qmult_lt_l. exact H2. apply H7.
    apply H5.
    apply (Qlt_trans _ (r*s)). apply H6.
    rewrite <- Qmult_assoc. apply Qmult_lt_l. exact H2. apply H5.
Qed.

Lemma Rmult_assoc (x y z : R) : ((x * y) * z == x * (y * z))%R.
Proof.
  destruct (split_pos x), (split_pos y), (split_pos z), x0, x1, x2.
  simpl in a,a0,a1. destruct a,a0,a1,H0,H2,H4. rewrite H,H1,H3.
  unfold Rminus. repeat rewrite Rmult_plus_distr_l.
  repeat rewrite Rmult_plus_distr_r.
  repeat rewrite Rmult_plus_distr_l.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite <- Ropp_mult_distr_r.
  repeat rewrite <- Ropp_mult_distr_l.
  repeat rewrite Rmult_assoc_pos; try assumption.
  repeat rewrite Ropp_involutive.
  apply Rplus_comp. do 2 rewrite Rplus_assoc.
  apply Rplus_comp. reflexivity.
  do 2 rewrite <- Rplus_assoc. apply Rplus_comp. 2: reflexivity.
  rewrite Rplus_comm. reflexivity.
  do 2 rewrite Rplus_assoc.
  apply Rplus_comp. reflexivity.
  do 2 rewrite <- Rplus_assoc. apply Rplus_comp. 2: reflexivity.
  rewrite Rplus_comm. reflexivity.
Qed.

(* Inverse. *)

Theorem Rinv_apart_0 : forall x : R, ({ y | x * y == 1 } -> x ## 0)%R.
Proof.
  intros x [y E].
  todo.
Qed.


(* The inverse of a real which is apart from zero. *)
Definition Rinv : forall x : R, (x ## 0 -> R)%R.
Proof.
  intros x H.
  refine {|
      lower := (fun q => (exists r, r < 0 /\ upper x r /\ 1 < q * r) \/
                         (exists r, lower x 0 /\ upper x r /\ q * r < 1)) ;
      upper := (fun q => (exists r, lower x r /\ upper x 0 /\ q * r < 1) \/
                         (exists r, 0 < r /\ lower x r /\ 1 < q * r))
    |}.
  - todo.
  - todo. 
  - todo. 
  - todo. 
  - todo. 
  - todo. 
  - todo. 
  - todo. 
  - todo. 
  - todo. 
Defined.

(*
Theorem R_pos_field : forall x : R, (0 < x  -> { y | x * y == 1 })%R.
Proof.
  intros x H.
  - exists (Rinv_pos x H).
    split ; intro q ; split.
    + intros [a [b [c [d [H1 [H2 [[r [R1 [R2 R3]]] [[s [S1 [S2 S3]]] [H5 [H6 [H7 H8]]]]]]]]]]].
      simpl.
      destruct (Qlt_le_dec 0 c) as [G|G].
      * transitivity (a * c) ; auto.
        transitivity (c * r) ; auto.
        rewrite Qmult_comm.
        apply Qmult_lt_l ; auto.
        apply (lower_below_upper x) ; assumption.
      * transitivity (b * c) ; auto.
        apply (Qle_lt_trans _ 0) ; [idtac | reflexivity].
        setoid_replace 0 with (b * 0) ; [ idtac | (symmetry ; apply Qmult_0_r)].
        apply Qmult_le_compat_l ; auto.
        apply Qlt_le_weak, (lower_below_upper x) ; auto.
    + todo.
    + todo.
    + todo.
Qed.
*)

Lemma Qmult_le_neg_pos_pos : forall q r, q <= 0 -> 0 <= r -> q * r <= 0.
Proof.
  intros q r H G.
  setoid_replace 0 with (0 * r).
  + now apply Qmult_le_compat_r.
  + reflexivity.
Qed.

Theorem R_field : forall x : R, (x ## 0  -> { y | x * y == 1 })%R.
Proof.
  intros x H.
  exists (Rinv x H).
  split ; intro q.
  - intros [a [b [c [d [H1 [H2 [H3 [H4 H5]]]]]]]].
    simpl.
    destruct H3 as [[r [R1 [R2 R3]]]|[r [R1 [R2 R3]]]] ;
    destruct H4 as [[s [S1 [S2 S3]]]|[s [S1 [S2 S3]]]].
    + destruct (Qlt_le_dec d 0) as [G|G].
      * transitivity (b * d).
        apply (Qlt_le_trans q _ _ H5).
        apply (Qle_trans _ (Qmin (b*c) (b*d))).
        apply Q.le_min_r. apply Q.le_min_r. 
        transitivity (d * s).
        setoid_rewrite (Qmult_comm d s).
        apply Qlt_mult_neg_r ; auto.
        apply (lower_below_upper x) ; auto. exact S3.
      * transitivity (a * d).
        apply (Qlt_le_trans q _ _ H5).
        apply (Qle_trans _ (Qmin (a*c) (a*d))).
        apply Q.le_min_l. apply Q.le_min_r. 
        apply (Qle_lt_trans _ 0) ; [ idtac | reflexivity ].
        apply Qmult_le_neg_pos_pos ; auto.
        apply Qlt_le_weak, (lower_below_upper x) ; auto.
    + exfalso.
      apply (Qlt_irrefl 0), (lower_below_upper x).
      * apply (lower_lower x 0 s) ; auto.
      * apply (upper_upper x r 0) ; auto.
   + exfalso.
     apply (Qlt_irrefl 0), (lower_below_upper x) ; auto.
   + destruct (Qlt_le_dec 0 c) as [G|G].
     * transitivity (a * c).
       apply (Qlt_le_trans q _ _ H5).
       apply (Qle_trans _ (Qmin (a*c) (a*d))).
       apply Q.le_min_l. apply Q.le_min_l. 
       transitivity (c * r).
       setoid_rewrite (Qmult_comm c r).
       apply Qmult_lt_compat_r ; auto.
       apply (lower_below_upper x) ; auto. exact R3.
     * transitivity (b * c).
       apply (Qlt_le_trans q _ _ H5).
       apply (Qle_trans _ (Qmin (b*c) (b*d))).
       apply Q.le_min_r. apply Q.le_min_l. 
       apply (Qle_lt_trans _ 0) ; [ idtac | reflexivity ].
       setoid_rewrite (Qmult_comm b c).
       apply Qmult_le_neg_pos_pos ; auto.
       apply Qlt_le_weak, (lower_below_upper x) ; auto.
  - todo.
Qed.

Theorem R_inv_apart_0 : forall x : R, ({y | x * y == 1} -> x ## 0)%R.
Proof.
  intros x [y [F G]].
  assert (H : 1#2 < 1) ; [ reflexivity | idtac ].
  destruct ((G (1#2)) H) as [a [b [c [d [L1 [L2 [L3 [L4 L5]]]]]]]].
  destruct (Q_dec c 0) as [[?|?]|?].
  - left ; exists b ; split ; auto.
    simpl ; transitivity ((1 # 2) / c).
    + todo.
    + todo.
  - right ; exists a ; split ; auto.
    simpl. transitivity ((1 # 2) / c).
    + todo.
    + todo.
  - absurd (1 # 2 < 0).
    + discriminate.
    + setoid_replace 0 with (a * c) ; auto.
      apply (Qlt_le_trans _ _ _ L5).
      apply (Qle_trans _ (Qmin (a*c) (a*d))).
      apply Q.le_min_l. apply Q.le_min_l. 
      setoid_rewrite q ; ring_simplify ; reflexivity.
Qed.
