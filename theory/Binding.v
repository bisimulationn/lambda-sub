From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer.

Fixpoint lc_at (d : nat) (t : trm) : Prop :=
  match t with
  | BVar n => n < d
  | FVar _ => True
  | App a b => lc_at d a /\ lc_at d b
  | Lam a => lc_at (S d) a
  | ESub a b => lc_at (S d) a /\ lc_at d b
  end.

Definition lc (t : trm) : Prop := lc_at 0 t.

Lemma fvs_lift : forall t k, fvs (lift k t) = fvs t.
Proof.
  induction t; intros k; simpl.
  - destruct (Nat.ltb n k); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma fvs_lift_many : forall n t k, fvs (lift_many n k t) = fvs t.
Proof.
  intros n t. revert n. induction t; intros nshift k; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma lift_many_one : forall t k, lift_many 1 k t = lift k t.
Proof.
  induction t; intros k; simpl.
  - destruct (Nat.ltb n k); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma lift_lc : forall t d, lc_at d t -> lift d t = t.
Proof.
  induction t; intros d H; simpl in *.
  - apply Nat.ltb_lt in H. rewrite H. reflexivity.
  - reflexivity.
  - destruct H as [Ha Hb]. rewrite (IHt1 d Ha), (IHt2 d Hb). reflexivity.
  - rewrite (IHt (S d) H). reflexivity.
  - destruct H as [Ha Hb]. rewrite (IHt1 (S d) Ha), (IHt2 d Hb). reflexivity.
Qed.

Lemma fvs_lower : forall t k, fvs (lower k t) = fvs t.
Proof.
  induction t; intros k; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Print Assumptions fvs_lower.

Lemma lift_0_lc : forall t, lc t -> lift 0 t = t.
Proof. intros t H. apply lift_lc. exact H. Qed.

Lemma open_rec_bvar : forall k u, open_rec k u (BVar k) = lift_many (S k) 0 u.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma close_rec_fvar : forall x k, close_rec x k (FVar x) = BVar k.
Proof. intros. simpl. rewrite Nat.eqb_refl. reflexivity. Qed.

Lemma open_rec_occurs_false : forall t u k, occurs k t = false -> open_rec k u t = t.
Proof.
  induction t; intros u k H; simpl in *.
  - rewrite H. reflexivity.
  - reflexivity.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 u k Ha), (IHt2 u k Hb). reflexivity.
  - rewrite (IHt u (S k) H). reflexivity.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 u (S k) Ha), (IHt2 u k Hb). reflexivity.
Qed.

Lemma close_rec_notin : forall t x k, ~ In x (fvs t) -> close_rec x k t = t.
Proof.
  induction t; intros x k H; simpl in *.
  - reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst a. exfalso. apply H. simpl. left. reflexivity.
    + reflexivity.
  - assert (Ha : ~ In x (fvs t1)) by (intro Hi; apply H; apply in_app_iff; left; exact Hi).
    assert (Hb : ~ In x (fvs t2)) by (intro Hi; apply H; apply in_app_iff; right; exact Hi).
    rewrite (IHt1 x k Ha), (IHt2 x k Hb). reflexivity.
  - rewrite (IHt x (S k) H). reflexivity.
  - assert (Ha : ~ In x (fvs t1)) by (intro Hi; apply H; apply in_app_iff; left; exact Hi).
    assert (Hb : ~ In x (fvs t2)) by (intro Hi; apply H; apply in_app_iff; right; exact Hi).
    rewrite (IHt1 x (S k) Ha), (IHt2 x k Hb). reflexivity.
Qed.

Lemma close_rec_fvs : forall t x k y, In y (fvs (close_rec x k t)) -> In y (fvs t).
Proof.
  induction t; intros x k y H; simpl in *.
  - destruct H.
  - destruct (Nat.eqb a x) eqn:E.
    + destruct H.
    + destruct H as [Hy | Hf]. subst y. simpl. left. reflexivity. destruct Hf.
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply (IHt1 x k y). exact H.
    + right. apply (IHt2 x k y). exact H.
  - apply (IHt x (S k) y). exact H.
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply (IHt1 x (S k) y). exact H.
    + right. apply (IHt2 x k y). exact H.
Qed.

Lemma open_rec_bvar_neq : forall n k u, n <> k -> open_rec k u (BVar n) = BVar n.
Proof.
  intros n k u H. simpl. destruct (Nat.eqb n k) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma open_rec_fvs : forall t u k y, In y (fvs (open_rec k u t)) -> In y (fvs u) \/ In y (fvs t).
Proof.
  induction t; intros u k y H.
  - destruct (Nat.eqb n k) eqn:E.
    + apply Nat.eqb_eq in E. subst n. rewrite (open_rec_bvar k u) in H.
      left. rewrite <- (fvs_lift_many (S k) u 0). exact H.
    + apply Nat.eqb_neq in E. rewrite (open_rec_bvar_neq n k u E) in H.
      simpl in H. destruct H.
  - simpl in H. right. exact H.
  - simpl in H. apply in_app_iff in H as [H|H].
    + destruct (IHt1 u k y H) as [Hl|Hr]. left. exact Hl. right. apply in_app_iff. left. exact Hr.
    + destruct (IHt2 u k y H) as [Hl|Hr]. left. exact Hl. right. apply in_app_iff. right. exact Hr.
  - simpl in H. destruct (IHt u (S k) y H) as [Hl|Hr]. left. exact Hl. right. exact Hr.
  - simpl in H. apply in_app_iff in H as [H|H].
    + destruct (IHt1 u (S k) y H) as [Hl|Hr]. left. exact Hl. right. apply in_app_iff. left. exact Hr.
    + destruct (IHt2 u k y H) as [Hl|Hr]. left. exact Hl. right. apply in_app_iff. right. exact Hr.
Qed.

Lemma open_close : forall t x k, occurs k t = false -> open_rec k (FVar x) (close_rec x k t) = t.
Proof.
  induction t; intros x k H; simpl in *.
  - rewrite H. reflexivity.
  - destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst a. rewrite open_rec_bvar. reflexivity.
    + reflexivity.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 x k Ha), (IHt2 x k Hb). reflexivity.
  - rewrite (IHt x (S k) H). reflexivity.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 x (S k) Ha), (IHt2 x k Hb). reflexivity.
Qed.

Lemma subst_fvar_self : forall x u, lc u -> subst x u (FVar x) = u.
Proof.
  intros x u Hu. unfold subst. simpl. rewrite Nat.eqb_refl. simpl.
  rewrite lift_many_one.
  apply lift_0_lc. exact Hu.
Qed.

Lemma subst_fvar_other : forall x y u, y <> x -> subst x u (FVar y) = FVar y.
Proof.
  intros x y u Hxy. unfold subst. simpl. destruct (Nat.eqb y x) eqn:E.
  - apply Nat.eqb_eq in E. contradiction.
  - reflexivity.
Qed.

Lemma subst_fvs : forall x u t y, In y (fvs (subst x u t)) -> In y (fvs u) \/ In y (fvs t).
Proof.
  intros x u t y H. unfold subst in H.
  apply open_rec_fvs in H. destruct H as [H|H]. left. exact H. right.
  apply close_rec_fvs in H. exact H.
Qed.

Print Assumptions fvs_lift.
Print Assumptions lift_lc.
Print Assumptions open_rec_occurs_false.
Print Assumptions close_rec_notin.
Print Assumptions close_rec_fvs.
Print Assumptions open_rec_fvs.
Print Assumptions open_close.
Print Assumptions subst_fvar_self.
Print Assumptions subst_fvar_other.
Print Assumptions subst_fvs.

Lemma lift_many_lc_at : forall t amount d k,
  lc_at d t -> k <= d -> lc_at (amount + d) (lift_many amount k t).
Proof.
  induction t; intros amount d k Hlc Hkd; simpl in *.
  - destruct (Nat.ltb n k) eqn:E.
    + apply Nat.ltb_lt in E. lia.
    + lia.
  - exact I.
  - destruct Hlc as [Ha Hb]. split; [apply IHt1 | apply IHt2]; assumption.
  - replace (S (amount + d)) with (amount + S d) by lia.
    apply IHt; [exact Hlc | lia].
  - destruct Hlc as [Ha Hb]. split.
    + replace (S (amount + d)) with (amount + S d) by lia.
      apply IHt1; [exact Ha | lia].
    + apply IHt2; assumption.
Qed.

Lemma lower_lc_at : forall t d k,
  lc_at (S d) t -> occurs k t = false -> k <= d -> lc_at d (lower k t).
Proof.
  induction t; intros d k Hlc Ho Hkd; simpl in *.
  - apply Nat.eqb_neq in Ho. destruct (Nat.ltb k n) eqn:E.
    + apply Nat.ltb_lt in E. lia.
    + apply Nat.ltb_ge in E. lia.
  - exact I.
  - destruct Hlc as [Ha Hb]. apply orb_false_iff in Ho as [Hoa Hob].
    split; [apply IHt1 | apply IHt2]; assumption.
  - apply IHt; [exact Hlc | exact Ho | lia].
  - destruct Hlc as [Ha Hb]. apply orb_false_iff in Ho as [Hoa Hob]. split.
    + apply IHt1; [exact Ha | exact Hoa | lia].
    + apply IHt2; assumption.
Qed.

Print Assumptions fvs_lift_many.
Print Assumptions lift_many_one.
Print Assumptions lift_many_lc_at.
Print Assumptions lower_lc_at.
