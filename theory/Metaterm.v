From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding.

Inductive mtrm : Type :=
| mBVar : nat -> mtrm
| mFVar : atom -> mtrm
| mMVar : atom -> list atom -> mtrm
| mApp : mtrm -> mtrm -> mtrm
| mLam : mtrm -> mtrm
| mESub : mtrm -> mtrm -> mtrm.

Fixpoint mfvs (t : mtrm) : list atom :=
  match t with
  | mBVar _ => []
  | mFVar x => [x]
  | mMVar x d => x :: d
  | mApp a b => mfvs a ++ mfvs b
  | mLam a => mfvs a
  | mESub a b => mfvs a ++ mfvs b
  end.

Fixpoint lift_m (k : nat) (t : mtrm) : mtrm :=
  match t with
  | mBVar n => if Nat.ltb n k then mBVar n else mBVar (S n)
  | mFVar x => mFVar x
  | mMVar x d => mMVar x d
  | mApp a b => mApp (lift_m k a) (lift_m k b)
  | mLam a => mLam (lift_m (S k) a)
  | mESub a b => mESub (lift_m (S k) a) (lift_m k b)
  end.

Fixpoint open_rec_m (k : nat) (u : mtrm) (t : mtrm) : mtrm :=
  match t with
  | mBVar n => if Nat.eqb n k then lift_m k u else mBVar n
  | mFVar x => mFVar x
  | mMVar x d => mMVar x d
  | mApp a b => mApp (open_rec_m k u a) (open_rec_m k u b)
  | mLam a => mLam (open_rec_m (S k) u a)
  | mESub a b => mESub (open_rec_m (S k) u a) (open_rec_m k u b)
  end.

Fixpoint close_rec_m (x : atom) (k : nat) (t : mtrm) : mtrm :=
  match t with
  | mBVar n => mBVar n
  | mFVar y => if Nat.eqb y x then mBVar k else mFVar y
  | mMVar y d => mMVar y d
  | mApp a b => mApp (close_rec_m x k a) (close_rec_m x k b)
  | mLam a => mLam (close_rec_m x (S k) a)
  | mESub a b => mESub (close_rec_m x (S k) a) (close_rec_m x k b)
  end.

Fixpoint of_trm (t : trm) : mtrm :=
  match t with
  | BVar n => mBVar n
  | FVar x => mFVar x
  | App a b => mApp (of_trm a) (of_trm b)
  | Lam a => mLam (of_trm a)
  | ESub a b => mESub (of_trm a) (of_trm b)
  end.

Lemma of_trm_fvs : forall t, mfvs (of_trm t) = fvs t.
Proof. induction t; simpl; [reflexivity | reflexivity | rewrite IHt1, IHt2; reflexivity | rewrite IHt; reflexivity | rewrite IHt1, IHt2; reflexivity]. Qed.

Lemma of_trm_lift : forall t k, of_trm (lift k t) = lift_m k (of_trm t).
Proof.
  induction t; intros k; simpl.
  - destruct (Nat.ltb n k); reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma of_trm_open : forall t k u,
  of_trm (open_rec k u t) = open_rec_m k (of_trm u) (of_trm t).
Proof.
  induction t; intros k u; simpl.
  - destruct (Nat.eqb n k) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst n. simpl. rewrite of_trm_lift. reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma of_trm_close : forall t x k,
  of_trm (close_rec x k t) = close_rec_m x k (of_trm t).
Proof.
  induction t; intros x k; simpl.
  - reflexivity.
  - destruct (Nat.eqb a x); reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma of_trm_injective : forall t t', of_trm t = of_trm t' -> t = t'.
Proof.
  induction t; intros t' H; destruct t'; simpl in H; try discriminate.
  - injection H as H. f_equal. exact H.
  - injection H as H. f_equal. exact H.
  - injection H as H1 H2. f_equal; [apply IHt1 | apply IHt2]; assumption.
  - injection H as H. f_equal. apply IHt. exact H.
  - injection H as H1 H2. f_equal; [apply IHt1 | apply IHt2]; assumption.
Qed.

Print Assumptions of_trm_fvs.
Print Assumptions of_trm_lift.
Print Assumptions of_trm_open.
Print Assumptions of_trm_close.
Print Assumptions of_trm_injective.

Lemma mfvs_lift_m : forall t k, mfvs (lift_m k t) = mfvs t.
Proof.
  induction t; intros k; simpl.
  - destruct (Nat.ltb n k); reflexivity.
  - reflexivity.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma mfvs_close_m : forall t x k y, In y (mfvs (close_rec_m x k t)) -> In y (mfvs t).
Proof.
  induction t; intros x k y H; simpl in *.
  - destruct H.
  - destruct (Nat.eqb a x) eqn:E.
    + destruct H.
    + destruct H as [Hy | Hf]. subst y. simpl. left. reflexivity. destruct Hf.
  - exact H.
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply (IHt1 x k y). exact H.
    + right. apply (IHt2 x k y). exact H.
  - apply (IHt x (S k) y). exact H.
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply (IHt1 x (S k) y). exact H.
    + right. apply (IHt2 x k y). exact H.
Qed.

Lemma mfvs_open_m : forall t k u y,
  In y (mfvs (open_rec_m k u t)) -> In y (mfvs u) \/ In y (mfvs t).
Proof.
  induction t; intros k u y H; simpl in *.
  - destruct (Nat.eqb n k) eqn:E.
    + apply Nat.eqb_eq in E. subst n. simpl in H.
      left. rewrite <- (mfvs_lift_m u k). exact H.
    + simpl in H. destruct H.
  - right. exact H.
  - right. exact H.
  - apply in_app_iff in H as [H|H].
    + destruct (IHt1 k u y H) as [Hl|Hr]. left; exact Hl. right; apply in_app_iff; left; exact Hr.
    + destruct (IHt2 k u y H) as [Hl|Hr]. left; exact Hl. right; apply in_app_iff; right; exact Hr.
  - destruct (IHt (S k) u y H) as [Hl|Hr]. left; exact Hl. right; exact Hr.
  - apply in_app_iff in H as [H|H].
    + destruct (IHt1 (S k) u y H) as [Hl|Hr]. left; exact Hl. right; apply in_app_iff; left; exact Hr.
    + destruct (IHt2 k u y H) as [Hl|Hr]. left; exact Hl. right; apply in_app_iff; right; exact Hr.
Qed.

Print Assumptions mfvs_lift_m.
Print Assumptions mfvs_close_m.
Print Assumptions mfvs_open_m.
