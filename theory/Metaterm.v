From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction Closure Metatheory.

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

Inductive mctx : Type :=
| mGHole : mctx
| mGAppL : mctx -> mtrm -> mctx
| mGAppR : mtrm -> mctx -> mctx
| mGLam : mctx -> mctx
| mGESubL : mctx -> mtrm -> mctx
| mGESubR : mtrm -> mctx -> mctx.

Fixpoint mplug (C : mctx) (t : mtrm) : mtrm :=
  match C with
  | mGHole => t
  | mGAppL C1 u => mApp (mplug C1 t) u
  | mGAppR u C1 => mApp u (mplug C1 t)
  | mGLam C1 => mLam (mplug C1 t)
  | mGESubL C1 u => mESub (mplug C1 t) u
  | mGESubR t1 C1 => mESub t1 (mplug C1 t)
  end.

Fixpoint mctx_of (C : ctx) : mctx :=
  match C with
  | GHole => mGHole
  | GAppL C1 u => mGAppL (mctx_of C1) (of_trm u)
  | GAppR u C1 => mGAppR (of_trm u) (mctx_of C1)
  | GLam C1 => mGLam (mctx_of C1)
  | GESubL C1 u => mGESubL (mctx_of C1) (of_trm u)
  | GESubR t1 C1 => mGESubR (of_trm t1) (mctx_of C1)
  end.

Lemma of_trm_plug : forall C t, of_trm (plug C t) = mplug (mctx_of C) (of_trm t).
Proof.
  induction C; intros a; simpl; try reflexivity; rewrite IHC; reflexivity.
Qed.

Fixpoint moccurs (n : nat) (t : mtrm) : bool :=
  match t with
  | mBVar m => Nat.eqb m n
  | mFVar _ => false
  | mMVar _ _ => false
  | mApp a b => moccurs n a || moccurs n b
  | mLam a => moccurs (S n) a
  | mESub a b => moccurs (S n) a || moccurs n b
  end.

Definition moccurs0 (t : mtrm) : bool := moccurs 0 t.

Inductive mzctx : Type :=
| mZTop : mzctx
| mZAppL : mzctx -> mtrm -> mzctx
| mZAppR : mtrm -> mzctx -> mzctx
| mZLam : mzctx -> mzctx
| mZESubL : mzctx -> mtrm -> mzctx
| mZESubR : mtrm -> mzctx -> mzctx.

Fixpoint mzfill (C : mzctx) (k : nat) : mtrm :=
  match C with
  | mZTop => mBVar k
  | mZAppL C1 u => mApp (mzfill C1 k) u
  | mZAppR u C1 => mApp u (mzfill C1 k)
  | mZLam C1 => mLam (mzfill C1 (S k))
  | mZESubL C1 u => mESub (mzfill C1 (S k)) u
  | mZESubR t1 C1 => mESub t1 (mzfill C1 k)
  end.

Fixpoint mzplug_lift (C : mzctx) (k : nat) (t : mtrm) : mtrm :=
  match C with
  | mZTop => lift_m k t
  | mZAppL C1 u => mApp (mzplug_lift C1 k t) u
  | mZAppR u C1 => mApp u (mzplug_lift C1 k t)
  | mZLam C1 => mLam (mzplug_lift C1 (S k) t)
  | mZESubL C1 u => mESub (mzplug_lift C1 (S k) t) u
  | mZESubR t1 C1 => mESub t1 (mzplug_lift C1 k t)
  end.

Fixpoint mzdecs (t : mtrm) (k : nat) : list mzctx :=
  match t with
  | mBVar n => if Nat.eqb n k then [mZTop] else []
  | mFVar _ => []
  | mMVar _ _ => []
  | mApp a b => map (fun C => mZAppL C b) (mzdecs a k) ++ map (fun C => mZAppR a C) (mzdecs b k)
  | mLam a => map mZLam (mzdecs a (S k))
  | mESub a b => map (fun C => mZESubL C b) (mzdecs a (S k)) ++ map (fun C => mZESubR a C) (mzdecs b k)
  end.

Inductive mred : mtrm -> mtrm -> Prop :=
| mred_emb : forall t t', red1 t t' -> mred (of_trm t) (of_trm t')
| mred_ctx : forall C t t', mred t t' -> mred (mplug C t) (mplug C t')
| mred_B : forall body u, mred (mApp (mLam body) u) (mESub body u)
| mred_gc : forall body u, moccurs0 body = false -> mred (mESub body u) body
| mred_r : forall C body u, mzfill C 0 = body ->
    mred (mESub body u) (mESub (mzplug_lift C 0 u) u).

Lemma mred_of_red1 : forall t t', red1 t t' -> mred (of_trm t) (of_trm t').
Proof. intros. apply mred_emb. exact H. Qed.

Lemma mred_context : forall C t t', mred t t' -> mred (mplug C t) (mplug C t').
Proof. intros. apply mred_ctx. exact H. Qed.

Lemma mred_term_context : forall C t t',
  red1 t t' -> mred (of_trm (plug C t)) (of_trm (plug C t')).
Proof.
  intros. rewrite of_trm_plug, of_trm_plug.
  apply mred_ctx. apply mred_emb. exact H.
Qed.

Print Assumptions of_trm_plug.
Print Assumptions mred_of_red1.
Print Assumptions mred_context.
Print Assumptions mred_term_context.

Lemma of_trm_moccurs : forall t k, moccurs k (of_trm t) = occurs k t.
Proof.
  induction t; intros k; simpl; try reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - rewrite IHt. reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma of_trm_moccurs0 : forall t, moccurs0 (of_trm t) = occurs0 t.
Proof. intros. apply of_trm_moccurs. Qed.

Lemma mred_B_intro : forall body u, mred (mApp (mLam body) u) (mESub body u).
Proof. intros. apply mred_B. Qed.

Lemma mred_gc_intro : forall body u, moccurs0 body = false -> mred (mESub body u) body.
Proof. intros. apply mred_gc. exact H. Qed.

Print Assumptions of_trm_moccurs.
Print Assumptions of_trm_moccurs0.

Lemma mred_r_intro : forall C body u, mzfill C 0 = body ->
  mred (mESub body u) (mESub (mzplug_lift C 0 u) u).
Proof. intros. apply mred_r. exact H. Qed.

Print Assumptions mred_r_intro.

Inductive Plus_m (R : mtrm -> mtrm -> Prop) : mtrm -> mtrm -> Prop :=
| plusm1 : forall t u, R t u -> Plus_m R t u
| plusmS : forall t u v, R t u -> Plus_m R u v -> Plus_m R t v.

Lemma Plus_mred_of_Plus_red1 : forall a b,
  Plus red1 a b -> Plus_m mred (of_trm a) (of_trm b).
Proof.
  intros a b H. induction H as [a0 b0 HR | a0 b0 u0 HR HP IH].
  - apply plusm1. apply mred_emb. exact HR.
  - apply plusmS with (u := of_trm b0).
    + apply mred_emb. exact HR.
    + exact IH.
Qed.

Lemma mred_full_comp_pure : forall body u,
  Plus_m mred (mESub (of_trm body) (of_trm u)) (of_trm (open_rec 0 u body)).
Proof.
  intros body u.
  change (Plus_m mred (of_trm (ESub body u)) (of_trm (open_rec 0 u body))).
  apply Plus_mred_of_Plus_red1. apply lemma_2_2_full_comp.
Qed.

Lemma mred_plus_one : forall a b, red1 a b -> Plus_m mred (of_trm a) (of_trm b).
Proof. intros. apply plusm1. apply mred_emb. exact H. Qed.

Print Assumptions Plus_mred_of_Plus_red1.
Print Assumptions mred_full_comp_pure.
Print Assumptions mred_plus_one.
