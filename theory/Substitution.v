From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding.

Lemma open_rec_app : forall k u a b,
  open_rec k u (App a b) = App (open_rec k u a) (open_rec k u b).
Proof. reflexivity. Qed.

Lemma open_rec_lam : forall k u a,
  open_rec k u (Lam a) = Lam (open_rec (S k) u a).
Proof. reflexivity. Qed.

Lemma open_rec_esub : forall k u a b,
  open_rec k u (ESub a b) = ESub (open_rec (S k) u a) (open_rec k u b).
Proof. reflexivity. Qed.

Lemma close_rec_app : forall x k a b,
  close_rec x k (App a b) = App (close_rec x k a) (close_rec x k b).
Proof. reflexivity. Qed.

Lemma close_rec_lam : forall x k a,
  close_rec x k (Lam a) = Lam (close_rec x (S k) a).
Proof. reflexivity. Qed.

Lemma close_rec_esub : forall x k a b,
  close_rec x k (ESub a b) = ESub (close_rec x (S k) a) (close_rec x k b).
Proof. reflexivity. Qed.

Lemma subst_app : forall x u a b,
  subst x u (App a b) = App (subst x u a) (subst x u b).
Proof. reflexivity. Qed.

Lemma subst_lam : forall x u a,
  subst x u (Lam a) = Lam (open_rec 1 u (close_rec x 1 a)).
Proof. reflexivity. Qed.

Lemma subst_esub : forall x u a b,
  subst x u (ESub a b) = ESub (open_rec 1 u (close_rec x 1 a)) (subst x u b).
Proof. reflexivity. Qed.

Lemma subst_notin : forall x u t,
  ~ In x (fvs t) -> occurs 0 t = false -> subst x u t = t.
Proof.
  intros x u t Hx Ho. unfold subst.
  rewrite (close_rec_notin t x 0 Hx).
  apply open_rec_occurs_false. exact Ho.
Qed.

Lemma subst_lc_self : forall x u, lc u -> subst x u (FVar x) = u.
Proof. intros. apply subst_fvar_self. exact H. Qed.

Lemma subst_other : forall x y u, y <> x -> subst x u (FVar y) = FVar y.
Proof. intros. apply subst_fvar_other. exact H. Qed.

Print Assumptions open_rec_app.
Print Assumptions open_rec_lam.
Print Assumptions open_rec_esub.
Print Assumptions close_rec_app.
Print Assumptions close_rec_lam.
Print Assumptions close_rec_esub.
Print Assumptions subst_app.
Print Assumptions subst_lam.
Print Assumptions subst_esub.
Print Assumptions subst_notin.
Print Assumptions subst_lc_self.
Print Assumptions subst_other.

Lemma open_rec_lc_atom : forall t k x, lc_at k t -> open_rec k (FVar x) t = t.
Proof.
  induction t; intros k x H; simpl in *.
  - destruct (Nat.eqb n k) eqn:E; [| reflexivity].
    apply Nat.eqb_eq in E. subst n. exfalso. lia.
  - reflexivity.
  - destruct H as [Ha Hb]. rewrite (IHt1 k x Ha), (IHt2 k x Hb). reflexivity.
  - rewrite (IHt (S k) x H). reflexivity.
  - destruct H as [Ha Hb]. rewrite (IHt1 (S k) x Ha), (IHt2 k x Hb). reflexivity.
Qed.

Lemma open_rec_lc : forall t x, lc t -> open_rec 0 (FVar x) t = t.
Proof. intros. apply open_rec_lc_atom. exact H. Qed.

Print Assumptions open_rec_lc_atom.
Print Assumptions open_rec_lc.
