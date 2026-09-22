From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction.

Inductive Plus (R : trm -> trm -> Prop) : trm -> trm -> Prop :=
| plus1 : forall t u, R t u -> Plus R t u
| plusS : forall t u v, R t u -> Plus R u v -> Plus R t v.

Lemma Plus_red1_context : forall C a b, Plus red1 a b -> Plus red1 (plug C a) (plug C b).
Proof.
  intros C a b H. induction H.
  - destruct H as [r Hr]. apply plus1. exists r. apply rctx. exact Hr.
  - destruct H as [r Hr]. apply plusS with (u := plug C u).
    + exists r. apply rctx. exact Hr.
    + exact IHPlus.
Qed.

Fixpoint occurs_count (n : nat) (t : trm) : nat :=
  match t with
  | BVar m => if Nat.eqb m n then 1 else 0
  | FVar _ => 0
  | App a b => occurs_count n a + occurs_count n b
  | Lam a => occurs_count (S n) a
  | ESub a b => occurs_count (S n) a + occurs_count n b
  end.

Lemma occurs_count_zero : forall t k, occurs_count k t = 0 -> occurs k t = false.
Proof.
  induction t; intros k H; simpl in *.
  - destruct (Nat.eqb n k) eqn:E; [discriminate H | reflexivity].
  - reflexivity.
  - assert (Ha : occurs_count k t1 = 0) by lia.
    assert (Hb : occurs_count k t2 = 0) by lia.
    rewrite (IHt1 k Ha), (IHt2 k Hb). reflexivity.
  - apply IHt. exact H.
  - assert (Ha : occurs_count (S k) t1 = 0) by lia.
    assert (Hb : occurs_count k t2 = 0) by lia.
    rewrite (IHt1 (S k) Ha), (IHt2 k Hb). reflexivity.
Qed.

Lemma occurs_count_false : forall t k, occurs k t = false -> occurs_count k t = 0.
Proof.
  induction t; intros k H; simpl in *.
  - rewrite H. reflexivity.
  - reflexivity.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 k Ha), (IHt2 k Hb). reflexivity.
  - apply IHt. exact H.
  - apply orb_false_iff in H as [Ha Hb].
    rewrite (IHt1 (S k) Ha), (IHt2 k Hb). reflexivity.
Qed.

Lemma occurs_count_pos : forall t n, occurs n t = true -> occurs_count n t > 0.
Proof.
  intros t n H. destruct (Nat.eq_dec (occurs_count n t) 0) as [Hz|Hnz].
  - exfalso. apply occurs_count_zero in Hz. rewrite Hz in H. discriminate H.
  - lia.
Qed.

Lemma occurs_lift_self : forall t k, occurs k (lift k t) = false.
Proof.
  induction t; intros k; simpl.
  - destruct (Nat.ltb n k) eqn:E.
    + apply Nat.ltb_lt in E. apply Nat.eqb_neq. lia.
    + apply Nat.ltb_ge in E. apply Nat.eqb_neq. lia.
  - reflexivity.
  - rewrite IHt1, IHt2. reflexivity.
  - apply IHt.
  - rewrite IHt1, IHt2. reflexivity.
Qed.

Lemma zdecs_nonempty : forall t k, occurs k t = true -> exists C, In C (zdecs t k).
Proof.
  induction t; intros k H; simpl in *.
  - destruct (Nat.eqb n k) eqn:E.
    + exists ZTop. simpl. left. reflexivity.
    + discriminate H.
  - discriminate H.
  - apply orb_true_iff in H as [H|H].
    + destruct (IHt1 k H) as [C HC]. exists (ZAppL C t2). simpl.
      apply in_app_iff. left. apply in_map_iff. exists C. split. reflexivity. exact HC.
    + destruct (IHt2 k H) as [C HC]. exists (ZAppR t1 C). simpl.
      apply in_app_iff. right. apply in_map_iff. exists C. split. reflexivity. exact HC.
  - destruct (IHt (S k) H) as [C HC]. exists (ZLam C). simpl.
    apply in_map_iff. exists C. split. reflexivity. exact HC.
  - apply orb_true_iff in H as [H|H].
    + destruct (IHt1 (S k) H) as [C HC]. exists (ZESubL C t2). simpl.
      apply in_app_iff. left. apply in_map_iff. exists C. split. reflexivity. exact HC.
    + destruct (IHt2 k H) as [C HC]. exists (ZESubR t1 C). simpl.
      apply in_app_iff. right. apply in_map_iff. exists C. split. reflexivity. exact HC.
Qed.

Lemma occurs_count_zfill_plug : forall C k u,
  occurs_count k (zfill C k) = S (occurs_count k (zplug_lift C k u)).
Proof.
  induction C; intros k u; simpl.
  - rewrite Nat.eqb_refl. simpl.
    rewrite (occurs_count_false (lift k u) k (occurs_lift_self u k)). reflexivity.
  - rewrite (IHC k u). reflexivity.
  - rewrite (IHC k u). rewrite Nat.add_succ_r. reflexivity.
  - rewrite (IHC (S k) u). reflexivity.
  - rewrite (IHC (S k) u). reflexivity.
  - rewrite (IHC k u). rewrite Nat.add_succ_r. reflexivity.
Qed.

Lemma open_rec_zplug_lift : forall C k u,
  open_rec k u (zplug_lift C k u) = open_rec k u (zfill C k).
Proof.
  induction C; intros k u; simpl.
  - rewrite (open_rec_occurs_false (lift k u) u k (occurs_lift_self u k)).
    rewrite Nat.eqb_refl. reflexivity.
  - rewrite (IHC k u). reflexivity.
  - rewrite (IHC k u). reflexivity.
  - rewrite (IHC (S k) u). reflexivity.
  - rewrite (IHC (S k) u). reflexivity.
  - rewrite (IHC k u). reflexivity.
Qed.

Lemma full_comp_aux : forall n body u, occurs_count 0 body <= n ->
  Plus red1 (ESub body u) (open_rec 0 u body).
Proof.
  induction n as [| n IH]; intros body u Hn.
  - assert (Hc : occurs_count 0 body = 0) by lia.
    assert (Ho : occurs0 body = false) by (apply occurs_count_zero; exact Hc).
    rewrite (open_rec_occurs_false body u 0 Ho).
    apply plus1. exists RGc. apply red1r_root. apply rGc. exact Ho.
  - destruct (occurs0 body) eqn:E.
    + destruct (zdecs_nonempty body 0 E) as [C HC].
      assert (Hbody : zfill C 0 = body) by (apply zdecs_sound; exact HC).
      assert (Hlt : occurs_count 0 (zplug_lift C 0 u) < occurs_count 0 body).
      { rewrite <- Hbody. rewrite (occurs_count_zfill_plug C 0 u). lia. }
      assert (Hle : occurs_count 0 (zplug_lift C 0 u) <= n) by lia.
      apply plusS with (u := ESub (zplug_lift C 0 u) u).
      * exists RR. apply red1r_root. apply rR. exact Hbody.
      * rewrite <- Hbody. rewrite <- (open_rec_zplug_lift C 0 u).
        apply IH. exact Hle.
    + rewrite (open_rec_occurs_false body u 0 E).
      apply plus1. exists RGc. apply red1r_root. apply rGc. exact E.
Qed.

Lemma lemma_2_2_full_comp : forall body u, Plus red1 (ESub body u) (open_rec 0 u body).
Proof. intros. apply (full_comp_aux (occurs_count 0 body) body u). lia. Qed.

Lemma fvs_zplug_lift : forall C k u y,
  In y (fvs (zplug_lift C k u)) -> In y (fvs u) \/ In y (fvs (zfill C k)).
Proof.
  induction C; intros k u y H; simpl in *.
  - left. rewrite <- (fvs_lift u k). exact H.
  - apply in_app_iff in H as [H|H].
    + destruct (IHC k u y H) as [Hl|Hr]. left; exact Hl.
      right; apply in_app_iff; left; exact Hr.
    + right; apply in_app_iff; right; exact H.
  - apply in_app_iff in H as [H|H].
    + right; apply in_app_iff; left; exact H.
    + destruct (IHC k u y H) as [Hl|Hr]. left; exact Hl.
      right; apply in_app_iff; right; exact Hr.
  - destruct (IHC (S k) u y H) as [Hl|Hr]. left; exact Hl. right; exact Hr.
  - apply in_app_iff in H as [H|H].
    + destruct (IHC (S k) u y H) as [Hl|Hr]. left; exact Hl.
      right; apply in_app_iff; left; exact Hr.
    + right; apply in_app_iff; right; exact H.
  - apply in_app_iff in H as [H|H].
    + right; apply in_app_iff; left; exact H.
    + destruct (IHC k u y H) as [Hl|Hr]. left; exact Hl.
      right; apply in_app_iff; right; exact Hr.
Qed.

Lemma plug_fv_mono : forall C a s, incl (fvs a) (fvs s) -> incl (fvs (plug C a)) (fvs (plug C s)).
Proof.
  induction C; intros a s H; unfold incl in *; simpl in *.
  - apply H.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff; left; apply (IHC a s H); exact Hy.
    + apply in_app_iff; right; exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff; left; exact Hy.
    + apply in_app_iff; right; apply (IHC a s H); exact Hy.
  - intros y Hy. apply (IHC a s H); exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff; left; apply (IHC a s H); exact Hy.
    + apply in_app_iff; right; exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff; left; exact Hy.
    + apply in_app_iff; right; apply (IHC a s H); exact Hy.
Qed.

Lemma red1_root_fv : forall r t t', red1_root r t t' -> incl (fvs t') (fvs t).
Proof.
  intros r t t' HR. destruct HR.
  - simpl. unfold incl. intros y Hy. exact Hy.
  - simpl. unfold incl. intros y Hy. apply in_app_iff. left. exact Hy.
  - simpl. unfold incl. intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + destruct (fvs_zplug_lift C 0 u y Hy) as [Hu|Hb].
      * apply in_app_iff. right. exact Hu.
      * apply in_app_iff. left. rewrite <- H. exact Hb.
    + apply in_app_iff. right. exact Hy.
Qed.

Lemma red1r_fv : forall r a b, red1r r a b -> incl (fvs b) (fvs a).
Proof.
  intros r a b H. induction H.
  - apply red1_root_fv with (r := r). assumption.
  - apply plug_fv_mono. assumption.
Qed.

Lemma lemma_2_1_fv_preserved : forall t t', red1 t t' -> incl (fvs t') (fvs t).
Proof. intros t t' [r Hr]. apply red1r_fv with r. exact Hr. Qed.

Inductive beta1 : trm -> trm -> Prop :=
| beta_root : forall body u, beta1 (App (Lam body) u) (open_rec 0 u body)
| beta_ctx : forall C t t', beta1 t t' -> beta1 (plug C t) (plug C t').

Lemma lemma_2_3_beta_sim : forall a b, beta1 a b -> Plus red1 a b.
Proof.
  intros a b H. induction H.
  - apply plusS with (u := ESub body u).
    + exists RB. apply red1r_root. apply rB.
    + apply lemma_2_2_full_comp.
  - apply Plus_red1_context. exact IHbeta1.
Qed.

Print Assumptions Plus_red1_context.
Print Assumptions occurs_count_zero.
Print Assumptions occurs_count_false.
Print Assumptions occurs_count_pos.
Print Assumptions occurs_lift_self.
Print Assumptions zdecs_nonempty.
Print Assumptions occurs_count_zfill_plug.
Print Assumptions open_rec_zplug_lift.
Print Assumptions lemma_2_2_full_comp.
Print Assumptions fvs_zplug_lift.
Print Assumptions plug_fv_mono.
Print Assumptions red1_root_fv.
Print Assumptions red1r_fv.
Print Assumptions lemma_2_1_fv_preserved.
Print Assumptions lemma_2_3_beta_sim.
