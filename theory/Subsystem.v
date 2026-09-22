From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction.

Inductive red_sub_root : trm -> trm -> Prop :=
| rs_gc : forall body u, occurs0 body = false -> red_sub_root (ESub body u) body
| rs_r : forall C body u, zfill C 0 = body ->
    red_sub_root (ESub body u) (ESub (zplug_lift C 0 u) u).

Inductive red_sub : trm -> trm -> Prop :=
| red_sub_base : forall t t', red_sub_root t t' -> red_sub t t'
| red_sub_ctx : forall C t t', red_sub t t' -> red_sub (plug C t) (plug C t').

Lemma red_sub_root_to_red1 : forall t t', red_sub_root t t' -> red1 t t'.
Proof.
  intros t t' H. destruct H.
  - exists RGc. apply red1r_root. apply rGc. exact H.
  - exists RR. apply red1r_root. apply rR. exact H.
Qed.

Lemma red_sub_to_red1 : forall t t', red_sub t t' -> red1 t t'.
Proof.
  intros t t' H. induction H.
  - apply red_sub_root_to_red1. exact H.
  - destruct IHred_sub as [r Hr]. exists r. apply rctx. exact Hr.
Qed.

Lemma red_sub_context : forall C t t', red_sub t t' -> red_sub (plug C t) (plug C t').
Proof. intros. apply red_sub_ctx. exact H. Qed.

Lemma red_sub_gc : forall body u, occurs0 body = false -> red_sub (ESub body u) body.
Proof. intros. apply red_sub_base. apply rs_gc. exact H. Qed.

Lemma red_sub_r : forall C body u, zfill C 0 = body ->
  red_sub (ESub body u) (ESub (zplug_lift C 0 u) u).
Proof. intros. apply red_sub_base. apply rs_r. exact H. Qed.

Print Assumptions red_sub_root_to_red1.
Print Assumptions red_sub_to_red1.
Print Assumptions red_sub_context.

Lemma occurs_zfill : forall C k, occurs k (zfill C k) = true.
Proof.
  induction C; intros k; simpl.
  - rewrite Nat.eqb_refl. reflexivity.
  - rewrite IHC. reflexivity.
  - rewrite IHC. rewrite orb_true_r. reflexivity.
  - rewrite (IHC (S k)). reflexivity.
  - rewrite (IHC (S k)). reflexivity.
  - rewrite IHC. rewrite orb_true_r. reflexivity.
Qed.

Lemma zfill_occurs0 : forall C body, zfill C 0 = body -> occurs0 body = true.
Proof. intros C body H. rewrite <- H. apply occurs_zfill. Qed.

Lemma R_Gc_disjoint : forall body, occurs0 body = false -> ~ (exists C, zfill C 0 = body).
Proof.
  intros body Hf [C HC]. apply zfill_occurs0 in HC.
  rewrite Hf in HC. discriminate HC.
Qed.

Print Assumptions occurs_zfill.
Print Assumptions zfill_occurs0.
Print Assumptions R_Gc_disjoint.
