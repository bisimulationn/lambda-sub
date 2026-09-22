From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From Stdlib Require Import Wf_nat.
From LambdaSub Require Import ExecReducer Binding Reduction Metatheory Closure.

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

Lemma Star_red_sub_context : forall C t t', Star red_sub t t' -> Star red_sub (plug C t) (plug C t').
Proof.
  intros C t t' H. induction H.
  - apply star_refl.
  - apply star_step with (u := plug C u).
    + apply red_sub_context. exact H.
    + exact IHStar.
Qed.

Lemma full_comp_aux_sub : forall n body u, occurs_count 0 body <= n ->
  Plus red_sub (ESub body u) (open_rec 0 u body).
Proof.
  induction n as [| n IH]; intros body u Hn.
  - assert (Hc : occurs_count 0 body = 0) by lia.
    assert (Ho : occurs0 body = false) by (apply occurs_count_zero; exact Hc).
    rewrite (open_rec_occurs_false body u 0 Ho).
    apply plus1. apply red_sub_gc. exact Ho.
  - destruct (occurs0 body) eqn:E.
    + destruct (zdecs_nonempty body 0 E) as [C HC].
      assert (Hbody : zfill C 0 = body) by (apply zdecs_sound; exact HC).
      assert (Hlt : occurs_count 0 (zplug_lift C 0 u) < occurs_count 0 body).
      { rewrite <- Hbody. rewrite (occurs_count_zfill_plug C 0 u). lia. }
      assert (Hle : occurs_count 0 (zplug_lift C 0 u) <= n) by lia.
      apply plusS with (u := ESub (zplug_lift C 0 u) u).
      * apply red_sub_r. exact Hbody.
      * rewrite <- Hbody. rewrite <- (open_rec_zplug_lift C 0 u).
        apply IH. exact Hle.
    + rewrite (open_rec_occurs_false body u 0 E).
      apply plus1. apply red_sub_gc. exact E.
Qed.

Lemma plus_red_sub_full_comp : forall body u, Plus red_sub (ESub body u) (open_rec 0 u body).
Proof. intros. apply (full_comp_aux_sub (occurs_count 0 body) body u). lia. Qed.

Lemma star_red_sub_full_comp : forall body u, Star red_sub (ESub body u) (open_rec 0 u body).
Proof. intros. apply Plus_to_Star. apply plus_red_sub_full_comp. Qed.

Print Assumptions Star_red_sub_context.
Print Assumptions plus_red_sub_full_comp.
Print Assumptions star_red_sub_full_comp.

Fixpoint es_count (t : trm) : nat :=
  match t with
  | BVar _ | FVar _ => 0
  | App a b => es_count a + es_count b
  | Lam a => es_count a
  | ESub a b => S (es_count a + es_count b)
  end.

Inductive red_gc : trm -> trm -> Prop :=
| rgc_root : forall body u, occurs0 body = false -> red_gc (ESub body u) body
| rgc_ctx : forall C t t', red_gc t t' -> red_gc (plug C t) (plug C t').

Lemma es_count_plug_mono : forall C t t',
  es_count t' < es_count t -> es_count (plug C t') < es_count (plug C t).
Proof.
  induction C; intros a b H; simpl.
  - exact H.
  - pose proof (IHC a b H) as IH; lia.
  - pose proof (IHC a b H) as IH; lia.
  - pose proof (IHC a b H) as IH; lia.
  - pose proof (IHC a b H) as IH; lia.
  - pose proof (IHC a b H) as IH; lia.
Qed.

Lemma red_gc_measure : forall a b, red_gc a b -> es_count b < es_count a.
Proof.
  intros a b H. induction H.
  - simpl. lia.
  - apply es_count_plug_mono. exact IHred_gc.
Qed.

Lemma red_gc_terminates : forall t, Acc (fun x y => red_gc y x) t.
Proof.
  assert (H : forall n t, es_count t = n -> Acc (fun x y => red_gc y x) t).
  { intro n. induction n as [n IH] using lt_wf_ind.
    intros t E. constructor. intros y Hy.
    apply (IH (es_count y)).
    - pose proof (red_gc_measure t y Hy). lia.
    - reflexivity. }
  intros t. apply (H (es_count t) t). reflexivity.
Qed.

Lemma red_gc_to_red_sub : forall a b, red_gc a b -> red_sub a b.
Proof.
  intros a b H. induction H.
  - apply red_sub_gc. exact H.
  - apply red_sub_ctx. exact IHred_gc.
Qed.

Print Assumptions es_count_plug_mono.
Print Assumptions red_gc_measure.
Print Assumptions red_gc_terminates.
Print Assumptions red_gc_to_red_sub.
