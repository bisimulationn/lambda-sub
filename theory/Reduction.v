From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer.

Fixpoint zfill (C : zctx) (k : nat) : trm :=
  match C with
  | ZTop => BVar k
  | ZAppL C1 u => App (zfill C1 k) u
  | ZAppR u C1 => App u (zfill C1 k)
  | ZLam C1 => Lam (zfill C1 (S k))
  | ZESubL C1 u => ESub (zfill C1 (S k)) u
  | ZESubR t1 C1 => ESub t1 (zfill C1 k)
  end.

Lemma zdecs_sound : forall t k C, In C (zdecs t k) -> zfill C k = t.
Proof.
  induction t; intros k C H; simpl in *.
  - destruct (Nat.eqb n k) eqn:E; [| destruct H].
    destruct H as [H|[]]. subst C. apply Nat.eqb_eq in E. subst n. reflexivity.
  - destruct H.
  - apply in_app_iff in H as [H|H].
    + apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
      simpl. rewrite (IHt1 k C1 HIn). reflexivity.
    + apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
      simpl. rewrite (IHt2 k C1 HIn). reflexivity.
  - apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
    simpl. rewrite (IHt (S k) C1 HIn). reflexivity.
  - apply in_app_iff in H as [H|H].
    + apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
      simpl. rewrite (IHt1 (S k) C1 HIn). reflexivity.
    + apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
      simpl. rewrite (IHt2 k C1 HIn). reflexivity.
Qed.

Lemma zdecs_complete : forall C k s, zfill C k = s -> In C (zdecs s k).
Proof.
  induction C; intros k s Heq.
  - rewrite <- Heq. simpl. rewrite Nat.eqb_refl. simpl. left. reflexivity.
  - destruct s as [n | x | a b | a | a b]; try discriminate.
    injection Heq as Ha Hu. subst a. subst b. simpl. apply in_app_iff. left.
    apply in_map_iff. exists C. split. reflexivity. apply IHC. reflexivity.
  - destruct s as [n | x | a b | a | a b]; try discriminate.
    injection Heq as Ha Hu. subst a. subst b. simpl. apply in_app_iff. right.
    apply in_map_iff. exists C. split. reflexivity. apply IHC. reflexivity.
  - destruct s as [n | x | a b | a | a b]; try discriminate.
    injection Heq as Ha. subst a. simpl. apply in_map_iff. exists C. split.
    reflexivity. apply IHC. reflexivity.
  - destruct s as [n | x | a b | a | a b]; try discriminate.
    injection Heq as Ha Hu. subst a. subst b. simpl. apply in_app_iff. left.
    apply in_map_iff. exists C. split. reflexivity. apply IHC. reflexivity.
  - destruct s as [n | x | a b | a | a b]; try discriminate.
    injection Heq as Ha Hu. subst a. subst b. simpl. apply in_app_iff. right.
    apply in_map_iff. exists C. split. reflexivity. apply IHC. reflexivity.
Qed.

Lemma positions_at : forall t C, In C (positions t) -> forall s, at_ctx C t = Some s -> plug C s = t.
Proof.
  induction t; intros C Hpos s Hat; simpl in *.
  - destruct Hpos as [HC | Hpos].
    + subst C. injection Hat as H. subst s. reflexivity.
    + destruct Hpos.
  - destruct Hpos as [HC | Hpos].
    + subst C. injection Hat as H. subst s. reflexivity.
    + destruct Hpos.
  - destruct Hpos as [HC | Hpos].
    + subst C. injection Hat as H. subst s. reflexivity.
    + apply in_app_iff in Hpos as [H|H].
      * apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
        simpl in Hat. simpl. rewrite (IHt1 C1 HIn s Hat). reflexivity.
      * apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
        simpl in Hat. simpl. rewrite (IHt2 C1 HIn s Hat). reflexivity.
  - destruct Hpos as [HC | Hpos].
    + subst C. injection Hat as H. subst s. reflexivity.
    + apply in_map_iff in Hpos as [C1 [Heq HIn]]. subst C.
      simpl in Hat. simpl. rewrite (IHt C1 HIn s Hat). reflexivity.
  - destruct Hpos as [HC | Hpos].
    + subst C. injection Hat as H. subst s. reflexivity.
    + apply in_app_iff in Hpos as [H|H].
      * apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
        simpl in Hat. simpl. rewrite (IHt1 C1 HIn s Hat). reflexivity.
      * apply in_map_iff in H as [C1 [Heq HIn]]. subst C.
        simpl in Hat. simpl. rewrite (IHt2 C1 HIn s Hat). reflexivity.
Qed.

Inductive red1_root : rule -> trm -> trm -> Prop :=
| rB : forall body u, red1_root RB (App (Lam body) u) (ESub body u)
| rGc : forall body u, occurs0 body = false -> red1_root RGc (ESub body u) body
| rR : forall C body u, zfill C 0 = body ->
    red1_root RR (ESub body u) (ESub (zplug_lift C 0 u) u).

Inductive red1r : rule -> trm -> trm -> Prop :=
| red1r_root : forall r t t', red1_root r t t' -> red1r r t t'
| rctx : forall r C t t', red1r r t t' -> red1r r (plug C t) (plug C t').

Definition red1 (t t' : trm) : Prop := exists r, red1r r t t'.

Lemma root_steps_sound : forall t r t', In (r,t') (root_steps t) -> red1r r t t'.
Proof.
  intros t r t' H.
  destruct t as [n | x | t1 t2 | body | body u].
  - simpl in H. destruct H.
  - simpl in H. destruct H.
  - destruct t1 as [n | x | a b | body | body u]; simpl in H.
    + destruct H.
    + destruct H.
    + destruct H.
    + destruct H as [H|[]]. injection H as Hr Ht. subst. apply red1r_root. apply rB.
    + destruct H.
  - simpl in H. destruct H.
  - simpl in H. apply in_app_iff in H as [H|H].
    + destruct (occurs0 body) eqn:E.
      * simpl in H. destruct H.
      * simpl in H. destruct H as [H|[]]. injection H as Hr Ht. subst.
        apply red1r_root. apply rGc. exact E.
    + apply in_map_iff in H as [C [Heq HIn]]. injection Heq as Hr Ht. subst.
      apply red1r_root. apply rR. apply zdecs_sound. exact HIn.
Qed.

Lemma root_steps_complete : forall t r t', red1_root r t t' -> In (r,t') (root_steps t).
Proof.
  intros t r t' H. destruct H.
  - simpl. left. reflexivity.
  - simpl. rewrite H. simpl. left. reflexivity.
  - simpl. apply in_app_iff. right. apply in_map_iff. exists C. split.
    reflexivity. apply zdecs_complete. exact H.
Qed.

Lemma steps_sound : forall t r t', In (r,t') (steps t) -> red1r r t t'.
Proof.
  intros t r t' H. unfold steps in H.
  apply in_flat_map in H as [C [Hpos Hstep]].
  unfold step_at in Hstep.
  destruct (at_ctx C t) as [s|] eqn:E; [| simpl in Hstep; destruct Hstep].
  apply in_map_iff in Hstep as [[pr pt] [Heq Hin]]. injection Heq as Hr Ht.
  subst r t'.
  assert (Hp : plug C s = t) by (apply (positions_at t C Hpos s E)).
  rewrite <- Hp. apply rctx. apply root_steps_sound. exact Hin.
Qed.

Corollary steps_sound_red1 : forall t r t', In (r,t') (steps t) -> red1 t t'.
Proof. intros. exists r. apply steps_sound. exact H. Qed.

Lemma positions_hole : forall t, In GHole (positions t).
Proof. intros t. destruct t; simpl; left; reflexivity. Qed.

Corollary root_steps_in_steps : forall t r t', In (r,t') (root_steps t) -> In (r,t') (steps t).
Proof.
  intros t r t' H. unfold steps.
  apply in_flat_map. exists GHole. split.
  - apply positions_hole.
  - unfold step_at. simpl. apply in_map_iff. exists (r,t'). split.
    + reflexivity.
    + exact H.
Qed.

Print Assumptions zdecs_sound.
Print Assumptions zdecs_complete.
Print Assumptions positions_at.
Print Assumptions root_steps_sound.
Print Assumptions root_steps_complete.
Print Assumptions steps_sound.
Print Assumptions steps_sound_red1.
Print Assumptions root_steps_in_steps.

Fixpoint comp (C D : ctx) : ctx :=
  match C with
  | GHole => D
  | GAppL C1 u => GAppL (comp C1 D) u
  | GAppR u C1 => GAppR u (comp C1 D)
  | GLam C1 => GLam (comp C1 D)
  | GESubL C1 u => GESubL (comp C1 D) u
  | GESubR t1 C1 => GESubR t1 (comp C1 D)
  end.

Lemma plug_comp : forall C D u, plug (comp C D) u = plug C (plug D u).
Proof.
  induction C; intros D u; simpl.
  - reflexivity.
  - rewrite IHC. reflexivity.
  - rewrite IHC. reflexivity.
  - rewrite IHC. reflexivity.
  - rewrite IHC. reflexivity.
  - rewrite IHC. reflexivity.
Qed.

Lemma positions_comp : forall C a D, In D (positions a) -> In (comp C D) (positions (plug C a)).
Proof.
  induction C; intros a D H; simpl.
  - exact H.
  - right. apply in_app_iff. left. apply in_map_iff. exists (comp C D). split.
    reflexivity. apply IHC. exact H.
  - right. apply in_app_iff. right. apply in_map_iff. exists (comp C D). split.
    reflexivity. apply IHC. exact H.
  - right. apply in_map_iff. exists (comp C D). split.
    reflexivity. apply IHC. exact H.
  - right. apply in_app_iff. left. apply in_map_iff. exists (comp C D). split.
    reflexivity. apply IHC. exact H.
  - right. apply in_app_iff. right. apply in_map_iff. exists (comp C D). split.
    reflexivity. apply IHC. exact H.
Qed.

Lemma at_ctx_comp : forall C D a s, at_ctx D a = Some s -> at_ctx (comp C D) (plug C a) = Some s.
Proof.
  induction C; intros D a s H; simpl.
  - exact H.
  - apply IHC. exact H.
  - apply IHC. exact H.
  - apply IHC. exact H.
  - apply IHC. exact H.
  - apply IHC. exact H.
Qed.

Lemma steps_complete : forall a r b, red1r r a b -> In (r,b) (steps a).
Proof.
  intros a r b H. induction H.
  - apply root_steps_in_steps. apply root_steps_complete. exact H.
  - unfold steps in *.
    apply in_flat_map in IHred1r as [D [HD Hst]].
    apply in_flat_map. exists (comp C D). split.
    + apply positions_comp. exact HD.
    + unfold step_at in *.
      destruct (at_ctx D t) as [s|] eqn:E; [| simpl in Hst; destruct Hst].
      apply in_map_iff in Hst as [[pr pt] [Heq Hin]].
      rewrite (at_ctx_comp C D t s E). simpl.
      apply in_map_iff. exists (pr, pt). split.
      * simpl in *. injection Heq as Hr Ht. subst pr.
        rewrite (plug_comp C D pt). rewrite Ht. reflexivity.
      * exact Hin.
Qed.

Scheme Equality for trm.

Definition has_red (t t' : trm) : bool :=
  existsb (fun p => if trm_eq_dec (snd p) t' then true else false) (steps t).

Lemma has_red_f : forall t' (p : rule * trm), (if trm_eq_dec (snd p) t' then true else false) = true <-> snd p = t'.
Proof.
  intros t' [r s]. simpl. destruct (trm_eq_dec s t').
  - simpl. split; intro H; [exact e | reflexivity].
  - simpl. split; intro H; [discriminate H | exfalso; exact (n H)].
Qed.

Lemma has_red_spec : forall t t', has_red t t' = true <-> red1 t t'.
Proof.
  intros t t'. unfold has_red. split.
  - intro H. apply existsb_exists in H. destruct H as [[pr pt] [Hin Hf]].
    apply has_red_f in Hf. simpl in Hf. exists pr. apply steps_sound. rewrite Hf in Hin. exact Hin.
  - intros [r Hr]. apply existsb_exists. exists (r,t'). split.
    + apply steps_complete. exact Hr.
    + apply has_red_f. reflexivity.
Qed.

Lemma red1_dec : forall t t', {red1 t t'} + {~ red1 t t'}.
Proof.
  intros t t'. destruct (has_red t t') eqn:E.
  - left. apply has_red_spec. exact E.
  - right. intro H. apply has_red_spec in H. rewrite H in E. discriminate E.
Qed.

Print Assumptions plug_comp.
Print Assumptions positions_comp.
Print Assumptions at_ctx_comp.
Print Assumptions steps_complete.
Print Assumptions has_red_spec.
Print Assumptions red1_dec.
