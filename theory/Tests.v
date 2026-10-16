From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction Metatheory.

Definition t_id : trm := App (Lam (BVar 0)) (FVar 1).
Definition t_dup : trm := App (Lam (App (BVar 0) (BVar 0))) (FVar 1).
Definition t_dup_es : trm := ESub (App (BVar 0) (BVar 0)) (FVar 1).
Definition t_gc : trm := ESub (FVar 2) (FVar 1).
Definition t_nested : trm := ESub (ESub (BVar 0) (FVar 1)) (FVar 2).
Definition t_capture : trm := App (Lam (Lam (BVar 1))) (FVar 1).
Definition t_under : trm := ESub (Lam (BVar 1)) (FVar 2).

Definition corpus : list trm :=
  [t_id; t_dup; t_dup_es; t_gc; t_nested; t_capture; t_under].

Example g_id_beta : has_rule RB (steps t_id) = true.
Proof. reflexivity. Qed.

Example g_dup_beta : has_rule RB (steps t_dup) = true.
Proof. reflexivity. Qed.

Example g_dup_es_two_R : count_rule RR (steps t_dup_es) = 2.
Proof. reflexivity. Qed.

Example g_dup_es_no_Gc : has_rule RGc (steps t_dup_es) = false.
Proof. reflexivity. Qed.

Example g_gc_gc : has_rule RGc (steps t_gc) = true.
Proof. reflexivity. Qed.

Example g_gc_no_R : has_rule RR (steps t_gc) = false.
Proof. reflexivity. Qed.

Example g_nested_gc : has_rule RGc (steps t_nested) = true.
Proof. reflexivity. Qed.

Example g_under_R : has_rule RR (steps t_under) = true.
Proof. reflexivity. Qed.

Example g_capture_beta : has_rule RB (steps t_capture) = true.
Proof. reflexivity. Qed.

Example g_normal_var : normal_form (FVar 5) = true.
Proof. reflexivity. Qed.

Example g_normal_lam : normal_form (Lam (BVar 0)) = true.
Proof. reflexivity. Qed.

Example g_capture_avoid_lam : subst 0 (FVar 1) (Lam (Lam (BVar 1))) = Lam (Lam (BVar 1)).
Proof. reflexivity. Qed.

Example g_capture_avoid_es : subst 0 (FVar 1) (ESub (FVar 0) (FVar 2)) = ESub (FVar 1) (FVar 2).
Proof. reflexivity. Qed.

Example g_occurs0_lam : occurs0 (Lam (BVar 0)) = false.
Proof. reflexivity. Qed.

Example g_occurs0_bvar : occurs0 (BVar 0) = true.
Proof. reflexivity. Qed.

Lemma corpus_sound : forall t p, In t corpus -> In p (steps t) -> red1r (fst p) t (snd p).
Proof. intros t [r s] _ H. simpl. apply steps_sound. exact H. Qed.

Example gc_outer_index :
  root_steps (ESub (BVar 1) (FVar 7)) = [(RGc, BVar 0)].
Proof. reflexivity. Qed.

Example gc_under_lambda :
  root_steps (ESub (Lam (BVar 2)) (FVar 7)) = [(RGc, Lam (BVar 1))].
Proof. reflexivity. Qed.

Example gc_under_substitution :
  root_steps (ESub (ESub (BVar 2) (BVar 1)) (FVar 7)) =
  [(RGc, ESub (BVar 1) (BVar 0))].
Proof. reflexivity. Qed.

Example gc_preserves_inner_binder :
  root_steps (ESub (Lam (BVar 0)) (FVar 7)) = [(RGc, Lam (BVar 0))].
Proof. reflexivity. Qed.

Print Assumptions gc_outer_index.
Print Assumptions gc_under_lambda.
Print Assumptions gc_under_substitution.
Print Assumptions gc_preserves_inner_binder.

Example r_under_two_binders :
  root_steps (ESub (Lam (Lam (BVar 2))) (BVar 0)) =
  [(RR, ESub (Lam (Lam (BVar 3))) (BVar 0))].
Proof. reflexivity. Qed.

Example open_outer_reference :
  lower 0 (open_rec 0 (BVar 0) (Lam (Lam (BVar 2)))) =
  Lam (Lam (BVar 2)).
Proof. reflexivity. Qed.

Example gc_closed_under_lambda :
  red1 (Lam (ESub (BVar 1) (FVar 7))) (Lam (BVar 0)).
Proof.
  exists RGc. apply (rctx RGc (GLam GHole)).
  apply red1r_root. apply rGc. reflexivity.
Qed.

Example nested_r_preserves_closure :
  lc (Lam (ESub (Lam (Lam (BVar 3))) (BVar 0))).
Proof.
  apply red1_lc with (Lam (ESub (Lam (Lam (BVar 2))) (BVar 0))).
  - exists RR. apply (rctx RR (GLam GHole)).
    apply red1r_root. apply rR with (C := ZLam (ZLam ZTop)). reflexivity.
  - unfold lc. simpl. split; lia.
Qed.

Print Assumptions r_under_two_binders.
Print Assumptions open_outer_reference.
Print Assumptions gc_closed_under_lambda.
Print Assumptions nested_r_preserves_closure.

Lemma corpus_complete : forall t r t', In t corpus -> red1r r t t' -> In (r,t') (steps t).
Proof. intros t r t' _ H. apply steps_complete. exact H. Qed.

Lemma corpus_decides : forall t t', In t corpus -> has_red t t' = true <-> red1 t t'.
Proof. intros t t' _. apply has_red_spec. Qed.

Lemma corpus_fv_preserved : forall t p, In t corpus -> In p (steps t) ->
  incl (fvs (snd p)) (fvs t).
Proof. intros t [r s] _ H. simpl. apply (lemma_2_1_fv_preserved t s). exact (steps_sound_red1 t r s H). Qed.

Print Assumptions corpus_sound.
Print Assumptions corpus_complete.
Print Assumptions corpus_decides.
Print Assumptions corpus_fv_preserved.
