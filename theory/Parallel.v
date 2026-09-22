From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction.

Inductive par : trm -> trm -> Prop :=
| par_refl : forall t, par t t
| par_step : forall t t', red1 t t' -> par t t'
| par_ctx : forall C t t', par t t' -> par (plug C t) (plug C t').

Lemma par_red1_iff : forall t t', par t t' <-> t = t' \/ red1 t t'.
Proof.
  intros t t'. split.
  - intros H. induction H.
    + left. reflexivity.
    + right. exact H.
    + destruct IHpar as [Heq|Hr].
      * left. subst. reflexivity.
      * right. destruct Hr as [r Hr]. exists r. apply rctx. exact Hr.
  - intros [Heq|Hr].
    + subst. apply par_refl.
    + apply par_step. exact Hr.
Qed.

Lemma red1_in_par : forall t t', red1 t t' -> par t t'.
Proof. intros. apply par_step. exact H. Qed.

Lemma par_context : forall C t t', par t t' -> par (plug C t) (plug C t').
Proof. intros. apply par_ctx. exact H. Qed.

Lemma par_to_red1_or_eq : forall t t', par t t' -> t = t' \/ red1 t t'.
Proof. intros. apply par_red1_iff. exact H. Qed.

Lemma red1_or_eq_to_par : forall t t', t = t' \/ red1 t t' -> par t t'.
Proof. intros. apply par_red1_iff. exact H. Qed.

Lemma par_reflexive : forall t, par t t.
Proof. intros. apply par_refl. Qed.

Print Assumptions par_red1_iff.
Print Assumptions red1_in_par.
Print Assumptions par_context.
Print Assumptions par_to_red1_or_eq.
Print Assumptions red1_or_eq_to_par.
Print Assumptions par_reflexive.
