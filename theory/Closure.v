From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction Metatheory.

Inductive Star (R : trm -> trm -> Prop) : trm -> trm -> Prop :=
| star_refl : forall t, Star R t t
| star_step : forall t u v, R t u -> Star R u v -> Star R t v.

Lemma Star_trans : forall R a b c, Star R a b -> Star R b c -> Star R a c.
Proof.
  intros R a b c H. induction H; intros Hbc.
  - exact Hbc.
  - apply star_step with (u := u). exact H. apply IHStar. exact Hbc.
Qed.

Lemma red1_star : forall t t', red1 t t' -> Star red1 t t'.
Proof.
  intros t t' H. apply star_step with (u := t'). exact H. apply star_refl.
Qed.

Lemma Plus_to_Star : forall R t u, Plus R t u -> Star R t u.
Proof.
  intros R t u H. induction H.
  - apply star_step with (u := u). exact H. apply star_refl.
  - apply star_step with (u := u). exact H. exact IHPlus.
Qed.

Lemma Star_red1_context : forall C t t', Star red1 t t' -> Star red1 (plug C t) (plug C t').
Proof.
  intros C t t' H. induction H.
  - apply star_refl.
  - apply star_step with (u := plug C u).
    + destruct H as [r Hr]. exists r. apply rctx. exact Hr.
    + exact IHStar.
Qed.

Lemma star_one_trans : forall R a b c, R a b -> Star R b c -> Star R a c.
Proof. intros. apply star_step with (u := b). exact H. exact H0. Qed.

Print Assumptions Star_trans.
Print Assumptions red1_star.
Print Assumptions Plus_to_Star.
Print Assumptions Star_red1_context.
Print Assumptions star_one_trans.
