From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.

Definition atom := nat.

Inductive ntrm : Type :=
| NVar : atom -> ntrm
| NApp : ntrm -> ntrm -> ntrm
| NLam : atom -> ntrm -> ntrm
| NESub : ntrm -> atom -> ntrm -> ntrm
| NMVar : atom -> list atom -> ntrm.

Fixpoint nfv (t : ntrm) : list atom :=
  match t with
  | NVar x => [x]
  | NApp a b => nfv a ++ nfv b
  | NLam x a => filter (fun y => negb (Nat.eqb y x)) (nfv a)
  | NESub a x b => filter (fun y => negb (Nat.eqb y x)) (nfv a) ++ nfv b
  | NMVar _ d => d
  end.

Definition isubst_meta (X : atom) (d : list atom) (x : atom) (v : ntrm) : ntrm :=
  if existsb (Nat.eqb x) d then NESub (NMVar X d) x v else NMVar X d.

Lemma isubst_meta_in : forall X d x v, In x d -> isubst_meta X d x v = NESub (NMVar X d) x v.
Proof.
  intros X d x v H. unfold isubst_meta.
  destruct (existsb (Nat.eqb x) d) eqn:E; [reflexivity |].
  assert (Hex : existsb (Nat.eqb x) d = true)
    by (apply existsb_exists; exists x; split; [exact H | apply Nat.eqb_refl]).
  rewrite Hex in E. discriminate E.
Qed.

Lemma isubst_meta_notin : forall X d x v, ~ In x d -> isubst_meta X d x v = NMVar X d.
Proof.
  intros X d x v H. unfold isubst_meta.
  destruct (existsb (Nat.eqb x) d) eqn:E; [| reflexivity].
  exfalso. apply existsb_exists in E. destruct E as [y [Hy HE]].
  apply Nat.eqb_eq in HE. subst y. apply H. exact Hy.
Qed.

Inductive nctx : Type :=
| nHole : nctx
| nAppL : nctx -> ntrm -> nctx
| nAppR : ntrm -> nctx -> nctx
| nLam : atom -> nctx -> nctx
| nESubL : nctx -> atom -> ntrm -> nctx
| nESubR : ntrm -> atom -> nctx -> nctx.

Fixpoint nplug (C : nctx) (t : ntrm) : ntrm :=
  match C with
  | nHole => t
  | nAppL C1 u => NApp (nplug C1 t) u
  | nAppR u C1 => NApp u (nplug C1 t)
  | nLam x C1 => NLam x (nplug C1 t)
  | nESubL C1 x u => NESub (nplug C1 t) x u
  | nESubR t1 x C1 => NESub t1 x (nplug C1 t)
  end.

Fixpoint is_subst_chain (C : nctx) : bool :=
  match C with
  | nHole => true
  | nESubL C1 _ _ => is_subst_chain C1
  | _ => false
  end.

Inductive Es : ntrm -> ntrm -> Prop :=
| Es_refl : forall t, Es t t
| Es_sym : forall t u, Es t u -> Es u t
| Es_trans : forall t u v, Es t u -> Es u v -> Es t v
| Es_C : forall t x u y v,
    y <> x -> ~ In y (nfv u) -> ~ In x (nfv v) ->
    Es (NESub (NESub t x u) y v) (NESub (NESub t y v) x u)
| Es_ctx : forall C t t', Es t t' -> Es (nplug C t) (nplug C t').

Fixpoint cbinders (C : nctx) : list atom :=
  match C with
  | nHole => []
  | nAppL C1 _ => cbinders C1
  | nAppR _ C1 => cbinders C1
  | nLam x C1 => x :: cbinders C1
  | nESubL C1 _ _ => cbinders C1
  | nESubR _ _ C1 => cbinders C1
  end.

Definition cavoid (C : nctx) (phi : list atom) : bool :=
  forallb (fun y => negb (existsb (Nat.eqb y) phi)) (cbinders C).

Inductive nred : ntrm -> ntrm -> Prop :=
| nred_B : forall t x u, nred (NApp (NLam x t) u) (NESub t x u)
| nred_Gc : forall t x u, ~ In x (nfv t) -> nred (NESub t x u) t
| nred_RX : forall C X d x u phi,
    In x d ->
    In x phi ->
    (forall y, In y (nfv u) -> In y phi) ->
    is_subst_chain C = false ->
    nred (NESub (nplug C (NMVar X d)) x u)
         (NESub (nplug C (NESub (NMVar X d) x u)) x u)
| nred_R : forall C x u phi,
    In x phi ->
    (forall y, In y (nfv u) -> In y phi) ->
    cavoid C phi = true ->
    nred (NESub (nplug C (NVar x)) x u) (NESub (nplug C u) x u)
| nred_ctx : forall C t t', nred t t' -> nred (nplug C t) (nplug C t').

Lemma eqC_in_Es : forall t x u y v,
  y <> x -> ~ In y (nfv u) -> ~ In x (nfv v) ->
  Es (NESub (NESub t x u) y v) (NESub (NESub t y v) x u).
Proof. intros. apply Es_C; assumption. Qed.

Lemma Es_ctx_any : forall C t t', Es t t' -> Es (nplug C t) (nplug C t').
Proof. intros. apply Es_ctx. exact H. Qed.

Lemma nred_R_intro : forall C x u phi,
  In x phi -> (forall y, In y (nfv u) -> In y phi) -> cavoid C phi = true ->
  nred (NESub (nplug C (NVar x)) x u) (NESub (nplug C u) x u).
Proof.
  intros C x u phi Hx Hu Hc.
  apply nred_R with (phi := phi).
  - exact Hx.
  - exact Hu.
  - exact Hc.
Qed.

Lemma Es_refl_any : forall t, Es t t.
Proof. intros. apply Es_refl. Qed.

Lemma Es_sym_any : forall t u, Es t u -> Es u t.
Proof. intros. apply Es_sym. exact H. Qed.

Lemma Es_trans_any : forall t u v, Es t u -> Es u v -> Es t v.
Proof. intros. apply Es_trans with (u := u); assumption. Qed.

Print Assumptions isubst_meta_in.
Print Assumptions isubst_meta_notin.
Print Assumptions Es_ctx_any.
Print Assumptions nred_R_intro.
Print Assumptions eqC_in_Es.
Print Assumptions Es_refl_any.
Print Assumptions Es_sym_any.
Print Assumptions Es_trans_any.

Lemma in_filter_neq : forall y x l,
  In y (filter (fun z => negb (Nat.eqb z x)) l) -> In y l /\ y <> x.
Proof.
  intros y x l H. apply filter_In in H. destruct H as [Hl Hp]. split; [exact Hl |].
  apply Nat.eqb_neq. destruct (Nat.eqb y x) eqn:E; [| reflexivity].
  simpl in Hp. discriminate Hp.
Qed.

Lemma filter_neq_in : forall y x l,
  In y l -> y <> x -> In y (filter (fun z => negb (Nat.eqb z x)) l).
Proof.
  intros y x l Hl Hne. apply filter_In. split; [exact Hl |].
  apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.


Lemma nplug_fv_mono : forall C t s,
  incl (nfv t) (nfv s) -> incl (nfv (nplug C t)) (nfv (nplug C s)).
Proof.
  induction C; intros t s Hincl; unfold incl in *; simpl in *.
  - apply Hincl.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. apply (IHC t s Hincl). exact Hy.
    + apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. exact Hy.
    + apply in_app_iff. right. apply (IHC t s Hincl). exact Hy.
  - intros y Hy. apply in_filter_neq in Hy as [Hy Hne].
    apply filter_neq_in.
    + apply (IHC t s Hincl). exact Hy.
    + exact Hne.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. apply in_filter_neq in Hy as [Hy Hne].
      apply filter_neq_in.
      * apply (IHC t s Hincl). exact Hy.
      * exact Hne.
    + apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. exact Hy.
    + apply in_app_iff. right. apply (IHC t s Hincl). exact Hy.
Qed.

Lemma nplug_fv_upper : forall C t s,
  incl (nfv (nplug C t)) (nfv (nplug C s) ++ nfv t).
Proof.
  induction C; intros t s; unfold incl in *; simpl in *.
  - intros y Hy. apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply (IHC t s) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply in_app_iff. left. exact Hy.
      * apply in_app_iff. right. exact Hy.
    + apply in_app_iff. left. apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. apply in_app_iff. left. exact Hy.
    + apply (IHC t s) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply in_app_iff. right. exact Hy.
      * apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_filter_neq in Hy as [Hy Hne].
    apply (IHC t s) in Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hne].
    + apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_filter_neq in Hy as [Hy Hne].
      apply (IHC t s) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hne].
      * apply in_app_iff. right. exact Hy.
    + apply in_app_iff. left. apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_app_iff. left. apply in_app_iff. left. exact Hy.
    + apply (IHC t s) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply in_app_iff. right. exact Hy.
      * apply in_app_iff. right. exact Hy.
Qed.

Inductive nred_core : ntrm -> ntrm -> Prop :=
| ncore_B : forall t x u, nred_core (NApp (NLam x t) u) (NESub t x u)
| ncore_Gc : forall t x u, ~ In x (nfv t) -> nred_core (NESub t x u) t
| ncore_R : forall C x u phi,
    In x phi -> (forall y, In y (nfv u) -> In y phi) -> cavoid C phi = true ->
    nred_core (NESub (nplug C (NVar x)) x u) (NESub (nplug C u) x u)
| ncore_ctx : forall C t t', nred_core t t' -> nred_core (nplug C t) (nplug C t').

Lemma nred_core_fv : forall t t', nred_core t t' -> incl (nfv t') (nfv t).
Proof.
  intros t t' H. induction H; simpl; unfold incl in *.
  - intros y Hy. exact Hy.
  - intros y Hy. apply in_app_iff. left.
    apply filter_neq_in; [exact Hy | intro E; apply H; subst; exact Hy].
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_filter_neq in Hy as [Hy Hne].
      apply (nplug_fv_upper C u (NVar x)) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hne].
      * apply in_app_iff. right. exact Hy.
    + apply in_app_iff. right. exact Hy.
  - apply nplug_fv_mono. exact IHnred_core.
Qed.

Print Assumptions nplug_fv_mono.
Print Assumptions nplug_fv_upper.
Print Assumptions nred_core_fv.

Lemma nplug_esub_fv : forall C X d x u y,
  y <> x ->
  In y (nfv (nplug C (NESub (NMVar X d) x u))) ->
  In y (nfv (nplug C (NMVar X d))) \/ In y (nfv u).
Proof.
  induction C; intros X d x u y Hne Hy; simpl in *.
  - apply in_app_iff in Hy as [Hy|Hy].
    + left. apply in_filter_neq in Hy as [Hy _]. simpl. exact Hy.
    + right. exact Hy.
  - apply in_app_iff in Hy as [Hy|Hy].
    + apply (IHC X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
      * left. apply in_app_iff. left. exact Hy.
      * right. exact Hy.
    + left. apply in_app_iff. right. exact Hy.
  - apply in_app_iff in Hy as [Hy|Hy].
    + left. apply in_app_iff. left. exact Hy.
    + apply (IHC X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
      * left. apply in_app_iff. right. exact Hy.
      * right. exact Hy.
  - apply in_filter_neq in Hy as [Hy Hz].
    apply (IHC X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
    + left. apply filter_neq_in; [exact Hy | exact Hz].
    + right. exact Hy.
  - apply in_app_iff in Hy as [Hy|Hy].
    + apply in_filter_neq in Hy as [Hy Hz].
      apply (IHC X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
      * left. apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hz].
      * right. exact Hy.
    + left. apply in_app_iff. right. exact Hy.
  - apply in_app_iff in Hy as [Hy|Hy].
    + left. apply in_app_iff. left. exact Hy.
    + apply (IHC X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
      * left. apply in_app_iff. right. exact Hy.
      * right. exact Hy.
Qed.

Lemma nred_fv : forall t t', nred t t' -> incl (nfv t') (nfv t).
Proof.
  intros t t' H. induction H; simpl; unfold incl in *.
  - intros y Hy. exact Hy.
  - intros y Hy. apply in_app_iff. left.
    apply filter_neq_in; [exact Hy | intro E; apply H; subst; exact Hy].
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_filter_neq in Hy as [Hy Hne].
      apply (nplug_esub_fv C X d x u y Hne) in Hy. destruct Hy as [Hy|Hy].
      * apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hne].
      * apply in_app_iff. right. exact Hy.
    + apply in_app_iff. right. exact Hy.
  - intros y Hy. apply in_app_iff in Hy as [Hy|Hy].
    + apply in_filter_neq in Hy as [Hy Hne].
      apply (nplug_fv_upper C u (NVar x)) in Hy. apply in_app_iff in Hy as [Hy|Hy].
      * apply in_app_iff. left. apply filter_neq_in; [exact Hy | exact Hne].
      * apply in_app_iff. right. exact Hy.
    + apply in_app_iff. right. exact Hy.
  - apply nplug_fv_mono. exact IHnred.
Qed.

Print Assumptions nplug_esub_fv.
Print Assumptions nred_fv.
