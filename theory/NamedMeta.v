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

Lemma in_filter_neq_iff : forall z a l,
  In z (filter (fun w => negb (Nat.eqb w a)) l) <-> In z l /\ z <> a.
Proof.
  intros z a l. split.
  - intro H. apply filter_In in H. destruct H as [Hl Hp]. split; [exact Hl |].
    apply Nat.eqb_neq. destruct (Nat.eqb z a) eqn:E; [| reflexivity].
    simpl in Hp. discriminate Hp.
  - intros [Hl Hne]. apply filter_In. split; [exact Hl |].
    apply Nat.eqb_neq in Hne. rewrite Hne. reflexivity.
Qed.

Lemma Es_fv_both : forall t u, Es t u ->
  incl (nfv t) (nfv u) /\ incl (nfv u) (nfv t).
Proof.
  apply Es_ind.
  - intros t0. split; unfold incl; auto.
  - intros t0 u0 H1 IH1. split.
    + apply (proj2 IH1).
    + apply (proj1 IH1).
  - intros t0 u0 v0 H1 H2 IH1 IH2. split.
    + intros z Hz. apply (proj1 IH2). apply (proj1 H2). exact Hz.
    + intros z Hz. apply (proj2 H2). apply (proj2 IH2). exact Hz.
  - intros t0 x0 u0 y0 v0 Hyx Hyu Hxv. split; unfold incl; intros z Hz; simpl in *;
    apply in_app_iff in Hz as [Hz|Hz].
    + apply in_filter_neq_iff in Hz as [Hz Hy]. apply in_app_iff in Hz as [Hz|Hz].
      * apply in_filter_neq_iff in Hz as [Hz Hx].
        apply in_app_iff. left. apply in_filter_neq_iff. split; [| exact Hx].
        apply in_app_iff. left. apply in_filter_neq_iff. split; [exact Hz | exact Hy].
      * apply in_app_iff. right. exact Hz.
    + apply in_app_iff. left. apply in_filter_neq_iff. split; [| ].
      * apply in_app_iff. right. exact Hz.
      * intro E. apply Hxv. subst z. exact Hz.
    + apply in_filter_neq_iff in Hz as [Hz Hx]. apply in_app_iff in Hz as [Hz|Hz].
      * apply in_filter_neq_iff in Hz as [Hz Hy].
        apply in_app_iff. left. apply in_filter_neq_iff. split; [| exact Hy].
        apply in_app_iff. left. apply in_filter_neq_iff. split; [exact Hz | exact Hx].
      * apply in_app_iff. right. exact Hz.
    + apply in_app_iff. left. apply in_filter_neq_iff. split; [| ].
      * apply in_app_iff. right. exact Hz.
      * intro E. apply Hyu. subst z. exact Hz.
  - intros C0 t0 t0' H1 IH1. split; apply nplug_fv_mono.
    + apply (proj1 IH1).
    + apply (proj2 IH1).
Qed.

Lemma Es_fv : forall t u, Es t u -> forall z, In z (nfv t) <-> In z (nfv u).
Proof.
  intros t u H z. destruct (Es_fv_both t u H) as [Htu Hut]. split.
  - apply Htu.
  - apply Hut.
Qed.

Print Assumptions in_filter_neq_iff.
Print Assumptions Es_fv.

Fixpoint nvars (t : ntrm) : list atom :=
  match t with
  | NVar x => [x]
  | NApp a b => nvars a ++ nvars b
  | NLam x a => x :: nvars a
  | NESub a x u => x :: (nvars a ++ nvars u)
  | NMVar _ d => d
  end.

Definition rename_atom (x y z : atom) : atom :=
  if Nat.eqb z x then y else z.

Fixpoint rename_bound (x y : atom) (t : ntrm) : ntrm :=
  match t with
  | NVar z => NVar (rename_atom x y z)
  | NApp a b => NApp (rename_bound x y a) (rename_bound x y b)
  | NLam z a => NLam z (if Nat.eqb z x then a else rename_bound x y a)
  | NESub a z u =>
      NESub (if Nat.eqb z x then a else rename_bound x y a) z (rename_bound x y u)
  | NMVar X d => NMVar X (map (rename_atom x y) d)
  end.

Definition fresh_atom (avoid : list atom) : atom := S (fold_right Nat.max 0 avoid).

Definition freshen_binder (avoid : list atom) (a : ntrm) (x : atom) (u : ntrm) : ntrm :=
  let y := fresh_atom (x :: (nvars a ++ nvars u ++ avoid)) in
  NESub (rename_bound x y a) y u.

Fixpoint freshen_substitutions (avoid : list atom) (t : ntrm) {struct t} : ntrm :=
  match t with
  | NVar x => NVar x
  | NApp a b =>
      let a' := freshen_substitutions (nvars b ++ avoid) a in
      NApp a' (freshen_substitutions (nvars a' ++ avoid) b)
  | NLam x a => NLam x (freshen_substitutions (x :: avoid) a)
  | NESub a x u =>
      let a' := freshen_substitutions (x :: (nvars u ++ avoid)) a in
      let u' := freshen_substitutions (x :: (nvars a' ++ avoid)) u in
      freshen_binder avoid a' x u'
  | NMVar X d => NMVar X d
  end.

Lemma in_fold_max : forall l x, In x l -> x <= fold_right Nat.max 0 l.
Proof.
  induction l as [| a l IH]; intros x H; simpl in *.
  - contradiction.
  - destruct H as [H|H].
    + subst x. apply Nat.le_max_l.
    + apply Nat.le_trans with (fold_right Nat.max 0 l).
      * apply IH. exact H.
      * apply Nat.le_max_r.
Qed.

Lemma fresh_atom_notin : forall l, ~ In (fresh_atom l) l.
Proof.
  intros l H. pose proof (in_fold_max l (fresh_atom l) H).
  unfold fresh_atom in *. lia.
Qed.

Lemma nfv_in_nvars : forall t x, In x (nfv t) -> In x (nvars t).
Proof.
  induction t; intros z H; simpl in *.
  - exact H.
  - apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply IHt1. exact H.
    + right. apply IHt2. exact H.
  - right. apply IHt. apply in_filter_neq in H. tauto.
  - right. apply in_app_iff in H as [H|H]; apply in_app_iff.
    + left. apply IHt1. apply in_filter_neq in H. tauto.
    + right. apply IHt2. exact H.
  - exact H.
Qed.

Lemma rename_atom_in : forall l x y z,
  In z (map (rename_atom x y) l) <->
  (z = y /\ In x l) \/ (z <> x /\ In z l).
Proof.
  intros l x y z. rewrite in_map_iff. unfold rename_atom. split.
  - intros [a [H Ha]]. destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst a. left. auto.
    + apply Nat.eqb_neq in E. subst z. right. auto.
  - intros [[H Hx]|[Hne Hz]].
    + subst z. exists x. rewrite Nat.eqb_refl. auto.
    + exists z. apply Nat.eqb_neq in Hne. rewrite Hne. auto.
Qed.

Lemma rename_bound_fv : forall t x y z,
  x <> y -> ~ In y (nvars t) ->
  (In z (nfv (rename_bound x y t)) <->
   (z = y /\ In x (nfv t)) \/ (z <> x /\ In z (nfv t))).
Proof.
  induction t; intros x y z Hxy Hy; simpl in *.
  - unfold rename_atom. destruct (Nat.eqb a x) eqn:E.
    + apply Nat.eqb_eq in E. subst a. intuition congruence.
    + apply Nat.eqb_neq in E. intuition congruence.
  - rewrite !in_app_iff in *. rewrite IHt1, IHt2; tauto.
  - assert (Hya : ~ In y (nvars t)) by tauto.
    assert (Hyn : y <> a) by (intro H; apply Hy; left; symmetry; exact H).
    destruct (Nat.eqb a x) eqn:E; simpl.
    + apply Nat.eqb_eq in E. subst a. rewrite !in_filter_neq_iff. intuition congruence.
    + apply Nat.eqb_neq in E. rewrite !in_filter_neq_iff.
      rewrite IHt by assumption. intuition congruence.
  - assert (Hya : ~ In y (nvars t1)) by (intro H; apply Hy; right; apply in_app_iff; left; exact H).
    assert (Hyu : ~ In y (nvars t2)) by (intro H; apply Hy; right; apply in_app_iff; right; exact H).
    assert (Hyn : y <> a) by (intro H; apply Hy; left; symmetry; exact H).
    destruct (Nat.eqb a x) eqn:E; simpl; rewrite !in_app_iff, !in_filter_neq_iff.
    + apply Nat.eqb_eq in E. subst a. rewrite IHt2 by assumption. intuition congruence.
    + apply Nat.eqb_neq in E. rewrite IHt1, IHt2 by assumption. intuition congruence.
  - apply rename_atom_in.
Qed.

Lemma freshen_binder_fv : forall avoid a x u z,
  In z (nfv (freshen_binder avoid a x u)) <-> In z (nfv (NESub a x u)).
Proof.
  intros avoid a x u z. unfold freshen_binder.
  set (y := fresh_atom (x :: (nvars a ++ nvars u ++ avoid))).
  assert (Hy : ~ In y (x :: (nvars a ++ nvars u ++ avoid))) by apply fresh_atom_notin.
  assert (Hxy : x <> y) by (intro H; apply Hy; left; exact H).
  assert (Hya : ~ In y (nvars a)) by (intro H; apply Hy; right; apply in_app_iff; left; exact H).
  assert (Hyaf : ~ In y (nfv a)) by (intro H; apply Hya; apply nfv_in_nvars; exact H).
  simpl. rewrite !in_app_iff, !in_filter_neq_iff.
  rewrite rename_bound_fv by assumption.
  destruct (Nat.eq_dec z y) as [-> | Hzy]; intuition congruence.
Qed.

Lemma freshen_substitutions_fv : forall t avoid z,
  In z (nfv (freshen_substitutions avoid t)) <-> In z (nfv t).
Proof.
  induction t; intros avoid z; cbn [freshen_substitutions]; try reflexivity.
  - cbn [nfv]. rewrite !in_app_iff, IHt1, IHt2. reflexivity.
  - cbn [nfv]. rewrite !in_filter_neq_iff, IHt. reflexivity.
  - change (In z (nfv (freshen_binder avoid
      (freshen_substitutions (a :: nvars t2 ++ avoid) t1) a
      (freshen_substitutions (a :: nvars (freshen_substitutions (a :: nvars t2 ++ avoid) t1) ++ avoid) t2)))
      <-> In z (nfv (NESub t1 a t2))).
    rewrite freshen_binder_fv. cbn [nfv].
    rewrite !in_app_iff, !in_filter_neq_iff, IHt1, IHt2. reflexivity.
Qed.

Example freshen_self_reference :
  freshen_substitutions [] (NESub (NVar 0) 0 (NVar 0)) = NESub (NVar 1) 1 (NVar 0).
Proof. reflexivity. Qed.

Fixpoint substitution_fresh (t : ntrm) : Prop :=
  match t with
  | NVar _ | NMVar _ _ => True
  | NApp a b => substitution_fresh a /\ substitution_fresh b
  | NLam _ a => substitution_fresh a
  | NESub a x u => ~ In x (nfv u) /\ substitution_fresh a /\ substitution_fresh u
  end.

Lemma rename_bound_fresh : forall t x y,
  x <> y -> ~ In y (nvars t) -> substitution_fresh t ->
  substitution_fresh (rename_bound x y t).
Proof.
  induction t; intros x y Hxy Hy Hfresh; simpl in *; try exact I.
  - rewrite in_app_iff in Hy. destruct Hfresh as [Ha Hb].
    split; [apply IHt1 | apply IHt2]; tauto.
  - destruct (Nat.eqb a x) eqn:E; [exact Hfresh |].
    apply IHt; tauto.
  - destruct Hfresh as [Hax [Ha Hu]].
    assert (Hya : ~ In y (nvars t1)) by (intro H; apply Hy; right; apply in_app_iff; left; exact H).
    assert (Hyu : ~ In y (nvars t2)) by (intro H; apply Hy; right; apply in_app_iff; right; exact H).
    assert (Hay : a <> y) by (intro H; apply Hy; left; exact H).
    split.
    + intro H. apply rename_bound_fv in H; try assumption. intuition congruence.
    + split.
      * destruct (Nat.eqb a x); [exact Ha |]. apply IHt1; assumption.
      * apply IHt2; assumption.
Qed.

Lemma freshen_binder_fresh : forall avoid a x u,
  substitution_fresh a -> substitution_fresh u ->
  substitution_fresh (freshen_binder avoid a x u).
Proof.
  intros avoid a x u Ha Hu. unfold freshen_binder.
  set (y := fresh_atom (x :: (nvars a ++ nvars u ++ avoid))).
  assert (Hy : ~ In y (x :: (nvars a ++ nvars u ++ avoid))) by apply fresh_atom_notin.
  simpl. split.
  - intro H. apply Hy. right. apply in_app_iff. right. apply in_app_iff. left.
    apply nfv_in_nvars. exact H.
  - split; [| exact Hu]. apply rename_bound_fresh; [| | exact Ha].
    + intro H. apply Hy. left. exact H.
    + intro H. apply Hy. right. apply in_app_iff. left. exact H.
Qed.

Theorem freshen_substitutions_fresh : forall t avoid,
  substitution_fresh (freshen_substitutions avoid t).
Proof.
  induction t; intros avoid; cbn [freshen_substitutions]; try exact I.
  - split; [apply IHt1 | apply IHt2].
  - apply IHt.
  - change (substitution_fresh (freshen_binder avoid
      (freshen_substitutions (a :: nvars t2 ++ avoid) t1) a
      (freshen_substitutions (a :: nvars (freshen_substitutions (a :: nvars t2 ++ avoid) t1) ++ avoid) t2))).
    apply freshen_binder_fresh; [apply IHt1 | apply IHt2].
Qed.

Lemma freshen_binder_avoids : forall avoid a x u,
  exists a' y, freshen_binder avoid a x u = NESub a' y u /\
    ~ In y avoid /\ ~ In y (nvars a) /\ ~ In y (nvars u) /\ y <> x.
Proof.
  intros avoid a x u. unfold freshen_binder.
  set (y := fresh_atom (x :: (nvars a ++ nvars u ++ avoid))).
  assert (Hy : ~ In y (x :: (nvars a ++ nvars u ++ avoid))) by apply fresh_atom_notin.
  exists (rename_bound x y a), y. split; [reflexivity |].
  simpl in Hy. rewrite !in_app_iff in Hy. intuition congruence.
Qed.

Print Assumptions rename_bound_fresh.
Print Assumptions freshen_binder_fresh.
Print Assumptions freshen_substitutions_fresh.
Print Assumptions freshen_binder_avoids.

Example freshen_shadowed_lambda :
  freshen_binder [] (NLam 0 (NVar 0)) 0 (NVar 1) = NESub (NLam 0 (NVar 0)) 2 (NVar 1).
Proof. reflexivity. Qed.

Example rename_nested_substitution :
  rename_bound 0 2 (NESub (NVar 0) 0 (NVar 0)) = NESub (NVar 0) 0 (NVar 2).
Proof. reflexivity. Qed.

Example freshen_annotation :
  freshen_binder [] (NMVar 9 [0; 1]) 0 (NVar 1) = NESub (NMVar 9 [2; 1]) 2 (NVar 1).
Proof. reflexivity. Qed.

Print Assumptions in_fold_max.
Print Assumptions fresh_atom_notin.
Print Assumptions nfv_in_nvars.
Print Assumptions rename_atom_in.
Print Assumptions rename_bound_fv.
Print Assumptions freshen_binder_fv.
Print Assumptions freshen_substitutions_fv.
Print Assumptions freshen_self_reference.
Print Assumptions freshen_shadowed_lambda.
Print Assumptions rename_nested_substitution.
Print Assumptions freshen_annotation.
