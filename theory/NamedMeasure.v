From Stdlib Require Import List Bool Arith Lia PeanoNat.
From Stdlib Require Import Setoid Morphisms.
Import ListNotations.
From LambdaSub Require Import NamedMeta NamedEs.

(* The measure of Appendix A of the paper.

   For a metaterm t the paper defines two functions:
     Mx(t)  an upper bound on the number of free occurrences of x that can
            give rise to redexes in sub-reducts of t,
     s(t)   the size measure used to orient the rules R, RX and Gc.
   Both discriminate on whether the body of a substitution is a chain
   X_Delta[x1/u1]...[xn/un] ending in a metavariable and the substituted
   variable belongs to the annotation Delta. We capture that shape with
   mhead below. *)

Fixpoint mhead (t : ntrm) : option (list atom) :=
  match t with
  | NMVar _ d => Some d
  | NESub a _ _ => mhead a
  | _ => None
  end.

Definition head_has (a : ntrm) (y : atom) : bool :=
  match mhead a with
  | Some d => existsb (Nat.eqb y) d
  | None => false
  end.

Fixpoint Mx (x : atom) (t : ntrm) : nat :=
  match t with
  | NVar y => if Nat.eqb y x then 1 else 0
  | NApp a b => Mx x a + Mx x b
  | NLam _ a => Mx x a
  | NMVar _ d => if existsb (Nat.eqb x) d then 1 else 0
  | NESub a y u =>
      if head_has a y
      then Mx x a + Mx y a * Mx x u
      else Mx x a + Mx x u + Mx y a * Mx x u
  end.

Fixpoint s (t : ntrm) : nat :=
  match t with
  | NVar _ => 1
  | NApp a b => s a + s b
  | NLam _ a => s a
  | NMVar _ d => length d
  | NESub a y u =>
      if head_has a y
      then s a - 1 + Mx y a * s u
      else s a + s u + Mx y a * s u
  end.

(* The counting invariant of the paper: Mx is an upper bound on the number
   of free occurrences of x. We count free occurrences directly with nocc. *)
Fixpoint nocc (x : atom) (t : ntrm) : nat :=
  match t with
  | NVar y => if Nat.eqb y x then 1 else 0
  | NApp a b => nocc x a + nocc x b
  | NLam y a => if Nat.eqb y x then 0 else nocc x a
  | NESub a y u => (if Nat.eqb y x then 0 else nocc x a) + nocc x u
  | NMVar _ d => if existsb (Nat.eqb x) d then 1 else 0
  end.

Lemma Mx_ge_0 : forall x t, 0 <= Mx x t.
Proof. intros x t. induction t; simpl; lia. Qed.

Lemma head_has_pos : forall a y, head_has a y = true -> 1 <= Mx y a.
Proof.
  intros a. induction a as [z | a1 IHa1 a2 _ | z a IHa | a1 IHa1 z u _ | X d]; intros y H.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - simpl in H. discriminate H.
  - simpl in H. simpl. destruct (head_has a1 z) eqn:E; pose proof (IHa1 y H); lia.
  - simpl in H. simpl.
    assert (Hex : existsb (Nat.eqb y) d = true).
    { unfold head_has, mhead in H. exact H. }
    rewrite Hex. lia.
Qed.

Lemma le_mul_of_one_le : forall n m, 1 <= n -> m <= n * m.
Proof.
  intros n m H. rewrite <- (Nat.mul_1_l m) at 1.
  apply Nat.mul_le_mono_r. exact H.
Qed.

Lemma nocc_le_Mx : forall x t, nocc x t <= Mx x t.
Proof.
  intros x t. induction t as [y | a IHa b IHb | y a IHa | a IHa y u IHu | X d].
  - simpl. destruct (Nat.eqb y x); lia.
  - simpl. lia.
  - simpl. destruct (Nat.eqb y x); lia.
  - simpl. destruct (head_has a y) eqn:E.
    + assert (Hpos : 1 <= Mx y a) by (apply head_has_pos; exact E).
      assert (Hnl : Mx x u <= Mx y a * Mx x u) by (apply le_mul_of_one_le; exact Hpos).
      destruct (Nat.eqb y x) eqn:Ey; lia.
    + destruct (Nat.eqb y x) eqn:Ey; lia.
  - simpl. destruct (existsb (Nat.eqb x) d); lia.
Qed.

Print Assumptions Mx_ge_0.
Print Assumptions head_has_pos.
Print Assumptions le_mul_of_one_le.
Print Assumptions nocc_le_Mx.

(* ------------------------------------------------------------------ *)
(* The missing invariants.

   The measure proof needs the reduction rules to preserve freeness, in the
   sense that a variable that is not free in a term contributes nothing
   to the measure. Concretely the paper uses

       x notin fv(t)  implies  Mx(x,t) = 0

   for the Gc case and, through Lemma A.2, for the R and RX cases. That
   property is not true on the raw named syntax: a metavariable may carry
   an annotation variable that an enclosing substitution binds. The
   metaterm X_[x][x/y] below is the smallest witness. Its free variables
   are {y}, it therefore has no free occurrence of x, yet Mx(x, .) = 1. *)

Lemma nfv_annot_bound_example :
  nfv (NESub (NMVar 9 [0]) 0 (NVar 1)) = [1].
Proof. reflexivity. Qed.

Lemma Mx_fresh_fails :
  ~ (forall x t, ~ In x (nfv t) -> Mx x t = 0).
Proof.
  intro H.
  assert (Hn : ~ In 0 (nfv (NESub (NMVar 9 [0]) 0 (NVar 1)))).
  { rewrite nfv_annot_bound_example. intros [Hc|Hc]; [discriminate Hc | destruct Hc]. }
  specialize (H 0 (NESub (NMVar 9 [0]) 0 (NVar 1)) Hn).
  compute in H. discriminate H.
Qed.

(* Lemma A.1, invariance of Mx and s under the C equation, also needs the
   invariant. The two terms below are related by C with x = 0, y = 1, y not
   free in u and x not free in v, yet their sizes and Mx values differ: the
   occurrences of 1 and 0 that sit inside the metavariable annotation but
   below the substitutions are counted by the special clauses. *)
Definition A1_t : ntrm := NMVar 0 [0; 1].
Definition A1_u : ntrm :=
  NApp (NESub (NMVar 8 [1]) 1 (NVar 3))
       (NApp (NApp (NVar 5) (NVar 6)) (NVar 7)).
Definition A1_v : ntrm := NESub (NMVar 7 [0]) 0 (NVar 4).
Definition A1_lhs : ntrm := NESub (NESub A1_t 0 A1_u) 1 A1_v.
Definition A1_rhs : ntrm := NESub (NESub A1_t 1 A1_v) 0 A1_u.

Lemma A1_C_related : Es A1_lhs A1_rhs.
Proof.
  apply Es_C with (x := 0) (y := 1).
  - intro E. discriminate E.
  - compute. intros [H|[H|[H|[H|H]]]]; try discriminate H; destruct H.
  - compute. intros [H|H]; [discriminate H | destruct H].
Qed.

Lemma A1_s_differ : s A1_lhs <> s A1_rhs.
Proof. compute. discriminate. Qed.

Lemma A1_Mx_differ : Mx 0 A1_lhs <> Mx 0 A1_rhs.
Proof. compute. discriminate. Qed.

Lemma A1_not_invariant :
  ~ (forall t u, Es t u -> s t = s u /\ forall z, Mx z t = Mx z u).
Proof.
  intro H. destruct (H A1_lhs A1_rhs A1_C_related) as [Hs _].
  apply A1_s_differ. exact Hs.
Qed.

(* The corresponding Gc step is legal in the current rule system, but the
   measure does not decrease: the redex has the same size as its reduct.
   The body is X_[x][x/y] with x in the annotation, so the special clause
   of s applies and the (bound) x in the annotation is counted by Mx,
   cancelling the subtraction of one. *)
Lemma Gc_special_nondecrease :
  s (NESub (NESub (NMVar 9 [0]) 0 (NVar 1)) 0 (NVar 2))
  = s (NESub (NMVar 9 [0]) 0 (NVar 1)).
Proof. reflexivity. Qed.

Lemma nred_Gc_special :
  nred (NESub (NESub (NMVar 9 [0]) 0 (NVar 1)) 0 (NVar 2))
       (NESub (NMVar 9 [0]) 0 (NVar 1)).
Proof.
  apply nred_Gc. simpl. intros [Hc|Hc]; [discriminate Hc | destruct Hc].
Qed.

(* A second, independent, gap: the paper states s(t) >= 1, but a
   metavariable with empty annotation has size zero. Empty annotations are
   not excluded by the raw syntax. *)
Lemma s_metavar_empty : s (NMVar 9 []) = 0.
Proof. reflexivity. Qed.

(* Rule R as currently stated has no freshness side condition on the
   substituted term, so it creates a loop, which no terminating measure can
   orient. The step below is derivable with the empty context. The paper
   excludes it through the convention that no free and bound variable of a
   term share a name: x[x/u] with x free in u is not an alpha-canonical
   metaterm. *)
Lemma nred_R_selfloop : forall x,
  nred (NESub (NVar x) x (NVar x)) (NESub (NVar x) x (NVar x)).
Proof.
  intro x. apply nred_R with (C := nHole) (phi := [x]).
  - simpl. left. reflexivity.
  - intros y Hy. simpl in Hy. destruct Hy as [Hy|[]]. subst y. simpl. left. reflexivity.
  - reflexivity.
Qed.

Theorem current_sm_not_terminating : exists t, nred t t.
Proof. exists (NESub (NVar 0) 0 (NVar 0)). apply nred_R_selfloop. Qed.

(* Consequence for Es: the modulo relation subred inherits the loop, so it
   is not terminating either without the freshness invariant. *)
Lemma subred_selfloop : forall x,
  subred (NESub (NVar x) x (NVar x)) (NESub (NVar x) x (NVar x)).
Proof. intro x. apply subred_nred. apply nred_R_selfloop. Qed.

Theorem current_subred_not_terminating : exists t, subred t t.
Proof. exists (NESub (NVar 0) 0 (NVar 0)). apply subred_selfloop. Qed.

Print Assumptions Mx_fresh_fails.
Print Assumptions A1_C_related.
Print Assumptions A1_s_differ.
Print Assumptions A1_Mx_differ.
Print Assumptions A1_not_invariant.
Print Assumptions Gc_special_nondecrease.
Print Assumptions nred_Gc_special.
Print Assumptions s_metavar_empty.
Print Assumptions nred_R_selfloop.
Print Assumptions current_sm_not_terminating.
Print Assumptions subred_selfloop.
Print Assumptions current_subred_not_terminating.
