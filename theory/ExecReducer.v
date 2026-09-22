From Stdlib Require Import List Bool PeanoNat Lia.
Import ListNotations.

Definition atom := nat.

Inductive trm : Type :=
| BVar : nat -> trm
| FVar : atom -> trm
| App : trm -> trm -> trm
| Lam : trm -> trm
| ESub : trm -> trm -> trm.

Fixpoint fvs (t : trm) : list atom :=
  match t with
  | BVar _ => []
  | FVar x => [x]
  | App t1 t2 => fvs t1 ++ fvs t2
  | Lam t1 => fvs t1
  | ESub t1 t2 => fvs t1 ++ fvs t2
  end.

Definition in_fvs (x : atom) (t : trm) : bool :=
  existsb (Nat.eqb x) (fvs t).

Fixpoint lift (k : nat) (t : trm) : trm :=
  match t with
  | BVar n => if Nat.ltb n k then BVar n else BVar (S n)
  | FVar x => FVar x
  | App t1 t2 => App (lift k t1) (lift k t2)
  | Lam t1 => Lam (lift (S k) t1)
  | ESub t1 t2 => ESub (lift (S k) t1) (lift k t2)
  end.

Fixpoint open_rec (k : nat) (u : trm) (t : trm) : trm :=
  match t with
  | BVar n => if Nat.eqb n k then lift k u else BVar n
  | FVar x => FVar x
  | App t1 t2 => App (open_rec k u t1) (open_rec k u t2)
  | Lam t1 => Lam (open_rec (S k) u t1)
  | ESub t1 t2 => ESub (open_rec (S k) u t1) (open_rec k u t2)
  end.

Fixpoint close_rec (x : atom) (k : nat) (t : trm) : trm :=
  match t with
  | BVar n => BVar n
  | FVar y => if Nat.eqb y x then BVar k else FVar y
  | App t1 t2 => App (close_rec x k t1) (close_rec x k t2)
  | Lam t1 => Lam (close_rec x (S k) t1)
  | ESub t1 t2 => ESub (close_rec x (S k) t1) (close_rec x k t2)
  end.

Definition subst (x : atom) (u t : trm) : trm :=
  open_rec 0 u (close_rec x 0 t).

Fixpoint occurs (n : nat) (t : trm) : bool :=
  match t with
  | BVar m => Nat.eqb m n
  | FVar _ => false
  | App t1 t2 => occurs n t1 || occurs n t2
  | Lam t1 => occurs (S n) t1
  | ESub t1 t2 => occurs (S n) t1 || occurs n t2
  end.

Definition occurs0 (t : trm) : bool := occurs 0 t.

Inductive rule : Type := RB | RGc | RR.

Definition rule_eqb (r s : rule) : bool :=
  match r, s with
  | RB, RB => true
  | RGc, RGc => true
  | RR, RR => true
  | _, _ => false
  end.

Inductive zctx : Type :=
| ZTop : zctx
| ZAppL : zctx -> trm -> zctx
| ZAppR : trm -> zctx -> zctx
| ZLam : zctx -> zctx
| ZESubL : zctx -> trm -> zctx
| ZESubR : trm -> zctx -> zctx.

Fixpoint zplug (C : zctx) (k : nat) (t : trm) : trm :=
  match C with
  | ZTop => t
  | ZAppL C1 u => App (zplug C1 k t) u
  | ZAppR u C1 => App u (zplug C1 k t)
  | ZLam C1 => Lam (zplug C1 (S k) t)
  | ZESubL C1 u => ESub (zplug C1 (S k) t) u
  | ZESubR t1 C1 => ESub t1 (zplug C1 k t)
  end.

Fixpoint zplug_lift (C : zctx) (k : nat) (t : trm) : trm :=
  match C with
  | ZTop => lift k t
  | ZAppL C1 u => App (zplug_lift C1 k t) u
  | ZAppR u C1 => App u (zplug_lift C1 k t)
  | ZLam C1 => Lam (zplug_lift C1 (S k) t)
  | ZESubL C1 u => ESub (zplug_lift C1 (S k) t) u
  | ZESubR t1 C1 => ESub t1 (zplug_lift C1 k t)
  end.

Fixpoint zdecs (t : trm) (k : nat) : list zctx :=
  match t with
  | BVar n => if Nat.eqb n k then [ZTop] else []
  | FVar _ => []
  | App t1 t2 =>
      map (fun C => ZAppL C t2) (zdecs t1 k)
      ++ map (fun C => ZAppR t1 C) (zdecs t2 k)
  | Lam t1 => map ZLam (zdecs t1 (S k))
  | ESub t1 t2 =>
      map (fun C => ZESubL C t2) (zdecs t1 (S k))
      ++ map (fun C => ZESubR t1 C) (zdecs t2 k)
  end.

Definition root_steps (t : trm) : list (rule * trm) :=
  match t with
  | App (Lam body) u => [(RB, ESub body u)]
  | ESub body u =>
      (if occurs0 body then [] else [(RGc, body)])
      ++ map (fun C => (RR, ESub (zplug_lift C 0 u) u)) (zdecs body 0)
  | _ => []
  end.

Inductive ctx : Type :=
| GHole : ctx
| GAppL : ctx -> trm -> ctx
| GAppR : trm -> ctx -> ctx
| GLam : ctx -> ctx
| GESubL : ctx -> trm -> ctx
| GESubR : trm -> ctx -> ctx.

Fixpoint plug (C : ctx) (t : trm) : trm :=
  match C with
  | GHole => t
  | GAppL C1 u => App (plug C1 t) u
  | GAppR u C1 => App u (plug C1 t)
  | GLam C1 => Lam (plug C1 t)
  | GESubL C1 u => ESub (plug C1 t) u
  | GESubR t1 C1 => ESub t1 (plug C1 t)
  end.

Fixpoint positions (t : trm) : list ctx :=
  GHole ::
  match t with
  | BVar _ => []
  | FVar _ => []
  | App t1 t2 =>
      map (fun C => GAppL C t2) (positions t1)
      ++ map (fun C => GAppR t1 C) (positions t2)
  | Lam t1 => map GLam (positions t1)
  | ESub t1 t2 =>
      map (fun C => GESubL C t2) (positions t1)
      ++ map (fun C => GESubR t1 C) (positions t2)
  end.

Fixpoint at_ctx (C : ctx) (t : trm) : option trm :=
  match C, t with
  | GHole, t => Some t
  | GAppL C1 _, App t1 _ => at_ctx C1 t1
  | GAppR _ C2, App _ t2 => at_ctx C2 t2
  | GLam C1, Lam t1 => at_ctx C1 t1
  | GESubL C1 _, ESub t1 _ => at_ctx C1 t1
  | GESubR _ C2, ESub _ t2 => at_ctx C2 t2
  | _, _ => None
  end.

Definition step_at (C : ctx) (t : trm) : list (rule * trm) :=
  match at_ctx C t with
  | None => []
  | Some s => map (fun p => (fst p, plug C (snd p))) (root_steps s)
  end.

Definition steps (t : trm) : list (rule * trm) :=
  flat_map (fun C => step_at C t) (positions t).

Definition has_rule (r : rule) (l : list (rule * trm)) : bool :=
  existsb (fun p => rule_eqb r (fst p)) l.

Definition count_rule (r : rule) (l : list (rule * trm)) : nat :=
  length (filter (fun p => rule_eqb r (fst p)) l).

Definition normal_form (t : trm) : bool :=
  match steps t with [] => true | _ => false end.

Definition ex_id : trm := App (Lam (BVar 0)) (FVar 1).
Definition ex_dup : trm := App (Lam (App (BVar 0) (BVar 0))) (FVar 1).
Definition ex_dup_es : trm := ESub (App (BVar 0) (BVar 0)) (FVar 1).
Definition ex_es : trm := ESub (BVar 0) (FVar 1).
Definition ex_gc : trm := ESub (FVar 2) (FVar 1).
Definition ex_nested : trm := ESub (ESub (BVar 0) (FVar 1)) (FVar 2).

Example ex_id_beta : has_rule RB (steps ex_id) = true.
Proof. reflexivity. Qed.

Example ex_id_one_step : length (steps ex_id) = 1.
Proof. reflexivity. Qed.

Example ex_dup_beta : has_rule RB (steps ex_dup) = true.
Proof. reflexivity. Qed.

Example ex_dup_es_two_R : count_rule RR (steps ex_dup_es) = 2.
Proof. reflexivity. Qed.

Example ex_dup_es_no_Gc : has_rule RGc (steps ex_dup_es) = false.
Proof. reflexivity. Qed.

Example ex_es_R : has_rule RR (steps ex_es) = true.
Proof. reflexivity. Qed.

Example ex_es_no_Gc : has_rule RGc (steps ex_es) = false.
Proof. reflexivity. Qed.

Example ex_gc_gc : has_rule RGc (steps ex_gc) = true.
Proof. reflexivity. Qed.

Example ex_gc_no_R : has_rule RR (steps ex_gc) = false.
Proof. reflexivity. Qed.

Example ex_nested_has_gc : has_rule RGc (steps ex_nested) = true.
Proof. reflexivity. Qed.

Example ex_id_terminates : normal_form (plug GHole (FVar 5)) = true.
Proof. reflexivity. Qed.

Example fvs_lam : fvs (Lam (App (BVar 0) (FVar 1))) = [1].
Proof. reflexivity. Qed.

Example fvs_es : fvs (ESub (FVar 0) (FVar 1)) = [0; 1].
Proof. reflexivity. Qed.

Example occurs0_lam : occurs0 (Lam (BVar 0)) = false.
Proof. reflexivity. Qed.

Example occurs0_bvar : occurs0 (BVar 0) = true.
Proof. reflexivity. Qed.

Example open_basic : open_rec 0 (FVar 1) (BVar 0) = FVar 1.
Proof. reflexivity. Qed.

Example open_under_lam : open_rec 0 (FVar 1) (Lam (BVar 1)) = Lam (FVar 1).
Proof. reflexivity. Qed.

Example subst_hit : subst 0 (FVar 1) (FVar 0) = FVar 1.
Proof. reflexivity. Qed.

Example subst_miss : subst 0 (FVar 1) (FVar 2) = FVar 2.
Proof. reflexivity. Qed.

Example capture_avoid_1 :
  subst 0 (FVar 1) (Lam (BVar 0)) = Lam (BVar 0).
Proof. reflexivity. Qed.

Example capture_avoid_2 :
  subst 0 (FVar 1) (Lam (App (BVar 0) (FVar 0)))
  = Lam (App (BVar 0) (FVar 1)).
Proof. reflexivity. Qed.

Example capture_avoid_es :
  subst 0 (FVar 1) (ESub (FVar 0) (FVar 2))
  = ESub (FVar 1) (FVar 2).
Proof. reflexivity. Qed.

Print Assumptions ex_id_beta.
Print Assumptions ex_dup_es_two_R.
Print Assumptions ex_gc_gc.
Print Assumptions ex_nested_has_gc.
Print Assumptions capture_avoid_1.
Print Assumptions capture_avoid_2.
Print Assumptions capture_avoid_es.
Print Assumptions open_under_lam.
