From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction Metatheory Subsystem Substitution Parallel.

Definition next (s : nat) : nat := (s * 3 + 1) mod 97.

Fixpoint gen (fuel : nat) (s : nat) : trm * nat :=
  match fuel with
  | 0 => (FVar (s mod 5), next s)
  | S f =>
    match next s mod 6 with
    | 0 => (FVar (next s mod 5), next (next s))
    | 1 => let (a, s1) := gen f (next s) in
           let (b, s2) := gen f s1 in (App a b, next s2)
    | 2 => let (a, s1) := gen f (next s) in (Lam a, next s1)
    | 3 => let (a, s1) := gen f (next s) in
           let (b, s2) := gen f s1 in (ESub a b, next s2)
    | 4 => (BVar (next s mod 3), next (next s))
    | _ => (FVar (next s mod 5), next (next s))
    end
  end.

Fixpoint gen_list (count : nat) (s : nat) : list trm :=
  match count with
  | 0 => []
  | S c => let (t, s') := gen 3 s in t :: gen_list c s'
  end.

Lemma gen_list_length : forall count s, length (gen_list count s) = count.
Proof.
  induction count; intros s.
  - reflexivity.
  - cbn [gen_list].
    destruct (gen 3 s) as [t s'].
    cbn [length].
    rewrite IHcount. reflexivity.
Qed.

Definition check_term (t : trm) : bool :=
  forallb (fun p => has_red t (snd p)) (steps t).

Definition check_all (l : list trm) : bool := forallb check_term l.

Lemma check_term_true : forall t, check_term t = true.
Proof.
  intros t. unfold check_term.
  apply forallb_forall. intros [r s] Hp.
  apply has_red_spec. exact (steps_sound_red1 t r s Hp).
Qed.

Lemma check_all_true : forall l, check_all l = true.
Proof.
  intros l. unfold check_all.
  apply forallb_forall. intros t _. apply check_term_true.
Qed.

Example sample_agreement : check_all (gen_list 16 7) = true.
Proof. apply check_all_true. Qed.

Example sample_length : length (gen_list 16 7) = 16.
Proof. apply gen_list_length. Qed.

Lemma gen_sound : forall count seed t, In t (gen_list count seed) ->
  forall p, In p (steps t) -> red1r (fst p) t (snd p).
Proof. intros count seed t _ [r s] Hp. apply steps_sound. exact Hp. Qed.

Lemma gen_complete : forall count seed t r t', In t (gen_list count seed) ->
  red1r r t t' -> In (r,t') (steps t).
Proof. intros count seed t r t' _ H. apply steps_complete. exact H. Qed.

Lemma gen_fv_preserved : forall count seed t p, In t (gen_list count seed) ->
  In p (steps t) -> incl (fvs (snd p)) (fvs t).
Proof.
  intros count seed t [r s] _ H. simpl.
  apply (lemma_2_1_fv_preserved t s). exact (steps_sound_red1 t r s H).
Qed.

Print Assumptions gen_list_length.
Print Assumptions check_term_true.
Print Assumptions check_all_true.
Print Assumptions sample_agreement.
Print Assumptions sample_length.
Print Assumptions gen_sound.
Print Assumptions gen_complete.
Print Assumptions gen_fv_preserved.
