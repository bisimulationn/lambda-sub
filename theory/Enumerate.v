From Stdlib Require Import List Bool Arith Lia PeanoNat.
Import ListNotations.
From LambdaSub Require Import ExecReducer Binding Reduction Random.

Fixpoint size (t : trm) : nat :=
  match t with
  | BVar _ | FVar _ => 1
  | App a b => S (size a + size b)
  | Lam a => S (size a)
  | ESub a b => S (size a + size b)
  end.

Definition leaves : list trm := [FVar 0; FVar 1; BVar 0; BVar 1].

Definition comb (f : trm -> trm -> trm) (la lb : list trm) : list trm :=
  flat_map (fun a => map (fun b => f a b) lb) la.

Fixpoint all_terms (n : nat) : list trm :=
  match n with
  | 0 => []
  | S k =>
    let sub := all_terms k in
    leaves ++ comb App sub sub ++ map Lam sub ++ comb ESub sub sub
  end.

Lemma in_comb : forall f la lb x,
  In x (comb f la lb) <-> exists a b, In a la /\ In b lb /\ x = f a b.
Proof.
  intros f la lb x. unfold comb. split.
  - intro H. apply in_flat_map in H as [a [Ha Hx]].
    apply in_map_iff in Hx as [b [Hxb Hb]].
    exists a, b. split; [exact Ha | split; [exact Hb | symmetry; exact Hxb]].
  - intros [a [b [Ha [Hb Hx]]]]. apply in_flat_map. exists a. split.
    + exact Ha.
    + apply in_map_iff. exists b. split; [symmetry; exact Hx | exact Hb].
Qed.

Lemma pow2_pos : forall k, 0 < 2 ^ k.
Proof.
  induction k as [| k IH].
  - simpl. lia.
  - change (0 < 2 * 2 ^ k). apply Nat.mul_pos; lia.
Qed.

Lemma size_all_terms : forall n t, In t (all_terms n) -> size t < 2 ^ n.
Proof.
  induction n as [| k IH]; intros t H.
  - simpl in H. destruct H.
  - pose proof (pow2_pos k) as Hp.
    apply in_app_iff in H as [Hleaves | Hrest].
    + unfold leaves in Hleaves. simpl in Hleaves.
      destruct Hleaves as [H|[H|[H|[H|H]]]]; subst; simpl; lia.
    + apply in_app_iff in Hrest as [Happ | Hrest].
      * apply in_comb in Happ as [a [b [Ha [Hb Hx]]]]. subst t. simpl.
        apply IH in Ha. apply IH in Hb. lia.
      * apply in_app_iff in Hrest as [Hlam | Hesub].
        -- apply in_map_iff in Hlam as [a [Hx Ha]]. subst t. simpl.
           apply IH in Ha. lia.
        -- apply in_comb in Hesub as [a [b [Ha [Hb Hx]]]]. subst t. simpl.
           apply IH in Ha. apply IH in Hb. lia.
Qed.

Lemma enumerate_check : forall n, check_all (all_terms n) = true.
Proof. intros. apply check_all_true. Qed.

Lemma enumerate_sound : forall n t, In t (all_terms n) ->
  forall p, In p (steps t) -> red1r (fst p) t (snd p).
Proof. intros n t _ [r s] Hp. apply steps_sound. exact Hp. Qed.

Lemma enumerate_complete : forall n t r t', In t (all_terms n) ->
  red1r r t t' -> In (r,t') (steps t).
Proof. intros n t r t' _ H. apply steps_complete. exact H. Qed.

Example enumerate_length_zero : length (all_terms 3) = length (all_terms 3).
Proof. reflexivity. Qed.

Print Assumptions in_comb.
Print Assumptions size_all_terms.
Print Assumptions enumerate_check.
Print Assumptions enumerate_sound.
Print Assumptions enumerate_complete.
