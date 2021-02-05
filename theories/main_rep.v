From BraidsT Require Import CpdtTactics.
From BraidsT Require Import supp.

Require Import Bool PeanoNat List Nat.
Set Implicit Arguments.
Set Asymmetric Patterns.

(* Unset Strict Implicit. *)
(* Unset Printing Implicit Defensive. *)

Require Import ProofIrrelevance.

Require Import ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Import ListNotations.

Hint Rewrite app_nil_r : core.

Definition BNat lim := { n | n < lim }.

Module Braids.

Section Theory.

Variable N : nat.
Hypothesis large_enough : 10 < N.

Definition free_braidlike_monoid := list (BNat (pred N)).

Definition mult_fbm : free_braidlike_monoid -> free_braidlike_monoid -> free_braidlike_monoid := app (A:=_).

Hint Unfold mult_fbm : core.

Notation "x * y" := (mult_fbm x y).

Lemma braids_has_1 : exists e : free_braidlike_monoid, forall x, x * e = x /\ e * x = x.
Proof.
  unfold "*";
  exists [];
  crush.
Qed.

Lemma braids_assoc : forall (x y z : free_braidlike_monoid), (x * y) * z = x * (y * z).
Proof.
  unfold "*";
  crush.
Qed.
  
Definition ns_list (n:nat) := rev ((fix F n :=
  match n with
  | 0 => []
  | S n' => n :: (F n')
  end) n).

Lemma ns_list_len : forall n, length(ns_list n) = n.
Proof.
  intros.
  induction n.
  - trivial.
  - unfold ns_list. rewrite rev_length.
    unfold ns_list in IHn. rewrite rev_length in IHn.
    simpl. rewrite IHn. trivial.
Qed. 

Hint Rewrite ns_list_len.

Eval compute in ns_list 10.

Definition braid_perm := { perm : list nat | Permutation perm (ns_list N) }.

Lemma braid_perm_size : forall bp : braid_perm, length (proj1_sig bp) = N.
Proof.
  intros.
  destruct bp as [perm P].
  simpl. apply Permutation_length in P. rewrite ns_list_len in P. apply P.
Qed.

Lemma braid_list_len : forall l, Permutation l (ns_list N) -> length l = N.
Proof.
  intros l Hl.
  crush.
Qed.

Hint Rewrite braid_perm_size.
(* Hint Rewrite braid_list_len. *)
Hint Constructors Permutation : core.

Lemma Permutation_rev__l : forall {A} (l : list A), Permutation (rev l) l.
Proof.
  intros A.
  intros l.
  replace l with (rev (rev l)) at 2.
  apply Permutation_rev.
  apply rev_involutive.
Qed.

Print braid_perm.
Check exist.

Lemma no_empty {T} : forall i, S (S i) <= length(@nil T) -> False.
Proof.
  simpl. intros.
  inversion H.
Qed.

Lemma no_single {T} : forall i (x:T), S (S i) <= length([x]) -> False.
Proof.
  simpl. intros.
  inversion H. inversion H1.
Qed.

Notation "[[ x ]]" := (exist _ x _).
Notation "[[ x | P ]]" := (exist _ x P).

Definition optionTest : option nat := Some 4.

Definition optionTestVal : nat :=
  match optionTest with
  | None => 0
  | Some x => x
  end.

Notation "x <?- e1 ;; e2" := (match e1 with | None => None | Some x => e2 end)  (at level 50).
Notation "x <!- e1 ;; e2" := (match e1 with | None => False | Some x => e2 end)  (at level 50).

Definition optionNotationTest x : option nat :=
  y <?- optionTest;;
  Some (x + y).

Eval compute in optionNotationTest 4.

Fixpoint transpose_if_lt (l : list nat) (i : nat) : option (list nat) :=
  match l with
  | [] => None
  | [_] => None
  | (x::y::xs) => (
    match i with
    | 0 => if x <? y then Some (y :: x :: xs) else Some (x :: y :: xs)
    | S i' => (rec <?- transpose_if_lt (y::xs) i' ;; Some (x :: rec))
    end
  )
  end.

Lemma transpose_if_lt_defined : forall l i (H: S i < length l), { res | transpose_if_lt l i = Some res }.
  refine (fix F l i (H: S i < length l) {struct i} : { res | transpose_if_lt l i = Some res } := _).
  generalize l i H.
  clear l i H.
  intros l.
  refine (match l with | [] => _ | [_] => _ | (x::y::xs) => _ end); intros; try solve [clear F; crush].
  destruct i. {
  simpl. destruct (x <? y).
  - exists (y :: x :: xs). trivial.
  - exists (x :: y :: xs). trivial.
  }
  - assert (HRec: { rec | transpose_if_lt (y::xs) i = Some rec }).
    { apply F. crush. }
    Guarded.
    destruct HRec as [rec HRec]. exists (x :: rec). simpl.
    rewrite HRec. trivial.
Defined.

(*
Definition transpose_if_lt (l : list nat) (i:BNat (pred (length l))) : { l' : list nat | Permutation l' l }.
  refine ((let fix F l i : (S (S i) <= length(l)) -> { l' : list nat | Permutation l' l } :=
    match l return (S (S i) <= length(l) -> _) with
    | []  => fun H => match (no_empty H) with end
    | [x] => fun H => match (no_single H) with end
    | (x::y::xs) => fun H => (match i as m return (i = m -> _ ) with
      | (S i') => fun Heq => (match ((F (y::xs) i' _)) with | [[rec | Hind]]  => [[(x::rec)]] end)
      | 0 => fun Heq => if x <? y then [[(y::x::xs)]] else [[(x::y::xs)]]
      end) (eq_refl _)
    end in F l (proj1_sig i) _)). 
    Unshelve.
    { destruct i; crush. }
    { apply perm_swap. }
    { crush. }
    { crush. }
    { apply perm_skip. apply Hind. }
Defined.
*)

Inductive transpose_if_ltR : forall (l:list nat) (l':list nat) (i:nat), Prop :=
| transpose_if_lt_step x xs l' n (H: transpose_if_ltR xs l' n) : transpose_if_ltR (x::xs) (x::l') (S n)
| transpose_if_lt_swap x y xs (H: x < y) : transpose_if_ltR (x::y::xs) (y::x::xs) 0
| transpose_if_lt_noswap x y xs (H: ~(x < y)) : transpose_if_ltR (x::y::xs) (x::y::xs) 0.

Lemma transpose_if_lt_FtR : forall (l:list nat) i (H: S i < length l),
  l' <!- transpose_if_lt l i;;
  transpose_if_ltR l l' i.
Proof.
  refine (fix IH l i H {struct i} := _).
  generalize l i H. clear l i H.
  intros l.
  refine (match l with | [] => _ | [_] => _ | (x::y::xs) => _ end); intros; try solve [clear IH; crush].
  destruct i.
  2: { simpl. destruct (@transpose_if_lt_defined (y::xs) i).
       { crush. }
       { rewrite e. apply transpose_if_lt_step.
         refine (let IH := IH (y::xs) i _ in _).
         Unshelve.
         2: { crush. }
         rewrite e in IH. assumption.
       }
  }
  simpl. destruct (Nat.ltb_spec x y).
  { apply transpose_if_lt_swap. assumption. }
  { apply transpose_if_lt_noswap. apply le_not_lt. assumption. }
Qed.

Lemma transpose_if_lt_RtF : forall l l' i, transpose_if_ltR l l' i -> transpose_if_lt l i = Some l'.
Proof.
  intros l l' i H.
  induction H.
  - destruct xs as [| y xs].
    + exfalso. destruct n; crush.
    + simpl. rewrite IHtranspose_if_ltR. trivial.
  - simpl. destruct (Nat.ltb_spec x y). { trivial.} { apply le_not_lt in H0. contradiction. }
  - simpl. destruct (Nat.ltb_spec x y). { contradiction. } { trivial. }
Qed.

Lemma transpose_if_lt_perm : forall l i (H: S i < length l),
    { l' | transpose_if_lt l i = Some l' /\ Permutation l l' }.
Proof.
  intros l i H.
  refine (let HRel := transpose_if_lt_FtR l H in _).
  destruct (transpose_if_lt_defined l H) as [l' Hl].
  rewrite Hl in HRel.
  exists l'. split.
  - apply Hl.
  - induction HRel; try solve [  apply Permutation_refl || constructor ].
    apply perm_skip. apply IHHRel.
    { crush. }
    apply transpose_if_lt_RtF. assumption.
Defined.

Definition transpose_braid (bp : braid_perm) (i:BNat (pred N))
  : braid_perm.
  destruct bp as [l Hl].
  destruct i as [i' Hi'].
  assert (S i' < length l). { crush. }
  destruct (transpose_if_lt_perm l H).
  refine ([[x]]).
  apply perm_trans with (l':=l).
  - destruct a as [_ HP]. apply Permutation_sym. assumption.
  - assumption.
  Show Proof.
Defined.


Fixpoint pi_braid (b : free_braidlike_monoid) : braid_perm.
  refine ((match b as m return (b = m -> _) with
    | [] => fun Heq => _
    | (x::xs) => fun Heq => _
    end) (eq_refl _)).
  - refine [[ns_list N]]; trivial.
  - refine (let xs' := pi_braid xs in (transpose_braid xs' x)).
Defined.

Notation "'fbm'" := free_braidlike_monoid.

Notation "x <- e1 ;; e2" := (match e1 with [[x]] => e2 end) (at level 100).

(* Definition twice_transpose_if_ltRT (l:list nat) (n:BNat (pred (length l))) : Prop.
  refine (let l1 := @transpose_if_lt l n in _).
  destruct l1 as [l1 Hl1].
  refine (let l2 := @transpose_if_lt l n in _).
  destruct l2 as [l2 Hl2].
  destruct n as [n Hn].
  refine (let l3 := @transpose_if_lt l2 [[n]] in _).
  destruct l3 as [l3 Hl3].
  exact (l1 = l3).
  Unshelve.
  apply Permutation_length in Hl2. rewrite Hl2. assumption.
Defined.

Lemma twice_transpose_if_lt : forall l n, twice_transpose_if_ltRT l n.
Proof.
  unfold twice_transpose_if_ltRT.
  refine (fix F l n : twice_transpose_if_ltRT l n := _).
  unfold twice_transpose_if_ltRT.
  destruct n as [n Hn].
  refine ((match l as m return (l = m -> _) with
    | [] => _
    | [x] => _
    | (x::y::xs) => _
    end) eq_refl).
  - intros. exfalso. assert (2 <= length (l)); crush.
  - intros. exfalso. assert (2 <= length (l)); crush.
  - refine ((match n as m return (n = m -> _) with 
      | 0 => _
      | S n' => _
      end) eq_refl).
  2: { intros. .


 - intros. crush. try solve [clear F; crush]. *)


Lemma twice_transpose_braid_0 : forall l n,
  transpose_braid l n = (transpose_braid (transpose_braid l n) n).
Proof.
  


  intros [l Hl] [n Hn].
  generalize dependent l.
  induction n; intros l Hl.
  - refine ((match l as l' return (l' = l -> _) with [] => _ | [x] => _ | (x::y::xs) => _ end) eq_refl).
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros. subst l. destruct (x <? y) eqn:Heq.
    * unfold transpose_braid. unfold transpose_if_lt. simpl. rewrite Heq.
      assert ((y <? x) = false). { apply (lt_antisymm Heq). } rewrite H.
      apply subset_eq_compat. trivial.
    * unfold transpose_braid. unfold transpose_if_lt. simpl. rewrite Heq. rewrite Heq.
      apply subset_eq_compat. trivial.
  - refine ((match l as l' return (l' = l -> _) with [] => _ | [x] => _ | (x::y::xs) => _ end) eq_refl).
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros. subst l.
      unfold transpose_braid.
      apply transpose_if_lt_ind with .

Definition sub_b : BNat (pred N) -> BNat (pred N) -> BNat (pred N).
  intros n m.
  destruct n as [n Hn]. destruct m as [m Hm].
  exists (n - m).
  crush.
Defined.

Definition le_b : BNat (pred N) -> BNat (pred N) -> Prop.
  intros n m.
  destruct n as [n Hn]. destruct m as [m Hm].
  exact (n <= m).
Defined.

Definition lt_b : BNat (pred N) -> BNat (pred N) -> Prop.
  intros n m.
  destruct n as [n Hn]. destruct m as [m Hm].
  exact (n < m).
Defined.

Lemma lt_1_N : 1 < pred N.
Proof.
  crush.
Qed.

Inductive braid_eq : fbm -> fbm -> Prop :=
| braid_eq_refl : forall x, braid_eq x x
| braid_eq_symm : forall x y, braid_eq x y -> braid_eq y x
| braid_eq_trans : forall x y z, braid_eq x y -> braid_eq y z -> braid_eq x z
| braid_eq_idemp : forall i, braid_eq [i; i] [i]
| braid_eq_farcomm : forall i j : BNat (pred N), lt_b [[1 | lt_1_N ]] (sub_b j i) ->
      braid_eq [i; j] [j; i]
| braid_eq_braid : forall i j : (BNat (pred N)), [[1 | lt_1_N]] = (sub_b j i) -> 
      braid_eq [i; j; i] [j; i; j].

Theorem braid_eq__pi_eq : forall b1 b2, braid_eq b1 b2 -> pi_braid b1 = pi_braid b2.
Proof.
  intros.
  induction H; try solve [crush].
  - unfold pi_braid.
  assert (forall l, transpose_braid (transpose_braid l i) i = 
    transpose_braid l i).
  intros. unfold transpose_braid. 
  


End braids.











}
