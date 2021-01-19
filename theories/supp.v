From BraidsT Require Import CpdtTactics.

Require Import Bool PeanoNat List Nat.
Set Implicit Arguments.
Set Asymmetric Patterns.

Unset Strict Implicit.
Unset Printing Implicit Defensive.

Require Import ProofIrrelevance.

Require Import ZArith.
Require Import Coq.Sorting.Permutation.
Require Import Coq.Lists.List.
Import ListNotations.


Definition pair_ind := 
  fun (P : nat -> nat -> Prop) (f0m : forall m : nat, P 0 m)
  (fn0 : forall n : nat, P n 0) (fInd : forall n m : nat, P n m -> P (S n) (S m)) =>
fix F (n m : nat) : P n m := match n return (P n m) with
  | 0 => f0m m
  | S n' => match m return (P (S n') m) with
    | 0 => fn0 (S n')
    | S m' => fInd n' m' (F n' m')
    end
  end.

Lemma lt_antisymm : forall x y, x <? y = true -> y <? x = false.
Proof.
  intros x y H.
  apply (@pair_ind (fun x y => x <? y = true -> y <? x = false));
  try solve [crush].
Qed.

Hint Rewrite lt_antisymm : core.





























