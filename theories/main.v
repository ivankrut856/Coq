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
Require Import Coq.Program.Equality.

Import ListNotations.

Hint Rewrite app_nil_r : core.

Inductive BNat : nat ->  Set :=
| BZero : forall {n}, BNat (S n)
| BSucc : forall {n}, BNat n -> BNat (S n).

Lemma NoBNatZero : forall (b : (BNat 0)), False.
  intros b.
  refine (match b with | @BZero n => _ | @BSucc n _ => _ end); crush.
Qed.

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

(* Lemma no_empty {T} : forall i, S (S i) <= length(@nil T) -> False.
Proof.
  simpl. intros.
  inversion H.
Qed.

Lemma no_single {T} : forall i (x:T), S (S i) <= length([x]) -> False.
Proof.
  simpl. intros.
  inversion H. inversion H1.
Qed.

Lemma no_emptyT {T} : forall n : BNat (pred (length [] (A:=T))),  False.
Proof.
  simpl. intros [n H]. inversion H.
Qed.

Lemma no_singleT {T} : forall (x:T) (n : BNat (pred (length [x]))), False.
Proof.
  simpl. intros _ [n H].
  inversion H.
Qed. *)

Notation "[[ x ]]" := (exist _ x _).
Notation "[[ x | P ]]" := (exist _ x P).

Program Fixpoint transpose_if_lt (l : list nat) (i : BNat (pred (length l))) : list nat :=
  match l with
  | [] | [_] => _
  | x::y::xs =>
    match i with
    | BZero _   => if (x <? y) then y :: x :: xs else x :: y :: xs
    | BSucc _ i =>
      x :: (transpose_if_lt (y::xs) i)
    end
  end.
Next Obligation. inversion i. Defined.
Next Obligation. inversion i. Defined.
(* Next Obligation. *)
(*   intros i. simpl in i. *)
(*   refine ((match i in BNat (S n) return ( *)
(*                    match (S n) with | 0 => IDProp | S n' => n = (length xs) -> list nat end) *)
(*            with *)
(*            | BZero n' =>  fun Heq => _ *)
(*            | BSucc n' i' => fun Heq => _ *)
(*            end) eq_refl). *)
(*   + exact (if (x <? y) then y :: x :: xs else x :: y :: xs). *)
(*   + subst n'. *)
(*     exact (x :: (transpose_if_lt (y::xs) i')). *)
(* Defined. *)

Print transpose_if_lt.

Lemma transpose_if_lt_Sn (x y : nat) (l : list nat)
           (n : BNat (pred (length (y::l)))) :
  transpose_if_lt (x::y::l) (BSucc n) = x :: (transpose_if_lt (y::l) n).
Proof. reflexivity. Qed.

(* 
Definition transpose_if_lt (l : list nat) (i:BNat (pred (length l))) : list nat.
  destruct i as [i Hi].
  refine (let fix F l (i:nat) Hi {struct i}: list nat := _ in F l i Hi); clear l0 i0 Hi0.
  refine ((match l as l' return (forall i (Hi: i < (pred (length l'))), _) with
          | [] => _
          | [x] => _
          | (x::y::xs) => _
          end) i Hi); clear l i Hi.
  - intros n Hn. destruct (no_emptyT [[n | Hn]]).  
  - intros n Hn. destruct (no_singleT [[n | Hn]]).
  - intros n Hn. generalize Hn; clear Hn. refine (match n with 0 => _ | S n => _ end).
    + exact (fun _ => if (x <? y) then y :: x :: xs else x :: y :: xs).
    + refine (fun Hn => F (y::xs) n _). crush.
Defined.

Print transpose_if_lt.

 *)

Lemma transpose_if_lt_ind : forall (P : forall (l : list nat) (i : BNat (pred (length l))), Prop)
                            (H0 : (forall (x y : nat) (l : list nat), P (x::y::l) BZero))
                            (HSn : (forall (x y : nat) (l : list nat) (n : BNat (pred (length (y::l)))),
                                     P (y :: l) n -> P (x::y::l) (BSucc n))),
    forall (l : list nat) (i : BNat (pred (length l))), P l i.
Proof.
  intros.
  refine (let fix F l i {struct i} : P l i := _ in F l i); clear l0 i0.
  generalize i; clear i.
  refine (match l with | [] => _ | [x] => _ | (x::y::xs) => _ end).
  - simpl. intros i. exfalso. apply (NoBNatZero i).
  - simpl. intros i. exfalso. apply (NoBNatZero i).
  - intros i.
    Print eq_rect.
    refine (match i as m in BNat n
                  return (forall pf : n = pred (length (x :: y :: xs)),
                             eq_rect n BNat m (pred (length (x :: y :: xs))) pf = i ->
                             P (x :: y :: xs) i
                  )
            with
            | BZero n' => _
            | BSucc n' i' => _
            end eq_refl eq_refl).
    + intros pf H'. Check eq_nat_dec.
      inversion pf. subst.
      rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
      simpl.
      apply H0.
    + intros pf H. inversion pf. subst. rewrite <- Eqdep_dec.eq_rect_eq_dec by apply eq_nat_dec.
      apply HSn. apply F.
Qed.
  

Lemma transpose_if_lt_perm (l : list nat) (i:BNat (pred (length l))) :
  Permutation l (transpose_if_lt l i).
Proof.
  apply (transpose_if_lt_ind (fun l i => Permutation l (transpose_if_lt l i))).
  - simpl. intros.
    destruct (Nat.ltb_spec x y).
    { constructor. }
    { apply Permutation_refl. }
  - intros x y l0 n HInd.
    rewrite transpose_if_lt_Sn. constructor. apply HInd.
Qed.

Corollary transpose_if_lt_len l i : length (transpose_if_lt l i) = length l.
  apply Permutation_length. apply Permutation_sym. apply (transpose_if_lt_perm l i).
Qed.
    
(* 
Inductive transpose_if_ltR : forall (l:list nat) (l':list nat) (i:nat), Prop :=
| transpose_if_lt_step x xs l' n (H: transpose_if_ltR xs l' n) : transpose_if_ltR (x::xs) (x::l') (S n)
| transpose_if_lt_swap x y xs (H: x < y) : transpose_if_ltR (x::y::xs) (y::x::xs) 0
| transpose_if_lt_noswap x y xs (H: ~(x < y)) : transpose_if_ltR (x::y::xs) (x::y::xs) 0.

Lemma transpose_if_lt_FtR : forall (l:list nat) (bi:BNat (pred (length l))),
  let (i, _) := bi in
  let (l', _) := transpose_if_lt l bi in
  transpose_if_ltR l l' i.
Proof.
  intros l bi.
  destruct bi as [i Hi].
  generalize dependent l.
  induction i; intros l;
  refine ((match l as m return (l = m -> _) 
      with [] => _ | [x] => _ | (x::y::xs) => _ end) eq_refl);
  try solve [intros Hl Hi; exfalso; subst l; crush].
  Guarded.
  2:{ 
    intros Hl Hi. clear Hl; clear l0. 
    destruct (transpose_if_lt (x::y::xs) [[ S i | Hi ]]) eqn:Heq.
    cbn in Heq.
    apply transpose_if_lt_step. *)


Definition transpose_braid (bp : braid_perm) (i:BNat (pred N))
  : braid_perm.
  destruct bp as [bp Hbp].
  assert (length bp = N).
  { apply (braid_list_len Hbp). }
  refine ((match H in (_ = len) return (BNat (pred len) -> braid_perm) with
           | eq_refl => fun i => [[transpose_if_lt bp i]] end) i).
  apply Permutation_sym.
  apply perm_trans with bp.
  - apply Permutation_sym. assumption.
  - apply transpose_if_lt_perm.
Defined.

Print transpose_braid.

Definition pi_braid (b : free_braidlike_monoid) : braid_perm.
  refine (let fix pi_braid_sup (b : free_braidlike_monoid) (ini : braid_perm) : braid_perm := _ in
          pi_braid_sup b [[ns_list N]]).
  { trivial. }
  Unshelve.
  refine (match b with | [] => _ | (x::xs) => _ end).
  { exact ini. }
  exact (pi_braid_sup xs (transpose_braid ini x)).
Defined.

Print pi_braid.

Notation "'fbm'" := free_braidlike_monoid.

Notation "x <- e1 ;; e2" := (match e1 with [[x]] => e2 end) (at level 100).

Program Definition twice_transpose_if_ltRT (l : list nat) (n : BNat (pred (length l)))
  : Prop :=
  let f_once := transpose_if_lt l n in
  f_once = transpose_if_lt f_once n.
  (* let f_twice := transpose_if_lt f_once n in *)
  (* f_once = f_twice. *)
Next Obligation.
  apply f_equal_pred. rewrite transpose_if_lt_len. auto.
Defined.

Print twice_transpose_if_ltRT.

Locate "<?".

Lemma twice_transpose_if_lt l n : twice_transpose_if_ltRT l n.
Proof.
  generalize dependent n. 
  apply transpose_if_lt_ind; intros.
  2: { red. simpl in *.
       unfold twice_transpose_if_ltRT_obligation_1.
       simpl in *.
       assert (length (transpose_if_lt (y :: l0) n) = S (length l0)) as AA.
       { admit. }
       rewrite AA.

       2: admit.
       rewrite <- eq_rect_eq.

       rewrite rew_const.
       replace (eq_rect (S (length l0)) (fun H0 : nat => BNat H0) (BSucc n)
                        (length (transpose_if_lt (y :: l0) n))
                        (twice_transpose_if_ltRT_obligation_1 (x :: y :: l0) (BSucc n)))
               with (BSucc n).

rewrite transpose_if_lt_Sn.


  { red. simpl in *. unfold transpose_if_lt.

  generalize dependent n. induction l.
  { inversion n. }
  intros. red.

  inv n.
  {


  apply transpose_if_lt_ind; intros.
  { red. simpl in *. unfold transpose_if_lt.


destruct (classic (x <? y)).


destruct (Nat.ltb_spec x y).

  unfold twice_transpose_if_ltRT.
  generalize l n; clear l n.
  apply transpose_if_lt_ind.
  - intros x y l.
    destruct (Nat.ltb_spec x y).
    { 

Definition twice_transpose_if_ltRT (l:list nat) (n:BNat (pred (length l))) : Prop.
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

Print twice_transpose_if_ltRT.

Lemma twice_transpose_if_lt : forall l n, twice_transpose_if_ltRT l n.
Proof.
  unfold twice_transpose_if_ltRT.
  refine (fix F l : forall n, twice_transpose_if_ltRT l n := _).
  refine (match l with
          | [] => _
          | [x] => _
          | (x::y::xs) => _
          end).
  - intros n. exfalso.
    apply (no_emptyT n).
  - intros n. exfalso.
    apply (no_singleT n).
  - simpl. unfold twice_transpose_if_ltRT. intros [n Hn]. destruct n. {
    unfold transpose_if_lt at 1. unfold transpose_if_lt at 1. simpl.
    destruct (Nat.ltb_spec x y).
    + unfold transpose_if_lt. simpl. destruct (Nat.ltb_spec y x); crush.
    + unfold transpose_if_lt. simpl. destruct (Nat.ltb_spec x y); crush. }
  { 
  
  unfold twice_transpose_if_ltRT.
  destruct n as [n Hn].
  refine (match l with
          | [] => _
          | [x] => _
          | (x::y::xs) => _
          end).
    

  
  refine ((match l as m return (l = m -> _) with
    | [] => _
    | [x] => _
    | (x::y::xs) => _
    end) eq_refl).
  - intros. exfalso. assert (2 <= length (l)); crush.
  - intros. exfalso. assert (2 <= length (l)); crush.
  - 



    refine ((match n as m return (n = m -> _) with 
      | 0 => _
      | S n' => _
      end) eq_refl).
  2: { intros. .


 - intros. crush. try solve [clear F; crush].


Lemma twice_transpose_braid_0 : forall l n,
  transpose_braid l n = (transpose_braid (transpose_braid l n) n).
Proof.
  assert (
    forall l n, 
      let (lhs, _) := transpose_if_lt (l:=l) n in
      let (rhs, _) := (let (l', _) := transpose_if_lt (l:=l) n in 
        (transpose_if_lt (l:=l') (_ n))) in
      lhs = rhs).


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

  
  

(* Definition twice_transpose l (i : BNat (pred (length l)))
  : { l' : list nat | Permutation l' l }.
  refine (l' <- transpose_if_le l i;; _).
  refine (_ (transpose_if_le l' (_ i))).
  { intros k. destruct k as [k Hk]. exists k. apply Permutation_trans with l'; assumption. }
  { intros k. destruct k as [k Hk]. exists k. rewrite (Permutation_length p). assumption. }
Defined.

Print twice_transpose.

Lemma twice_transpose_n : forall l i,
  transpose_if_le l i = twice_transpose l i.
  intros l i. destruct i as [i Hi].
  induction i.
  - refine ((match l as l' return (l' = l -> _) with [] => _ | [x] => _ | (x::y::xs) => _ end) eq_refl).
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros. exfalso. assert (2 <= length (l)); crush.
    + intros Heq. subst l. clear l0. unfold transpose_if_le. unfold twice_transpose.
      destruct (x <=? y) eqn:Heq. simpl. rewrite Heq. *)

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











