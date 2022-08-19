Require Import List PeanoNat.
Import ListNotations.
From mathcomp Require Import ssreflect.

Set Implicit Arguments.

Module Sort.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Lemma length_nil {A: Type}:
  length ([]: list A) = 0.
Proof. by []. Qed.

Lemma length_cons {A: Type} (xs: list A) (x: A):
  length (x :: xs) = S (length xs).
Proof. by []. Qed.


Fixpoint sorted_i (x1: nat) (xs: list nat): bool :=
  match xs with
  | [] => true
  | x2 :: xs' => (x1 <=? x2) && sorted_i x2 xs'
  end.

Definition sorted (xs: list nat): bool :=
  match xs with
  | [] => true
  | x :: [] => true
  | x :: ys => sorted_i x ys
  end.

(* x0 :: x1 :: x2 :: x3 :: _*)
Lemma sorted_i_ind: forall x0 x1 xs,
  is_true (sorted_i x1 xs) ->
  x0 <= x1 ->
  is_true (sorted_i x0 (x1 :: xs)).
Proof.
move=> x0 x1 xs Hsorted Hx0_le_x1.
suff:
  xs = [] \/ (
    ( exists x2 xs', xs = x2 :: xs' -> 
      is_true ( (x1 <=? x2) && sorted_i x1 (x2 :: xs') ) ) ).
  case => /=.
  - move=> Hxs.
    rewrite Hxs /is_true Bool.andb_true_iff Nat.leb_le.
    split.
      by [].
      by [].
  - case.
    move=> x2.
    case.
    move=> xs'.
    rewrite /is_true 3!Bool.andb_true_iff.
    split.
    - by rewrite Nat.leb_le.
    - move: Hsorted.
      by rewrite /is_true.
move: Hsorted.
rewrite {1}/sorted_i.
case_eq xs.
- move=> Hxs _.
  by left.
- move=> x2 xs' Hxs.
  rewrite /is_true Bool.andb_true_iff.
  case.
  move=> Hx1_le_x2.
  case xs.









Lemma sorted_ind: forall x xs,
  is_true (sorted xs) -> (forall y, In y xs -> x <= y) -> is_true ( sorted (x :: xs) ).
Proof.
move=> x1 xs1 Hsorted Hmin.
rewrite /is_true /sorted.
case_eq xs1 => //=.
move=> x2 xs2 Hxs1.
case xs2.
- rewrite Nat.leb_le.
  specialize (Hmin x2).
  apply Hmin.
  rewrite Hxs1.
  by apply in_eq.
- move=> x3 xs3.
Restart.
move=> x1 xs1 Hsorted Hmin.
rewrite /is_true /sorted.
induction xs1.
by [].
