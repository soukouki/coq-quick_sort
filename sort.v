Require Import List PeanoNat FunInd.
Import ListNotations.
From mathcomp Require Import ssreflect.

Set Implicit Arguments.

Module Sort.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Fixpoint sorted (xs: list nat): Prop :=
  match xs with
  | [] => True
  | x1 :: [] => True
  | x1 :: (x2 :: _) as xs' => x1 <= x2 /\ sorted xs'
  end.

Lemma sorted_ind: forall x1 x2 xs3,
  sorted (x2 :: xs3) ->
  x1 <= x2 ->
  sorted (x1 :: x2 :: xs3).
Proof.
by [].
Qed.

Lemma sorted_ind_inv: forall x1 x2 xs3,
  sorted (x1 :: x2 :: xs3) -> sorted (x2 :: xs3) /\ x1 <= x2.
Proof.
move=> x1 x2 xs3 Hsorted.
split.
- move: Hsorted.
  rewrite {1}/sorted.
  rewrite -/sorted.
  case.
  by [].
- move: Hsorted.
  rewrite /sorted -/sorted.
  by case.
Qed.

Lemma sorted_app: forall xas xa xb xbs,
  sorted (xas ++ xa :: []) ->
  sorted (xb :: xbs) ->
  xa <= xb ->
  sorted (xas ++ xa :: xb :: xbs).
Proof.






















