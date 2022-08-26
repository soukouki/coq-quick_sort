Require Import List PeanoNat FunInd Arith.Wf_nat.
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

Lemma sorted_skip: forall x1 x2 xs,
  sorted (x1 :: x2 :: xs) -> sorted (x1 :: xs).
move=> x1 x2 x.
rewrite /=.
case.
move=> Hx1_le_x2.
rename x into xs2.
case_eq xs2.
  by [].
move=> x3 xs3 Hxs2.
case.
move=> Hx2_le_x3.
move=> Hsorted.
split.
- move: (Nat.le_trans x1 x2 x3).
  apply.
  + by [].
  + by [].
by [].
Qed.

Lemma sorted_min: forall x1 xs x,
  sorted (x1 :: xs) ->
  In x xs ->
  x1 <= x.
Proof.
move=> x1 xs x Hsorted Hinx.
move: (in_split x xs) => Hin_split.
move: Hin_split.
case.
  by [].
move=> xs1.
case.
move=> xs2 Hxs.
move: Hsorted.
rewrite Hxs.
clear xs Hxs Hinx.
move: xs1.
induction xs1.
- rewrite /=.
  case.
  by [].
- rename a into x2.
  rewrite -app_comm_cons.
  move=> H.
  apply IHxs1.
  move: H.
  set xs := xs1 ++ x :: xs2.
  by apply sorted_skip.
Qed.

Lemma sorted_app: forall xas xa xb xbs,
  sorted (xas ++ [xa]) ->
  sorted (xb :: xbs) ->
  xa <= xb ->
  sorted (xas ++ xa :: xb :: xbs).
Proof.
move=> xas xa xb xbs Hsorted_a Hsorted_b Hxa_le_xb.
move: xas Hsorted_a.
induction xas.
  by [].
rename a into x1.
move=> Hsorted_a.
case_eq xas.
- move=> Hxas.
  subst.
  apply sorted_ind.
  + by apply IHxas.
  + move: Hsorted_a.
    rewrite /=.
    by case.
- move=> x2 xs2 Hxas.
  subst.
  have: sorted((x2 :: xs2) ++ xa :: xb ::xbs).
    apply IHxas.
    by apply Hsorted_a.
  clear IHxas.
  set (xs := xa :: xb :: xbs).
  (* appendがあるからつらい・・ *)
  rewrite /=.
  move=> H.
  split.
  + move: Hsorted_a.
    rewrite /=.
    by case.
  + by [].
Qed.

















