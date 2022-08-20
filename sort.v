Require Import List PeanoNat FunInd.
Import ListNotations.
From mathcomp Require Import ssreflect.

Set Implicit Arguments.

Module Sort.

Local Open Scope list_scope.
Local Open Scope bool_scope.

Function sorted (xs: list nat): bool :=
  match xs with
  | [] => true
  | x1 :: [] => true
  | x1 :: (x2 :: _) as xs' => (x1 <=? x2) && sorted xs'
  end.

(* (x1 :: x2 :: x3 :: x4 :: _) as xs *)
Lemma sorted_ind': forall x1 x2 xs3,
  sorted (x2 :: xs3) = true ->
  x1 <= x2 ->
  sorted (x1 :: x2 :: xs3) = true.
Proof.
(*
induction xsで、
- xs = []
- forall xsに対してxs=[x3, xs']
の2つに分かれてほしい
*)
move=> x1 x2 xs3.
move: x1 x2.
move: xs3.
induction xs3.
- move=> x1 x2 Hsorted Hx1_le_x2.
  rewrite /sorted Bool.andb_true_iff.
  split.
  + by rewrite Nat.leb_le.
  + by [].
- move=> x1 x2 Hsorted Hx1_le_x2.
  rename a into x3.
  rewrite /sorted.
  rewrite 2!Bool.andb_true_iff 2!Nat.leb_le.
  split.
    by [].
  split.
    move: Hsorted.
    rewrite /sorted.
    rewrite Bool.andb_true_iff Nat.leb_le.
    by apply proj1.
  rewrite -/sorted.
  suff: sorted xs3 = true.
    move=> Hxs3_sorted.
    rewrite Hxs3_sorted.
    case_eq xs3 => //=.
    move=> x4 xs4 Hxs4.
    rewrite Bool.andb_true_iff.
    split.
    + move: Hsorted.
      rewrite /sorted Hxs4 2!Bool.andb_true_iff.
      case. move=> _.
      case. move=> H _.
      by [].
    + by [].
  move: Hsorted.
  rewrite {1}/sorted Bool.andb_true_iff.
  case.
  move=> Hx2_le_x3.
  rewrite -/sorted. 
  case_eq xs3.
    by [].
  move=> x4 xs4.
  rewrite Bool.andb_true_iff.
  move=> _.
  case.
  by [].
Qed.

