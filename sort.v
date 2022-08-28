Require Import List PeanoNat FunInd Arith.Wf_nat Recdef.
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
  generalize (xa :: xb :: xbs).
  move=> xs.
  (* sorted_invあたりを使おうかと思ったけど、appendがあるからつらい・・ *)
  rewrite /=.
  move=> H.
  split.
  + move: Hsorted_a.
    rewrite /=.
    by case.
  + by [].
Qed.

Function quick_sort (xs1: list nat) {measure length}: list nat :=
  match xs1 with
  | [] => []
  | x1 :: [] => [x1]
  | pivot :: xs2 =>
    let (left, right) := partition (Nat.leb pivot) xs2 in
      (quick_sort right) ++ (pivot :: (quick_sort left))
  end.
Proof.
(* xs1 = pivot :: x2 :: xs3 *)
(* xs2 = x2 :: xs3 *)
move=> xs1 pivot xs2 x2 xs3 Hxs2 Hxs1 left right Hpartition.
move: (partition_length (Nat.leb pivot) xs2).
rewrite Hxs2.
move=> Hlength_xs2.
specialize (Hlength_xs2 left right Hpartition).
apply (Nat.le_lt_trans (length left) (length (x2 :: xs3)) (length (pivot :: x2 :: xs3))).
- rewrite Hlength_xs2.
  apply Nat.le_add_r.
- by [].

(* leftとrightを入れ替えてもう一度同じことをする *)
move=> xs1 pivot xs2 x2 xs3 Hxs2 Hxs1 left right Hpartition.
move: (partition_length (Nat.leb pivot) xs2).
rewrite Hxs2.
move=> Hlength_xs2.
specialize (Hlength_xs2 left right Hpartition).
apply (Nat.le_lt_trans (length right) (length (x2 :: xs3)) (length (pivot :: x2 :: xs3))).
- rewrite Hlength_xs2 Nat.add_comm.
  apply Nat.le_add_r.
- by [].
Qed.

Lemma quick_sort_nil:
  quick_sort [] = [].
Proof.
by rewrite quick_sort_equation.
Qed.

Lemma quick_sort_one: forall x1,
  quick_sort [x1] = [x1].
Proof.
move=> x1.
by rewrite quick_sort_equation.
Qed.

Lemma quick_sort_two_sorted: forall x1 x2,
  sorted (quick_sort [x1; x2]).
Proof.
move=> x1 x2.
case_eq (x1 <=? x2).
+ move=> Hx1_le_x2.
  rewrite quick_sort_equation /=.
  rewrite Hx1_le_x2.
  rewrite quick_sort_nil quick_sort_one /=.
  split => //=.
  move: Hx1_le_x2.
  by rewrite Nat.leb_le.
+ move=> Hx2_le_x1.
  rewrite /=.
  rewrite quick_sort_equation /=.
  rewrite Hx2_le_x1.
  rewrite quick_sort_one quick_sort_nil /=.
  split => //=.
  move: Hx2_le_x1.
  rewrite Nat.leb_gt.
  by apply Nat.lt_le_incl.
Qed.

(* 多分これ、sortedとquick_sortを分けてやる方が楽なんじゃないかな。一旦x1<=x2<=x3みたいな形を証明して、それをさらにsortedと同等だと示す感じ *)

Theorem quick_sort_sorted: forall xs: list nat,
  sorted (quick_sort xs).
(* 帰納法のbase case *)
move=> xs.
induction xs.
  by rewrite quick_sort_nil.
rename a into x1.
rename IHxs into IHxs1.
induction xs.
  by rewrite quick_sort_one.
rename a into x2.
rename IHxs into IHxs2.
induction xs.
  by apply quick_sort_two_sorted.
rename a into x3.
move: IHxs => IHxs3.
(* 帰納法のinduction step *)












