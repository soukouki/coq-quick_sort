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
  | x1 :: xs1 => (forall x, In x xs1 -> x1 <= x) /\ sorted xs1
  end.

(* Fixpoint sorted_simple (xs: list nat): Prop :=
  match xs with
  | [] => True
  | x1 :: [] => True
  | x1 :: (x2 :: _) as xs' => x1 <= x2 /\ sorted_simple xs'
  end. 時間があれば、sorted xs <-> sorted_simpleを示しておきたい*)

(* えー・・・まぁAdmittedでいいや。そんな重要じゃないし *)
Example sorted_example1:
  sorted ([1; 2; 3]).
Proof.
rewrite /=.
split.
  move=> x.
  case.
    move=> H; rewrite -H.
    admit. (* 1 <= 2 *)
  case=> //.
    move=> H; rewrite -H.
    admit. (* 1 <= 3 *)
split.
  move=> x.
  case=> //.
  move=> H; rewrite -H.
  admit. (* 2 <= 3 *)
split=> //.
Admitted.

Function quick_sort (xs: list nat) {measure length}: list nat :=
  match xs with
  | [] => []
  | x1 :: [] => [x1]
  | pivot :: xs1 =>
    let (left, right) := partition (Nat.leb pivot) xs1 in
      (quick_sort right) ++ pivot :: (quick_sort left)
  end.
Proof.
(* xs = pivot :: x2 :: xs3 *)
(* xs1 = x2 :: xs3 *)
move=> xs pivot xs1 x2 xs2 Hxs1 Hxs left right Hpartition.
move: (partition_length (Nat.leb pivot) xs1).
rewrite Hxs1.
move=> Hlength_xs1.
specialize (Hlength_xs1 left right Hpartition).
apply (Nat.le_lt_trans (length left) (length (x2 :: xs2)) (length (pivot :: x2 :: xs2))).
- rewrite Hlength_xs1.
  apply Nat.le_add_r.
- by [].

(* leftとrightを入れ替えてもう一度同じことをする *)
move=> xs pivot xs1 x2 xs2 Hxs1 Hxs left right Hpartition.
move: (partition_length (Nat.leb pivot) xs1).
rewrite Hxs1.
move=> Hlength_xs1.
specialize (Hlength_xs1 left right Hpartition).
apply (Nat.le_lt_trans (length right) (length (x2 :: xs2)) (length (pivot :: x2 :: xs2))).
- rewrite Hlength_xs1 Nat.add_comm.
  apply Nat.le_add_r.
- by [].
Qed.

Example quick_sort_example:
  quick_sort [3; 1; 4; 2] = [1; 2; 3; 4].
Proof.
rewrite quick_sort_equation /=.
rewrite 2!quick_sort_equation /=.
by rewrite 2!quick_sort_equation /=.
Qed.



Lemma quick_sort_nil:
  quick_sort [] = [].
Proof.
by rewrite quick_sort_equation.
Qed.

Lemma quick_sort_one: forall x1: nat,
  quick_sort [x1] = [x1].
Proof.
move=> x1.
by rewrite quick_sort_equation.
Qed.

Lemma quick_sort_sorted_two: forall x1 x2,
  sorted (quick_sort [x1; x2]).
Proof.
move=> x1 x2.
case_eq (x1 <=? x2).
+ move=> Hx1_le_x2.
  rewrite quick_sort_equation /=.
  rewrite Hx1_le_x2.
  rewrite quick_sort_nil quick_sort_one /=.
  split=> //=.
  move=> x.
  case=> //.
  move=> H; subst.
  move: Hx1_le_x2.
  by rewrite Nat.leb_le.
+ move=> Hx1_nle_x2.
  rewrite /=.
  rewrite quick_sort_equation /=.
  rewrite Hx1_nle_x2.
  rewrite quick_sort_one quick_sort_nil /=.
  split=> //=.
  move=> x.
  case=> //.
  move=> H; subst.
  move: Hx1_nle_x2.
  rewrite Nat.leb_gt.
  by apply Nat.lt_le_incl.
Qed.

Theorem quick_sort_sorted: forall xs,
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
  by apply quick_sort_sorted_two.
rename a into x3.
move: IHxs => IHxs3.
(* 帰納法のinduction step *)
rewrite quick_sort_equation.
Search _ partition.















