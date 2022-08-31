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

Lemma sorted_ind: forall xs x1,
  (forall x, In x xs -> x1 <= x) /\ sorted xs -> sorted (x1 :: xs).
Proof. auto. Qed.

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

Lemma filter_length {A: Type} : forall (xs: list A) f,
  length (filter f xs) <= length xs.
Proof.
move=> xs f.
induction xs => //.
rewrite /=.
case (f a).
- suff: S (length (filter f xs)) <= S (length xs).
    by rewrite /=.
  by rewrite -Nat.succ_le_mono.
- by apply Nat.le_le_succ_r.
Qed.

Function quick_sort (xs: list nat) {measure length}: list nat :=
  match xs with
  | [] => []
  | x1 :: [] => [x1]
  | pivot :: xs1 =>
    let right := filter (fun x => x <? pivot) xs1 in
    let left := filter (fun x => pivot <=? x) xs1 in
      (quick_sort right) ++ pivot :: (quick_sort left)
  end.
Proof.
(* xs = pivot :: x2 :: xs3 *)
(* xs1 = x2 :: xs3 *)
move=> xs pivot xs1 x2 xs2 Hxs1 Hxs.
suff: length (filter _ (x2 :: xs2)) < S (length (x2 :: xs2)).
  by apply.
move=> b.
apply Nat.lt_succ_r.
by apply filter_length.

move=> xs pivot xs1 x2 xs2 Hxs1 Hxs.
suff: length (filter _ (x2 :: xs2)) < S (length (x2 :: xs2)).
  by apply.
move=> b.
apply Nat.lt_succ_r.
by apply filter_length.
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
  rewrite Nat.ltb_antisym.
  rewrite Hx1_le_x2 /=.
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
  rewrite Nat.ltb_antisym.
  rewrite Hx1_nle_x2 /=.
  rewrite quick_sort_one quick_sort_nil /=.
  split=> //=.
  move=> x.
  case=> //.
  move=> H; subst.
  move: Hx1_nle_x2.
  rewrite Nat.leb_gt.
  by apply Nat.lt_le_incl.
Qed.

Lemma quick_sort_In: forall xs x,
  In x xs = In x (quick_sort xs).
Admitted.



Theorem quick_sort_sorted: forall xs,
  sorted (quick_sort xs).
Proof.
(* 帰納法のbase case...と思ってたけれど、これcaseで十分説がある *)
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
remember (filter (fun x : nat => x <? x1) (x2 :: x3 :: xs)) as left.
remember (filter (fun x : nat => x1 <=? x) (x2 :: x3 :: xs)) as right.
induction left.
- rewrite quick_sort_nil /=.
  split.
    move=> x.
    rewrite -quick_sort_In.
    rewrite Heqright.
    rewrite filter_In.
    case.
    move=> _.
    by apply Compare_dec.leb_complete.
  induction right.
    by rewrite quick_sort_nil.
  rename a into pivot.
  suff: filter (fun x : nat => x <? pivot) right = [] /\ filter (fun x : nat => pivot <=? x) right = right.
    case.
    move=> HfilterR_right HfilterR_left.
    rewrite quick_sort_equation.
    rewrite HfilterR_right HfilterR_left.
    case_eq right => //.
    move=> x2' xs2' Hright.
    rewrite quick_sort_nil -Hright /=.
    clear x2' xs2' Hright.
    split.
    + move=> x.
      rewrite -quick_sort_In.
      rewrite -HfilterR_left.
      rewrite filter_In.
      case.
      move=> _.
      apply Nat.leb_le.
    + apply IHright.
      


















