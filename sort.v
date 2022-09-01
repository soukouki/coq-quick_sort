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
    auto.
  case=> //.
    move=> H; rewrite -H.
    auto.
split.
  move=> x.
  case=> //.
  move=> H; rewrite -H.
  auto.
split=> //.
Qed.

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

(* 今回は時間がなかったのでやらなかったが、quick_sortを展開してleftまたはpivotまたはrightにあることを順番に確認すればいけそう *)
Lemma quick_sort_In: forall xs x,
  In x xs <-> In x (quick_sort xs).
Admitted.

(* これは割と簡単そう *)
Lemma filter_nil_In {A: Type}: forall xs f,
  filter f xs = [] <-> (forall x: A, In x xs -> f x = false).
Admitted.

Lemma quick_sort_length_0: forall xs,
  length xs = 0 -> sorted (quick_sort xs).
Proof.
move=> xs Hlength_0.
have: xs = [].
  by apply length_zero_iff_nil.
move=> H.
by rewrite H quick_sort_nil.
Qed.

Lemma quick_sort_length_1: forall xs,
  length xs = 1 -> sorted (quick_sort xs).
Proof.
move=> xs Hlength_1.
suff: exists x1, xs = [x1].
  case.
  move=> x Hxs.
  by rewrite Hxs quick_sort_one.
move: Hlength_1.
case xs => //.
move=> x1 xs' Hlength.
suff: xs' = [].
  move=> H.
  rewrite H.
  by exists x1.
move: Hlength.
have: length (x1 :: xs') = S (length xs').
  by [].
move=> H.
rewrite H Nat.succ_inj_wd.
by rewrite length_zero_iff_nil.
Qed.

Lemma quick_sort_length_ind: forall xs,
  (forall l xs', l < length xs -> sorted (quick_sort xs')) ->
  sorted (quick_sort xs).
Proof.
move=> xs Hsorted_quick_sort.
case_eq xs. 
  by rewrite quick_sort_nil.
move=> x1 xs1 Hxs.
case_eq xs1.
  by rewrite quick_sort_one.
move=> x2 xs2 Hxs1.
rewrite quick_sort_equation.
remember (quick_sort (filter (fun x : nat => x <? x1) (x2 :: xs2))) as left.
remember (quick_sort (filter (fun x : nat => x1 <=? x) (x2 :: xs2))) as right.
have: length xs = S (length (x2 :: xs2)).
  by rewrite Hxs Hxs1 /=.
move=> Hxs_length.
induction left.
- rewrite /=.
  split.
  + rewrite Heqright.
    move=> x.
    rewrite -quick_sort_In.
    rewrite filter_In.
    case.
    move=> _.
    by rewrite Nat.leb_le.
  + rewrite Heqright.
    apply (Hsorted_quick_sort (length (filter (fun x : nat => x1 <=? x) (x2 :: xs2)))).
    rewrite Hxs_length.
    by apply /Lt.le_lt_n_Sm /filter_length.
(* (head :: left) ++ x1 :: right *)
- rename a into head.
  rewrite /=.
  split.
  + move=> x.
    rewrite in_app_iff.
    case.
    * move=> Hinx_left.
      suff: sorted (head :: left).
        rewrite /=.
        case.
        move=> H _.
        by apply (H x).
      rewrite Heqleft.
      apply (Hsorted_quick_sort (length (filter (fun x0 : nat => x0 <? x1) (x2 :: xs2)))).
      rewrite Hxs_length.
      by apply /Lt.le_lt_n_Sm /filter_length.
    * move=> Hin_right.
      have: x1 = x \/ In x right.
        move: Hin_right.
        by rewrite /=.
      clear Hin_right.
      have: In head (head :: left) -> head <= x1.
        rewrite Heqleft.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite Nat.ltb_lt.
        by apply Nat.lt_le_incl.
      move=> Hhead_le_x1.
      case.
      - move=> H; rewrite -H; clear H.
        apply Hhead_le_x1.
        apply in_eq.
      - rewrite Heqright.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite Nat.leb_le.
        apply Nat.le_trans.
        apply Hhead_le_x1.
        by apply in_eq.
  + apply IHleft.
    




Admitted.

Theorem quick_sort_length_ind': forall xs,
  (forall xs', S (length xs') = length xs -> sorted (quick_sort xs'))
  -> sorted (quick_sort xs).
Proof.
move=> xs Hlength_sorted.
set (a := fun l => (forall xs', l = length xs' -> sorted (quick_sort xs'))).
apply (le_ind (length xs) (fun l: nat => (forall xs', length xs' <= l -> sorted (quick_sort xs')))).


induction xs.
  by rewrite quick_sort_nil.
move=> Hlength_pred.v
rename a into x1.
rename xs into xs1.
apply quick_sort_length_ind.
(* xs'は、長さがxsよりも短い全てのリスト *)
move=> l xs' Hlength.
specialize (Hlength_pred xs').



















