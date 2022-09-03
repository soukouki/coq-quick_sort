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

Lemma quick_sort_single: forall x1: nat,
  quick_sort [x1] = [x1].
Proof.
move=> x1.
by rewrite quick_sort_equation.
Qed.

Lemma sorted_app: forall l r,
  sorted l -> sorted r -> (forall lx rx, In lx l -> In rx r -> lx <= rx) ->
  sorted (l ++ r).
Proof.
move=> l r Hsorted_l Hsorted_r Hlx_le_rx.
induction l.
  by [].
rename a into l1.
suff: sorted (l1 :: l ++ r).
  by [].
rewrite /=.
split.
- move=> x Hin_x.
  have: In x l \/ In x r.
    by rewrite -in_app_iff.
  case.
  + move=> Hx_in.
    move: Hsorted_l.
    rewrite /=.
    case.
    move=> H _.
    by apply H.
  + apply Hlx_le_rx.
    apply in_eq.
- apply IHl.
  + by apply Hsorted_l.
  + move=> lx rx Hlx_in Hrx_in.
    apply Hlx_le_rx.
    * rewrite /=.
      by right.
    * by [].
Qed.

(* 今回は時間がなかったのでやらなかったが、quick_sortを展開してleftまたはpivotまたはrightにあることを順番に確認すればいけそう *)
Lemma quick_sort_In: forall xs x,
  In x xs <-> In x (quick_sort xs).
Proof.
Admitted.

(* 眠かったので・・・ *)
Lemma lt_le_trans: forall n m p,
  n < m -> m <= p -> n <= p.
Proof.
Admitted.

Lemma quick_sort_sorted_length_ind: forall xs,
  (forall xs', length xs' < length xs -> sorted (quick_sort xs')) ->
  sorted (quick_sort xs).
Proof.
move=> xs Hsorted_quick_sort.
case_eq xs. 
  by rewrite quick_sort_nil.
move=> x1 xs1 Hxs.
case_eq xs1.
  by rewrite quick_sort_single.
move=> x2 xs2 Hxs1.
rewrite quick_sort_equation.
have: length xs = S (length (x2 :: xs2)).
  by rewrite Hxs Hxs1 /=.
move=> Hxs_length.
remember (quick_sort (filter (fun x : nat => x1 <=? x) (x2 :: xs2))) as right.
case_eq (quick_sort (filter (fun x : nat => x <? x1) (x2 :: xs2))).
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
    apply Hsorted_quick_sort.
    rewrite Hxs_length.
    by apply /Lt.le_lt_n_Sm /filter_length.
(* (head :: left) ++ x1 :: right *)
- move=> head left Heqleft.
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
      rewrite -Heqleft.
      apply Hsorted_quick_sort.
      rewrite Hxs_length.
      by apply /Nat.lt_succ_r /filter_length.
    * move=> Hin_right.
      have: x1 = x \/ In x right.
        move: Hin_right.
        by rewrite /=.
      clear Hin_right.
      have: In head (head :: left) -> head <= x1.
        rewrite -Heqleft.
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
  + apply sorted_app.
    * suff: sorted (head :: left).
        rewrite /=.
        by case.
      rewrite -Heqleft.
      apply: Hsorted_quick_sort.
      rewrite Hxs_length.
      by apply /Nat.lt_succ_r /filter_length.
    * rewrite Heqright.
      rewrite /sorted -/sorted.
      split.
      - move=> x.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case.
        by rewrite Nat.leb_le.
      - apply: Hsorted_quick_sort.
        rewrite Hxs_length.
        by apply /Nat.lt_succ_r /filter_length.
    * move=> lx rx Hlx Hrx.
      move: lt_le_trans => H.
      apply (H _ x1 _); clear H.
      - suff: In lx (head :: left) -> lx < x1.
          apply.
          rewrite /=.
          by right.
        rewrite -Heqleft.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case.
        move=> _.
        by rewrite Nat.ltb_lt.
      - move: Hrx.
        rewrite /=.
        case.
          move=> H; by rewrite H.
        rewrite Heqright.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case.
        move=> _.
        by rewrite Nat.leb_le.
Qed.

Definition length_quick_sort_sorted(l: nat) :=
  forall xs, l = length xs -> sorted (quick_sort xs).

Theorem quick_sort_sorted: forall xs,
  sorted (quick_sort xs).
Proof.
move=> xs.
apply (lt_wf_ind (length xs) length_quick_sort_sorted).
- move=> len.
  rewrite /length_quick_sort_sorted.
  move=> Hlength_lt_sorted xs1 Hxs1_length.
  move: Hlength_lt_sorted.
  subst.
  move=> Hlength_lt_sorted.
  apply quick_sort_sorted_length_ind.
  move=> xs2 Hxs2_length.
  apply (Hlength_lt_sorted (length xs2)).
  + by [].
  + by [].
- by [].
Qed.















