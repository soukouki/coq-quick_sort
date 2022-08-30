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

Lemma sorted_ind: forall x1 x2 xs2,
  sorted (x2 :: xs2) ->
  x1 <= x2 ->
  sorted (x1 :: x2 :: xs2).
Proof.
by [].
Qed.

Lemma sorted_ind_inv: forall x1 x2 xs2,
  sorted (x1 :: x2 :: xs2) -> sorted (x2 :: xs2) /\ x1 <= x2.
Proof.
move=> x1 x2 xs2 Hsorted.
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

Lemma sorted_min: forall x1 xs,
  sorted (x1 :: xs) -> (forall x, In x xs -> x1 <= x).
Proof.
move=> x1 xs Hsorted x Hinx.
move: (in_split x xs) => Hin_split.
move: Hin_split.
case=> //.
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

(* 命名とsorted_ind_invとの違いがキモい *)
Lemma sorted_min_inv: forall x1 xs,
  (forall x, In x xs -> x1 <= x) ->
  sorted xs ->
  sorted (x1 :: xs).
Proof.
move=> x1 xs Hmin Hsorted.
case_eq xs=> //.
move=> x2 xs2.
move=> Hxs.
split.
- apply (Hmin x2).
  rewrite Hxs /=.
  by left.
- by rewrite -Hxs.
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

(* TODO: x1 :: xs1の形に変える *)
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
  move: Hx1_le_x2.
  by rewrite Nat.leb_le.
+ move=> Hx2_le_x1.
  rewrite /=.
  rewrite quick_sort_equation /=.
  rewrite Hx2_le_x1.
  rewrite quick_sort_one quick_sort_nil /=.
  split=> //=.
  move: Hx2_le_x1.
  rewrite Nat.leb_gt.
  by apply Nat.lt_le_incl.
Qed.

Lemma partition_true_forall {A: Type}: forall (f: A -> bool) (xs: list A),
  (forall x, In x xs -> f x = true) -> partition f xs = (xs, []).
Proof.
induction xs=> //=.
rename a into x1.
move=> Hf_true.
rewrite IHxs.
- suff: f x1 = true.
    by [move=> H; rewrite H].
  apply Hf_true.
  by left.
- move=> x Hin.
  apply Hf_true.
  by right.
Qed.

Lemma quick_sort_min_head_stand: forall x1 xs,
  (forall x, In x xs -> x1 <= x) ->
  exists xs', x1 :: xs' = quick_sort (x1 :: xs).
Proof.
induction xs.
  move=> Hmin.
  exists [].
  by rewrite quick_sort_one.
rename a into x2.
move=> Hmin.
rewrite quick_sort_equation.
rewrite partition_true_forall.
  rewrite quick_sort_nil /=.
  by exists (quick_sort (x2 :: xs)).
move=> x Hx_in.
rewrite Nat.leb_le.
by apply Hmin.
Qed.

Lemma quick_sort_in: forall xs x,
  In x xs <-> In x (quick_sort xs).
Proof.
split.
- 
  induction xs=> //.
  rename a into x1.
  induction xs; try rewrite quick_sort_one //.
  rename a into x2.
  rewrite quick_sort_equation.
  

流れ
x = x1 \/ In x left \/ In x right.



Lemma quick_sort_inv: forall x1 xs,
  sorted (x1 :: quick_sort xs) ->
  sorted (quick_sort (x1 :: xs)).
Proof.
move=> x1 xs Hsorted.
have: (forall x, In x (quick_sort xs) -> x1 <= x).
  by apply sorted_min.
move=> Hmin.
move: quick_sort_min_head_stand => head_stand.
specialize (head_stand x1 xs).
have: exists xs', x1 :: xs' = quick_sort (x1 :: xs).
  apply head_stand.
  

case.
move=> xs' Hxs'.
rewrite Hxs'.



Lemma quick_sort_min_first: forall x1 xs,
  (forall x, In x xs -> x1 <= x) ->
  sorted (quick_sort (x1 :: xs)).
Proof.
induction xs.
  by rewrite quick_sort_one.
move=> Hx1_le_x2_and_xs.
rename a into x2.
rewrite quick_sort_equation /=.
have: x1 <=? x2 = true.
  rewrite Nat.leb_le.
  apply (Hx1_le_x2_and_xs x2).
  by apply in_eq.
move=> H; rewrite H; clear H.
rewrite partition_true_forall.
- rewrite quick_sort_equation.
  suff: sorted (x1 :: quick_sort (x2 :: xs))=> //.





  case_eq (quick_sort (x2 :: xs))=> //.
  move=> x3 xs3 Hquick_sort.
  apply sorted_ind.
  + move: (sorted_min x3 xs3) => H.
    apply H.



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
  by apply quick_sort_sorted_two.
rename a into x3.
move: IHxs => IHxs3.
(* 帰納法のinduction step *)
partitionまで遡ったらなにか見えたりしないかな・・・・

できることとできないこと
できる
- 決まった要素数に対して、sorted(quick_sort)
困り
- xsあるから、quick_sort xsの、例えば先頭にxsの要素が来るかも知れない
  - つまり、quick_sort後の並びについて直接扱えない
  - sorted(quick_sort)に対する補題を考えて、その上で処理するしかない
    - 紙に書いたような処理をするための補題を考えていくしか無い








