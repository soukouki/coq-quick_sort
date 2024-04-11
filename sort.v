Require Import List PeanoNat FunInd Arith.Wf_nat Recdef.
Import ListNotations.
From mathcomp Require Import ssreflect.

Module Sort.

(* ソートされている性質。累積帰納法と相性が良いように定義した *)
Fixpoint sorted (xs: list nat): Prop :=
  match xs with
  | [] => True
  | x1 :: xs1 => (forall x, In x xs1 -> x1 <= x) /\ sorted xs1
  end.

Example sorted_example1:
  sorted ([1; 2; 3]).
Proof.
repeat split => //=; move=> x.
- move=> [<- | [<- | H]] => //; by auto.
- case => // <-; by auto.
Qed.

(* 上のsortedの定義は少しややこしいので、もっとシンプルな定義と同値なことを証明しておきます *)
Fixpoint sorted_simple (xs: list nat): Prop :=
  match xs with
  | [] => True
  | x1 :: [] => True
  | x1 :: (x2 :: _) as xs' => x1 <= x2 /\ sorted_simple xs'
  end.

Definition length_sorted_simple(l: nat) :=
  forall xs, l = length xs -> sorted_simple xs -> sorted xs.

Theorem sorted_simple_iff: forall xs,
  sorted xs <-> sorted_simple xs.
Proof.
move=> xs.
split.
- induction xs => //=.
  rename a into x1.
  case.
  move=> Hx1_le_xs Hxs_sorted.
  case_eq xs => //.
  move=> x2 xs2 Hxs.
  rewrite -Hxs.
  split.
  + apply Hx1_le_xs.
    rewrite Hxs /=.
    by left.
  + by apply IHxs.
- apply: (lt_wf_ind (length xs) length_sorted_simple) => //.
  clear xs.
  move=> l.
  rewrite /length_sorted_simple.
  move=> Hlength_lt_sorted xs H Hsorted_simple.
  subst.
  case_eq xs => //=.
  move=> x1 xs1 Hxs.
  split.
  + move: Hsorted_simple.
    rewrite Hxs /=.
    case_eq xs1 => //.
    move=> x2 xs2 Hxs1.
    case.
    move=> Hx1_le_x2 Hsorted_simple_xs1 x.
    rewrite /=.
    case.
      by move=> H; rewrite -H.
    move=> Hx_in_xs2.
    apply (Nat.le_trans x1 x2 x) => //.
    suff: sorted xs1.
      rewrite Hxs1 /=.
      case.
      move=> H _.
      by apply H.
    apply (Hlength_lt_sorted (length xs1)) => //.
    * by rewrite Hxs /=.
    * by rewrite Hxs1.
  + apply (Hlength_lt_sorted (length xs1)) => //.
    * by rewrite Hxs /=.
    * move: Hsorted_simple.
      rewrite Hxs /=.
      case_eq xs1 => //.
      move=> x2 xs2 Hxs1.
      by case.
Qed.

Lemma filter_length {A: Type} : forall (xs: list A) f,
  length (filter f xs) <= length xs.
Proof.
move=> xs f.
induction xs => //.
rewrite /=.
case (f a) => /=.
- by rewrite -Nat.succ_le_mono.
- by apply Nat.le_le_succ_r.
Qed.

Function quick_sort (xs: list nat) {measure length}: list nat :=
  match xs with
  | [] => []
  | pivot :: xs1 =>
    let right := filter (fun x => x <? pivot) xs1 in
    let left := filter (fun x => pivot <=? x) xs1 in
      (quick_sort right) ++ pivot :: (quick_sort left)
  end.
Proof.
(* xs = pivot :: xs1 *)
move=> xs pivot xs1 Hxs.
rewrite /=.
apply Nat.lt_succ_r.
by apply filter_length.

move=> xs pivot xs1 Hxs.
rewrite /=.
apply Nat.lt_succ_r.
by apply filter_length.
Qed.

Example quick_sort_example:
  quick_sort [3; 4; 1; 4; 2] = [1; 2; 3; 4; 4].
Proof.
rewrite quick_sort_equation /=.
rewrite 2!quick_sort_equation /=.
rewrite 2!quick_sort_equation /=.
rewrite quick_sort_equation /=.
rewrite 2!quick_sort_equation /=.
by rewrite quick_sort_equation.
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
rewrite quick_sort_equation /=.
by rewrite quick_sort_equation.
Qed.

Lemma sorted_app: forall l r,
  sorted l -> sorted r -> (forall lx rx, In lx l -> In rx r -> lx <= rx) ->
  sorted (l ++ r).
Proof.
move=> l r Hsorted_l Hsorted_r Hlx_le_rx.
induction l as [|l1] => //.
rewrite -app_comm_cons.
rewrite /=.
split.
- (* x is a element of l ++ r *)
  move=> x Hin_x.
  have: In x l \/ In x r.
    by rewrite -in_app_iff.
  case.
  + move=> Hx_in.
    move: Hsorted_l.
    rewrite /=.
    case => H _.
    by apply H.
  + apply Hlx_le_rx.
    by apply in_eq.
- apply IHl.
  + by apply Hsorted_l.
  + move=> lx rx Hlx_in Hrx_in.
    apply Hlx_le_rx => //.
    rewrite /=.
    by right.
Qed.

Lemma filter_negb_In {A: Type}: forall xs (x: A) f g,
  In x xs ->
  (forall x', g x' = negb (f x')) ->
  In x (filter f xs) \/ In x (filter g xs).
Proof.
move=> xs x f g Hxin.
case_eq (f x) => Hfx.
- left.
  rewrite filter_In.
  by split => //.
- right.
  rewrite filter_In.
  split => //.
  rewrite H.
  by rewrite Bool.negb_true_iff.
Qed.

Lemma quick_sort_In_ind: forall xs x,
  (forall xs', length xs' < length xs -> (In x xs' <-> In x (quick_sort xs'))) ->
  (In x xs <-> In x (quick_sort xs)).
Proof.
move=> xs x Hquick_sort_In_length.
split.
- case_eq xs => //.
  move=> x1 xs1 Hxs.
  rewrite -{1}Hxs => Hxin.
  rewrite quick_sort_equation.
  remember (quick_sort (filter (fun x0 : nat => x0 <? x1) xs1)) as left.
  remember (quick_sort (filter (fun x0 : nat => x1 <=? x0) xs1)) as right.
  rewrite in_app_iff.
  suff: x1 = x \/ In x (left ++ right).
    rewrite /=.
    + case.
      by right; left.
    + rewrite in_app_iff.
      case.
      * by left.
      * by right; right.
  suff: In x xs -> x1 = x \/ In x xs1.
    case => //.
    + by left.
    + right.
      rewrite in_app_iff Heqleft Heqright.
      rewrite -Hquick_sort_In_length.
      rewrite -Hquick_sort_In_length.
      * apply (filter_negb_In xs1 x) => // x'.
        by apply Nat.leb_antisym.
      * rewrite Hxs.
        by apply /Lt.le_lt_n_Sm /filter_length.
      * rewrite Hxs /=.
        by apply /Lt.le_lt_n_Sm /filter_length.
  by rewrite Hxs /=.
- case_eq xs.
    by rewrite quick_sort_nil.
  move=> x1 xs1 Hxs.
  rewrite quick_sort_equation.
  rewrite in_app_iff.
  case => /=.
  + rewrite -Hquick_sort_In_length.
    * rewrite filter_In /=.
      case.
      by right.
    * rewrite Hxs.
      by apply /Lt.le_lt_n_Sm /filter_length.
  + case.
    * by left.
    * rewrite -Hquick_sort_In_length.
      - rewrite filter_In.
        case.
        by right.
      - rewrite Hxs.
        by apply /Lt.le_lt_n_Sm /filter_length.
Qed.

Definition length_quick_sort_In(l: nat) :=
  forall xs x, l = length xs -> In x xs <-> In x (quick_sort xs).

Lemma quick_sort_In: forall xs x,
  In x xs <-> In x (quick_sort xs).
Proof.
move=> xs x.
apply (lt_wf_ind (length xs) length_quick_sort_In) => // l.
rewrite /length_quick_sort_In => Hlength_lt_In xs1 x1 Hxs1_length.
subst.
apply quick_sort_In_ind => xs2 Hxs2.
apply (Hlength_lt_In (length xs2)) => //.
Qed.

Lemma quick_sort_sorted_length_ind: forall xs,
  (forall xs', length xs' < length xs -> sorted (quick_sort xs')) ->
  sorted (quick_sort xs).
Proof.
move=> xs Hsorted_quick_sort.
case_eq xs.
  by rewrite quick_sort_nil.
move=> x1 xs1 Hxs.
rewrite quick_sort_equation.
have: length xs = S (length xs1).
  by rewrite Hxs.
move=> Hxs_length.
remember (quick_sort (filter (fun x : nat => x1 <=? x) xs1)) as right.
case_eq (quick_sort (filter (fun x : nat => x <? x1) xs1)).
- rewrite /=.
  split.
  + move=> x.
    rewrite Heqright.
    rewrite -quick_sort_In.
    rewrite filter_In.
    case => _.
    by rewrite Nat.leb_le.
  + rewrite Heqright.
    apply Hsorted_quick_sort.
    rewrite Hxs_length.
    by apply /Lt.le_lt_n_Sm /filter_length.
(* (head :: left) ++ x1 :: right *)
- move=> head left Heqleft /=.
  split.
  + move=> x.
    rewrite in_app_iff.
    case.
    * move=> Hinx_left.
      suff: sorted (head :: left).
        rewrite /=.
        case.
        move=> H _.
        by apply H.
      rewrite -Heqleft.
      apply Hsorted_quick_sort.
      rewrite Hxs_length.
      by apply /Nat.lt_succ_r /filter_length.
    * rewrite /=.
      have: head <= x1.
        move: (in_eq head left).
        rewrite -Heqleft.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite Nat.ltb_lt.
        by apply Nat.lt_le_incl.
      move=> Hhead_le_x1.
      case.
      - move=> H; rewrite -H; clear H.
        by apply Hhead_le_x1.
      - rewrite Heqright.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite Nat.leb_le.
        apply Nat.le_trans.
        by apply Hhead_le_x1.
  + apply sorted_app.
    * suff: sorted (head :: left).
        by case.
      rewrite -Heqleft.
      apply Hsorted_quick_sort.
      rewrite Hxs_length.
      by apply /Nat.lt_succ_r /filter_length.
    * rewrite Heqright.
      rewrite /=.
      split.
      - move=> x.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case.
        by rewrite Nat.leb_le.
      - apply Hsorted_quick_sort.
        rewrite Hxs_length.
        by apply /Nat.lt_succ_r /filter_length.
    * move=> lx rx Hlx Hrx.
      apply Nat.le_trans with (m := x1).
      - have: In lx (head :: left).
          rewrite /=.
          by right.
        rewrite -Heqleft.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        rewrite Nat.ltb_lt.
        by apply Nat.lt_le_incl.
      - move: Hrx.
        rewrite /=.
        case.
          move=> H; by rewrite H.
        rewrite Heqright.
        rewrite -quick_sort_In.
        rewrite filter_In.
        case => _.
        by rewrite Nat.leb_le.
Qed.

Definition length_quick_sort_sorted(l: nat) :=
  forall xs, l = length xs -> sorted (quick_sort xs).

Theorem quick_sort_sorted: forall xs,
  sorted (quick_sort xs).
Proof.
move=> xs.
apply (lt_wf_ind (length xs) length_quick_sort_sorted) => // len.
rewrite /length_quick_sort_sorted.
move=> Hlength_lt_sorted xs1 Hxs1_length.
subst.
apply quick_sort_sorted_length_ind.
move=> xs2 Hxs2_length.
apply (Hlength_lt_sorted (length xs2)) => //.
Qed.



Definition count_nat := count_occ Nat.eq_dec.

(* count_occを気にせず使いたいので、置き換えるための補題 *)
Lemma count_nat_app: forall (l1 l2: list nat) (n: nat),
  count_nat (l1 ++ l2) n = count_nat l1 n + count_nat l2 n.
Proof.
move=> l1 l2 n.
by rewrite !/count_nat count_occ_app.
Qed.
Lemma count_nat_cons_eq: forall (l: list nat) (x n: nat),
  x = n -> count_nat (x :: l) n = S (count_nat l n).
Proof.
move=> l x n Hx_eq_n.
by rewrite !/count_nat count_occ_cons_eq.
Qed.
Lemma count_nat_cons_neq: forall (l: list nat) (x n: nat),
  x <> n -> count_nat (x :: l) n = count_nat l n.
Proof.
move=> l x n Hx_neq_n.
by rewrite !/count_nat count_occ_cons_neq.
Qed.

Lemma filter_negb_count_nat: forall xs f g,
  (forall x, g x = negb (f x)) ->
  (forall x, count_nat xs x = count_nat (filter f xs) x + count_nat (filter g xs) x).
Proof.
move=> xs f g Hgf n.
induction xs => //.
case_eq (f a).
- move=> Hfa_true.
  rewrite /= Hgf Hfa_true /=.
  case (Nat.eq_dec a n) => _ //.
  rewrite Nat.add_succ_l.
  by apply eq_S.
- move=> Hfa_false.
  rewrite /= Hgf Hfa_false /=.
  case (Nat.eq_dec a n) => _ //.
  rewrite Nat.add_succ_r.
  by apply eq_S.
Qed.

Lemma quick_sort_count_ind: forall xs,
  (forall xs', length xs' < length xs ->
    forall n, count_nat (quick_sort xs') n = count_nat xs' n) ->
  forall n, count_nat (quick_sort xs) n = count_nat xs n.
Proof.
move=> xs Hsorted_count n.
case_eq xs.
  by rewrite quick_sort_nil.
move=> x1 xs1 Hxs.
rewrite quick_sort_equation.
rewrite count_nat_app.
case_eq (x1 =? n).
- rewrite Nat.eqb_eq => Hx1_eq_n.
  rewrite count_nat_cons_eq => //.
  rewrite count_nat_cons_eq => //.
  rewrite Nat.add_succ_r.
  apply eq_S.
  have: forall fg, length (filter fg xs1) < length xs.
    move=> fg.
    rewrite Hxs /=.
    rewrite Nat.lt_succ_r.
    by apply filter_length.
  move=> Hfilter_length.
  rewrite Hsorted_count => //.
  rewrite Hsorted_count => //.
  rewrite -filter_negb_count_nat => //.
  move=> x.
  by apply Nat.leb_antisym.
- rewrite Nat.eqb_neq => Hx1_neq_n.
  rewrite count_nat_cons_neq => //.
  rewrite count_nat_cons_neq => //.
  have: forall fg, length (filter fg xs1) < length xs.
    move=> fg.
    rewrite Hxs /=.
    rewrite Nat.lt_succ_r.
    apply filter_length.
  move=> Hfilter_length.
  rewrite Hsorted_count => //.
  rewrite Hsorted_count => //.
  rewrite -filter_negb_count_nat => //.
  move=> x.
  by apply Nat.leb_antisym.
Qed.

Definition length_quick_sort_count(l: nat) :=
  forall xs, l = length xs -> forall n, count_nat (quick_sort xs) n = count_nat xs n.

Lemma quick_sort_count: forall xs,
  forall n, count_nat (quick_sort xs) n = count_nat xs n.
Proof.
move=> xs n.
apply (lt_wf_ind (length xs) length_quick_sort_count) => // len.
rewrite /length_quick_sort_count => Hlength_lt_sort_count xs1 Hxs1_length.
subst.
apply quick_sort_count_ind => xs2 Hxs2_length.
apply (Hlength_lt_sort_count (length xs2)) => //.
Qed.

Definition sort_algorithm (alg: list nat -> list nat) :=
  forall xs, sorted (alg xs) /\ forall n, count_nat (alg xs) n = count_nat xs n.

(*
  ということできちんとクイックソートがソートアルゴリズムであることが証明できました。
  これで安心してクイックソートを使えます！
*)
Theorem quick_sort_is_sort_algorithm: sort_algorithm quick_sort.
Proof.
rewrite /sort_algorithm => xs.
split.
- by apply quick_sort_sorted.
- by apply quick_sort_count.
Qed.

End Sort.












