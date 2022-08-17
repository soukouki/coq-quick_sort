Require Import Uint63 PArray.
From mathcomp Require Import ssreflect.

Module Sort.

Local Open Scope uint63_scope.

Definition Sorted (arr: array nat) : Prop :=
  forall x y: nat, forall i j: int,
  x = arr.[i] ->
  y = arr.[j] ->
  is_true(i <=? j) ->
    x <= y.

Example sorted_5_5_5:
  Sorted (make 3 5%nat).
Proof.
rewrite /Sorted.
move=> x y i j Hx Hy H_i_leq_j.
rewrite Hx Hy.
by rewrite get_make get_make.
Qed.

Example sorted_1_2_4:
  Sorted (make 3 0%nat)
    .[0 <- 1%nat]
    .[1 <- 2%nat]
    .[2 <- 4%nat].
Proof.
rewrite /Sorted.

これやめたほうが良い気がする
