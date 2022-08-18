Require Import List PeanoNat.
Import ListNotations.
From mathcomp Require Import ssreflect.

Set Implicit Arguments.

Module Sort.

Definition Sorted (xs: list nat): Prop :=
  forall x y i j: nat,
  nth_error xs i = Some x ->
  nth_error xs j = Some y ->
  i < j -> x <= y.

Local Open Scope list_scope.

Lemma length_nil {A: Type}:
  length ([]: list A) = 0.
Proof. by rewrite /length. Qed.

Lemma sorted_nil:
  Sorted [].
Proof.
rewrite /Sorted.
move=> x y i j Hx Hy H_i_lt_j.
move: Hx.
suff: nth_error ([]: list nat) i = None.
- move=> Hnth_none.
  rewrite Hnth_none.
  by [].
- apply nth_error_None.
  rewrite length_nil.
  by apply le_0_n.
Qed.

Lemma sorted_ind {A: Type} (xs: list nat) (x: nat):
  Sorted xs -> (forall y, In y xs -> x <= y) -> Sorted (x :: xs).
Proof.
move=> H_xs_sorted H_y_in_xs.
rewrite /Sorted.
move=> x0 y0 i j Hx0 Hy0 H_i_lt_j.




