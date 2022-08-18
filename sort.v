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
Proof. by []. Qed.

Lemma length_cons {A: Type} (xs: list A) (x: A):
  length (x :: xs) = S (length xs).
Proof. by []. Qed.

Lemma sorted_min (xs: list nat) (x: nat):
  Sorted (x :: xs) ->
  forall y i: nat,
  nth_error (x :: xs) i = Some y ->
  x <= y.
Proof.





(* 
Lemma nth_error_some_length {A: Type} (xs: list A) (i: nat):
  (exists (x: A), nth_error xs i = Some x) -> i < length xs.
Proof.
induction xs.
- case.
  suff: nth_error ([]: list A) i = None.
  + move=> Hnth_none.
    by rewrite Hnth_none.
  + apply nth_error_None.
    rewrite length_nil.
    by apply le_0_n.
- case.
  move=> x Hxs_some.
  rewrite length_cons.
(* ぜーんぜん解けないんだけど！？！？ *)
Abort.
 *)

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

(* Lemma sorted_ind (x: nat) (xs: list nat):
  Sorted xs -> (forall y, In y xs -> x <= y) -> Sorted (x :: xs).
Proof.
move=> Hxs_sorted Hy_in_xs.
rewrite /Sorted.
move=> x0 y0 i j Hx0 Hy0 Hi_lt_j. *)




Lemma sorted_one(x: nat):
  Sorted [x].
Proof.
rewrite /Sorted.
move=> x0 y0 i j Hx0 Hy0.
have: i = 0.
Search (nth_error _ _= Some _) In.
move: Hx0.
rewrite nth_error_In.



Lemma sorted_ind {A: Type} (xs: list nat) (x: nat):
  Sorted xs -> (forall y, In y xs -> x <= y) -> Sorted (x :: xs).
Proof.
induction xs.
move=> _ _.







