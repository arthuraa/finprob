(** Miscellaneous additions to mathcomp and finmap *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun finset.
From extructures Require Import ord fset.
From finprob Require Import complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.

Arguments bigcupP {T I x s P F}.

Section FoldSet.

Variables (T : ordType) (S : Type).

Implicit Types (f : T -> S -> S) (x : T) (y : S) (X : {fset T}).

Lemma foldr_fset1U f y0 x X :
  commutative_act f ->
  x \notin X ->
  foldr f y0 (x |: X) = f x (foldr f y0 X).
Proof.
move=> fC xX.
suff e: perm_eq (x |: X) (x :: X) by rewrite (foldr_perm_eq _ _ e).
apply: uniq_perm; rewrite ?uniq_fset //= ?xX ?uniq_fset // => x'.
by rewrite in_fsetU1 inE.
Qed.

Lemma foldr_fset1U_idem f y0 x X :
  commutative_act f ->
  idempotent_act f ->
  foldr f y0 (x |: X) = f x (foldr f y0 X).
Proof.
move=> fC fI.
rewrite -[RHS]/(foldr f y0 (x :: X)); apply: foldr_mem_eq => //.
by move=> y; rewrite !in_fsetU1 !inE.
Qed.

Lemma foldr_fsetU_idem f y0 X1 X2 :
  commutative_act f ->
  idempotent_act f ->
  foldr f y0 (X1 :|: X2) = foldr f (foldr f y0 X2) X1.
Proof.
rewrite -foldr_cat => fC fI; apply: foldr_mem_eq => // y.
by rewrite in_fsetU mem_cat.
Qed.

End FoldSet.
