(** Miscellaneous additions to mathcomp and finmap *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun finset.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Fold.

Variables (T : Type) (S : Type).

Implicit Types (f : T -> S -> S) (x : T) (y : S) (s : seq T).

Definition commutative_act f :=
  forall x1 x2 y, f x1 (f x2 y) = f x2 (f x1 y).

Definition idempotent_act f :=
  forall x y, f x (f x y) = f x y.

Lemma foldr_rcons f y0 s x :
  commutative_act f ->
  foldr f (f x y0) s = f x (foldr f y0 s).
Proof.
move=> fC ;elim: s => /= [|x' s IH]; rewrite ?cats0 //.
by rewrite IH 1?fC ?inE ?eqxx /= ?orbT // => x1 x2 x1_in x2_in y.
Qed.

Lemma foldrC f y0 s1 s2 :
  commutative_act f ->
  foldr f y0 (s1 ++ s2) = foldr f y0 (s2 ++ s1).
Proof.
move=> fC; rewrite !foldr_cat.
by elim: s1 => // x s1 IH /= in fC *; rewrite foldr_rcons ?IH //.
Qed.

End Fold.

Section FoldPerm.

Variables (T : eqType) (S : Type).

Implicit Types (f : T -> S -> S) (x : T) (y : S) (s : seq T).

Lemma foldr_perm_eq f y0 s1 s2 :
  commutative_act f ->
  perm_eq s1 s2 ->
  foldr f y0 s1 = foldr f y0 s2.
Proof.
move=> fC; elim: s2=> [|x s2 IH] in s1 * => [/perm_nilP -> //|].
case/perm_consP=> i [] s1' [] e s1s2.
rewrite -{1}(cat_take_drop i s1) foldrC ?cat_take_drop //.
by rewrite [_ ++ _]e /= IH // => x1 x2 x1P x2P y.
Qed.

Lemma foldr_idem f y0 x s :
  commutative_act f ->
  idempotent_act f ->
  x \in s ->
  f x (foldr f y0 s) = foldr f y0 s.
Proof.
move=> fC fI x_s.
rewrite (@foldr_perm_eq _ _ s (rot (index x s) s)) // 1?perm_sym ?perm_rot //.
by rewrite rot_index //=.
Qed.

Lemma foldr_undup f y0 s :
  commutative_act f ->
  idempotent_act f ->
  foldr f y0 s = foldr f y0 (undup s).
Proof.
move=> fC fI; elim: s => //= x s ->.
by case: ifP => // x_s; rewrite foldr_idem // mem_undup.
Qed.

Lemma foldr_mem_eq f y0 s1 s2 :
  commutative_act f ->
  idempotent_act f ->
  s1 =i s2 ->
  foldr f y0 s1 = foldr f y0 s2.
Proof.
move=> fC fI s1s2.
rewrite [LHS]foldr_undup // [RHS]foldr_undup //.
apply: foldr_perm_eq => //.
by apply: uniq_perm; rewrite ?undup_uniq // => x; rewrite !mem_undup.
Qed.

End FoldPerm.
