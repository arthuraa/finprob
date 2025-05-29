(** Miscellaneous additions to mathcomp and finmap *)

From HB Require Import structures.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq.
From mathcomp Require Import fintype finfun finset.
From mathcomp.finmap Require Import finmap.
From finprob Require Import complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope fset_scope.
Local Open Scope fmap_scope.

Arguments bigfcupP {T I r x F P}.

Section FoldSet.

Variables (T : choiceType) (S : Type).

Implicit Types (f : T -> S -> S) (x : T) (y : S) (X : {fset T}).

Lemma foldr_fset1U f y0 x X :
  commutative_act f ->
  x \notin X ->
  foldr f y0 (x |` X) = f x (foldr f y0 X).
Proof.
move=> fC xX.
suff e: perm_eq (x |` X) (x :: X) by rewrite (foldr_perm_eq _ _ e).
apply: uniq_perm; rewrite ?fset_uniq //= ?xX ?fset_uniq // => x'.
by rewrite in_fset1U inE.
Qed.

Lemma foldr_fset1U_idem f y0 x X :
  commutative_act f ->
  idempotent_act f ->
  foldr f y0 (x |` X) = f x (foldr f y0 X).
Proof.
move=> fC fI.
rewrite -[RHS]/(foldr f y0 (x :: X)); apply: foldr_mem_eq => //.
by move=> y; rewrite !in_fsetE !inE.
Qed.

Lemma foldr_fsetU_idem f y0 X1 X2 :
  commutative_act f ->
  idempotent_act f ->
  foldr f y0 (X1 `|` X2) = foldr f (foldr f y0 X2) X1.
Proof.
rewrite -foldr_cat => fC fI; apply: foldr_mem_eq => // y.
by rewrite in_fsetE mem_cat.
Qed.

End FoldSet.

Section Graph.

Local Open Scope fmap_scope.

Variables (T : choiceType) (S : Type).

Implicit Types (m : {fmap T -> S}).

Definition graphf m : seq (T * S) :=
  [seq (val x, m x) | x <- enum {: domf m}].

Definition graphf0 : graphf [fmap] = [::].
Proof. by rewrite /graphf /= enum_fset0. Qed.

Lemma graphf_fmap (K : {fset T}) (f : {ffun K -> S}) :
  graphf (@FinMap _ _ K f) = [seq (val x, f x) | x <- enum {: K}].
Proof. by []. Qed.

Definition mkfmap s : {fmap T -> S} :=
  foldr (fun p m => m.[p.1 <- p.2]) [fmap] s.

Lemma mkfmap1 x y s : mkfmap ((x, y) :: s) = (mkfmap s).[x <- y].
Proof. by []. Qed.

Lemma graphfK : cancel graphf mkfmap.
Proof.
move=> m; apply/fmapP=> x; rewrite /graphf.
case: (fndP m x)=> [x_in|x_nin].
- have: [` x_in] \in enum {: domf m} by rewrite mem_enum inE.
  elim: (enum _) => // y xs IH.
  rewrite inE; case/orP => [/eqP <-|{}/IH e].
    by rewrite fnd_set /= eqxx.
  rewrite map_cons mkfmap1 fnd_set; case: eqP => // xy.
  by congr (Some (m _)); apply/val_inj; rewrite -xy.
- elim: (enum _) => // [|y xs IH]; rewrite ?fnd_fmap0 //.
  rewrite map_cons mkfmap1 fnd_set.
  by case: ifP => // /eqP xy; rewrite xy (valP y) in x_nin.
Qed.

End Graph.
