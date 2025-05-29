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

Section QuantSet.

Variables T : choiceType.
Implicit Types (p : T -> bool) (x : T) (X : {fset T}).

Lemma all_fset1U p x X : all p (x |` X) = p x && all p X.
Proof.
rewrite -[RHS]/(all p (x :: X)); apply: eq_all_r => y.
by rewrite !inE.
Qed.

Lemma has_fset1U p x X : has p (x |` X) = p x || has p X.
Proof.
rewrite -[RHS]/(has p (x :: X)); apply: eq_has_r => y.
by rewrite !inE.
Qed.

End QuantSet.

Section Graph.

Local Open Scope fmap_scope.

Variables (T : choiceType) (S : Type).

Implicit Types (m : {fmap T -> S}) (x : T) (y : S).

Definition graphf m : seq (T * S) :=
  [seq (val xx, m xx) | xx <- enum {: domf m}].

Definition graphf0 : graphf [fmap] = [::].
Proof. by rewrite /graphf /= enum_fset0. Qed.

Lemma graphf_fmap (K : {fset T}) (f : {ffun K -> S}) :
  graphf (@FinMap _ _ K f) = [seq (val xx, f xx) | xx <- enum {: K}].
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

Section GraphMap.

Variables (T : choiceType) (S : Type) (R : Type).
Implicit Types (f : T -> S -> R) (m : {fmap T -> S}).

Lemma graphf_map f m :
  graphf [fmap x : domf m => f (val x) (m x)] =
  [seq (p.1, f p.1 p.2) | p <- graphf m].
Proof.
rewrite /graphf /= -map_comp /=.
by under eq_map => x do rewrite ffunE.
Qed.

End GraphMap.

Section FoldMap.

Variables (T : choiceType) (S R : Type) .
Implicit Types (f : T * S -> R -> R) (x : T) (y : S) (z : R).
Implicit Types (m : {fmap T -> S}).

Definition commutative_mact f :=
  forall x1 x2 y1 y2 z, x1 != x2 ->
    f (x1, y1) (f (x2, y2) z) = f (x2, y2) (f (x1, y1) z).

Definition idempotent_mact f :=
  forall x y1 y2 z, f (x, y1) (f (x, y2) z) = f (x, y1) z.

Lemma foldrm0 f z0 : foldr f z0 (graphf [fmap]) = z0.
Proof. by rewrite graphf0. Qed.

Lemma foldr_set f z0 m x y :
  commutative_mact f ->
  idempotent_mact f ->
  foldr f z0 (graphf m.[x <- y]) = f (x, y) (foldr f z0 (graphf m)).
Proof.
rewrite /graphf foldr_map /= => fC fI.
under eq_foldr do rewrite ffunE.
pose g1 x' z' := f (x', if x' == x then y else odflt y m.[? x']) z'.
rewrite -[LHS](foldr_map (@fsval _ _) g1); under [in RHS]eq_map => x'.
  rewrite (_ : m x' = odflt y m.[? val x']); first over.
  rewrite (in_fnd (valP x')) /=; congr (m _); exact: val_inj.
pose g2 x' z' := f (x', odflt y m.[? x']) z'.
rewrite [in RHS]foldr_map -[in RHS](foldr_map (@fsval _ _) g2).
have E (X : {fset T}) : perm_eq (map val (enum {: X})) X.
  apply: uniq_perm.
  - rewrite map_inj_uniq ?enum_uniq //; exact: val_inj.
  - by rewrite fset_uniq.
  move=> x'; apply/(sameP mapP)/(iffP idP).
  - by move=> /= x'_X; exists [` x'_X]; rewrite ?mem_enum ?inE.
  - case=> {}x' _ ->; exact: valP.
have g1C : commutative_act g1.
  move=> x1 x2 y'; rewrite /g1.
  by have [<- //|x1x2] := altP (x1 =P x2); rewrite fC.
rewrite (foldr_perm_eq _ g1C (E (x |` domf m))).
have g2C : commutative_act g2.
  move=> x1 x2 y'; rewrite /g2.
  by have [<- //|x1x2] := altP (x1 =P x2); rewrite fC.
rewrite (foldr_perm_eq _ g2C (E (domf m))).
have g1I : idempotent_act g1.
  move=> x' z; rewrite /g1; exact: fI.
rewrite foldr_fset1U_idem => //=; rewrite {1}/g1 eqxx.
have [x_m|x_m] := boolP (x \in domf m).
- rewrite -(fsetD1K x_m).
  rewrite foldr_fset1U // ?in_fsetD1 ?eqxx //.
  rewrite foldr_fset1U // ?in_fsetD1 ?eqxx //.
  rewrite /g1 /g2 eqxx !fI; congr f.
  by apply: eq_in_foldr => x' /fsetD1P [/negbTE -> x'_m] y'.
- congr f; apply: eq_in_foldr => x' x'_m y'.
  rewrite /g1 /g2; have [x'x|//] := altP eqP.
  by rewrite -x'x x'_m in x_m.
Qed.

End FoldMap.

Section FMapRect.

Variables (T : choiceType) (S : Type) (P : {fmap T -> S} -> Type).

Hypothesis P0 : P [fmap].
Hypothesis P1 : forall m, P m -> forall x y, x \notin domf m -> P m.[x <- y].

Lemma fmap_rect m : P m.
Proof.
move e: (domf m) => X.
elim/fset1U_rect: X => [|x X xX IH] in m e *.
  by move/fmap_nil: e => ->.
have x_m : x \in domf m by rewrite e fset1U1.
pose y := m.[x_m].
have {}e: domf m.[~ x] = X by rewrite domf_rem e fsetU1K.
have -> : m = m.[~ x].[x <- y].
  by rewrite -[LHS](setf_get [` x_m]) /= setf_rem1.
by apply: P1; rewrite ?e //; apply: IH.
Qed.

End FMapRect.
