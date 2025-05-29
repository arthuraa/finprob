(** Theory of finite probability distributions.  This file defines the {prob T}
type, which represents finite probability distributions with rational
coefficients over the type [T], which is required to be a choiceType.
Distributions form a monad, where the unit [dirac : T -> {prob T}] is the point
mass distribution, whereas the monadic bind [sample : (T -> {prob S}) -> {prob
T} -> {prob S}] samples from its first argument and feeds the sample to its
second argument. *)

Require Import Stdlib.Strings.String.
Require Import Stdlib.Unicode.Utf8.

From HB Require Import structures.

From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat choice seq
  fintype ssrint rat ssralg ssrnum bigop path finfun.

From mathcomp.finmap Require Import finmap.

From finprob Require Import complements finmap_complements.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Local Open Scope fset_scope.
Local Open Scope fmap_scope.

Declare Scope prob_scope.
Local Open Scope prob_scope.

Section Prob.

Variable T : choiceType.
Implicit Types (x : T) (X : {fset T}) (f : T -> rat).

(** We define probability distributions in two stages.  First, we define a
distribution as a map into the positive rationals that is 0 almost everywhere.
Then, we define {prob T} as the type of distributions of mass 1. *)

Record distr := Distr {
  dval :> {fsfun T -> rat with 0};
  _    :  all (fun x => 0 <= dval x) (finsupp dval)
}.
Definition distr_of & phant T := distr.
Notation "{ 'distr' T }" := (distr_of (Phant T))
  (at level 0, format "{ 'distr'  T }") : form_scope.
Identity Coercion distr_of_distr : distr_of >-> distr.

HB.instance Definition _ := [isSub of distr for dval].
HB.instance Definition _ := [Equality of distr by <:].
HB.instance Definition _ := [Choice of distr by <:].

HB.instance Definition _ := SubType.copy {distr T} distr.
HB.instance Definition _ := Equality.copy {distr T} distr.
HB.instance Definition _ := Choice.copy {distr T} distr.

Implicit Types (d : {distr T}).

Lemma eq_distr d1 d2 : d1 =1 d2 <-> d1 = d2.
Proof. by split=> [e|-> //]; apply/val_inj/fsfunP. Qed.

Lemma distr_ge0 d x : 0 <= d x.
Proof.
case: (finsuppP d x) => [//|]; apply/allP: x; exact/(valP d).
Qed.

Lemma mem_finsuppd d x : (x \in finsupp d) = (0 < d x).
Proof. by rewrite mem_finsupp Num.Theory.lt0r distr_ge0 andbT. Qed.

Definition mass d := \sum_(x <- finsupp d) d x.

Lemma massE d X :
  finsupp d `<=` X -> mass d = \sum_(x <- X) d x.
Proof.
rewrite /mass (big_fsetID _ (mem (finsupp d)) X) /= => sub.
rewrite [X in (_ + X)%R]big1_fset ?GRing.addr0.
- apply: eq_fbigl_cond => x.
  rewrite !inE !andbT andbC; case: finsuppP => // x_d.
  by rewrite (fsubsetP sub _ x_d).
- by move=> x; rewrite !inE memNfinsupp; case/andP => _ /eqP.
Qed.

Fact mkdistr_key : unit. Proof. exact: tt. Qed.

Lemma mkdistr_subproof (X : {fset T}) (f : T -> rat) :
  (forall x, x \in X -> 0 <= f x) ->
  let ff : {fsfun T -> rat with 0} := [fsfun x in X => f x] in
  all (fun x => 0 <= ff x) (finsupp ff).
Proof.
move=> /= pos; apply/allP=> x _; rewrite fsfunE.
by case: ifP=> // /pos.
Qed.

Definition mkdistr X f pos :=
  locked_with mkdistr_key
    (Distr (@mkdistr_subproof X f pos)).

Lemma mkdistrE X f pos x :
  @mkdistr X f pos x = if (x \in X) then f x else 0%R.
Proof. by rewrite /mkdistr unlock /= fsfunE. Qed.

Lemma finsupp_mkdistr X f pos :
  finsupp (@mkdistr X f pos) = [fset x in X | f x != 0].
Proof.
by apply/fsetP=> x; rewrite mem_finsupp mkdistrE !inE; case: ifP.
Qed.

Record prob :=
  Prob {pval : {distr T}; _ : mass pval == 1%R}.
Definition prob_of & phant T := prob.
Notation "{ 'prob' T }" := (prob_of (Phant T))
  (at level 0, format "{ 'prob'  T }") : form_scope.
Identity Coercion prob_of_prob : prob_of >-> prob.
Coercion pval : prob >-> distr_of.

HB.instance Definition _ := [isSub of prob for pval].
HB.instance Definition _ := [Equality of prob by <:].
HB.instance Definition _ := [Choice of prob by <:].

HB.instance Definition _ := SubType.copy {prob T} prob.
HB.instance Definition _ := Equality.copy {prob T} prob.
HB.instance Definition _ := Choice.copy {prob T} prob.

Implicit Types (p : {prob T}).

Lemma mkprob_subproof X f pos :
  \sum_(x <- X) f x = 1 ->
  mass (@mkdistr X f pos) == 1.
Proof.
move=> <-; apply/eqP.
rewrite [RHS](bigID (fun x => f x == 0)) /=.
have -> : \sum_(x <- X | f x == 0) f x = 0.
  by rewrite big1 // => x /eqP.
rewrite GRing.add0r /mass finsupp_mkdistr; apply: eq_fbig_cond => [x|x].
- by rewrite !inE andbT.
- by rewrite !inE /=; case/andP => x_X fx0 _; rewrite mkdistrE x_X.
Qed.

Fact mkprob_key : unit. Proof. exact: tt. Qed.

Definition mkprob X f pos e : {prob T} :=
  locked_with mkprob_key (Prob (@mkprob_subproof X f pos e)).

Lemma mkprobE X f pos e x :
  @mkprob X f pos e x = if x \in X then f x else 0.
Proof. by rewrite /mkprob unlock /= mkdistrE. Qed.

Lemma finsuppPrN0 p : finsupp p != fset0.
Proof.
by apply/eqP=> e; move: (eqP (valP p)); rewrite /mass e big_nil.
Qed.

Definition pchoose p : T := xchoose (fset0Pn _ (finsuppPrN0 p)).

Lemma pchoose_supp p : pchoose p \in finsupp p.
Proof. exact: xchooseP. Qed.

Definition dirac_def x x' : rat := (x == x')%:R.

Lemma dirac_subproof1 x x' : x' \in fset1 x -> 0 <= dirac_def x x'.
Proof. by rewrite /dirac_def; case: eq_op. Qed.

Lemma dirac_subproof2 x : \sum_(x' <- fset1 x) dirac_def x x' = 1.
Proof. by rewrite /= big_seq_fset1 /dirac_def eqxx. Qed.

(** Point mass distribution *)

Definition dirac x :=
  mkprob (@dirac_subproof1 x) (dirac_subproof2 x).

Lemma diracE x x' : dirac x x' = (x' == x)%:R.
Proof.
rewrite /dirac /dirac_def /= mkprobE in_fset1.
by rewrite eq_sym; case: (x == x').
Qed.

Lemma finsupp_dirac x : finsupp (dirac x) = fset1 x.
Proof.
apply/fsetP=> x'.
by rewrite mem_finsupp in_fset1 diracE; case: (x' =P x).
Qed.

Lemma finsupp_diracP x x' : reflect (x' = x) (x' \in finsupp (dirac x)).
Proof. rewrite finsupp_dirac; exact: fset1P. Qed.

Lemma dirac_inj : injective dirac.
Proof.
by move=> x y e; apply/fset1_inj; rewrite -!finsupp_dirac e.
Qed.

Lemma eq_prob p1 p2 : p1 =1 p2 <-> p1 = p2.
Proof. by split=> [/eq_distr/val_inj|-> //]. Qed.

Lemma in_eq_probL p1 p2 : {in finsupp p1, p1 =1 p2} -> p1 = p2.
Proof.
move=> e; apply/eq_prob=> x.
case: (finsuppP p1 x)=> xP; last exact: e.
have: \sum_(y <- finsupp p1) p2 y = 1.
  rewrite -(eqP (valP p1)) /mass /= big_seq [RHS]big_seq.
  by apply/eq_big=> // ? /e ->.
rewrite -(eqP (valP p2)) /mass /= [RHS](bigID (mem (finsupp p1))) /=.
have ->: \sum_(y <- finsupp p1) p2 y =
         \sum_(y <- finsupp p2 | y \in finsupp p1) p2 y.
  apply: eq_fbig_cond => // y; rewrite !inE /= andbT andbC.
  case: (finsuppP p1 y) => //= y_p1.
  by rewrite mem_finsupp -(e _ y_p1) -mem_finsupp y_p1.
rewrite -[LHS]GRing.addr0 => /GRing.addrI/esym/eqP.
rewrite Num.Theory.psumr_eq0; last by move=> ? _; rewrite distr_ge0.
case: (finsuppP p2 x) => //= x_p2.
by move=> /allP/(_ _ x_p2); rewrite xP => /eqP ->.
Qed.

Lemma in_eq_probR p1 p2 : {in finsupp p2, p1 =1 p2} -> p1 = p2.
Proof.
by move=> e; apply/esym/in_eq_probL=> x x_p2; rewrite e.
Qed.

Lemma diracK : cancel dirac pchoose.
Proof. by move=> x; have /finsupp_diracP := pchoose_supp (dirac x). Qed.

Lemma eq_finsupp_dirac p x : (finsupp p == fset1 x) = (p == dirac x).
Proof.
apply/(sameP eqP)/(iffP eqP)=> [->|e]; first exact: finsupp_dirac.
apply/in_eq_probR => _ /finsupp_diracP ->.
have:= massE (fsubset_refl (finsupp p)).
rewrite e big_seq_fset1 (eqP (valP p)) => <-; by rewrite diracE eqxx.
Qed.

End Prob.

Notation "{ 'distr' T }" := (distr_of (Phant T))
  (at level 0, format "{ 'distr'  T }") : form_scope.
Notation "{ 'prob' T }" := (prob_of (Phant T))
  (at level 0, format "{ 'prob'  T }") : form_scope.

Arguments dirac {_} x.
Arguments pchoose {_} p.
Arguments dirac_inj {_}.

Section Expectation.

Variable T : choiceType.

Implicit Types (p : {prob T}) (x y z : T) (F : T -> rat).
Implicit Types (X Y : {fset T}).

Import GRing.

Definition expect p F : rat :=
  \sum_(x <- finsupp p) F x * p x.

Notation "''E_' ( x <- p ) F" := (expect p (fun x => F))
  (at level 41, F at level 41, x, p at level 50,
    format "'[' ''E_' ( x  <-  p )  '/  ' F ']'").

Lemma expectE X p F :
  finsupp p `<=` X ->
  'E_(x <- p) F x = \sum_(x <- X) F x * p x.
Proof.
rewrite /expect => p_in_X; apply: big_fset_incl => // x x_X.
by case: finsuppP => // _ _; rewrite GRing.mulr0.
Qed.

Lemma expect_dirac x F : 'E_(y <- dirac x) F y = F x.
Proof.
by rewrite /expect finsupp_dirac /= big_seq_fset1 diracE eqxx mulr1.
Qed.

Lemma mulr_expectr r p F : r * ('E_(x <- p) F x) = 'E_(x <- p) r * F x.
Proof.
rewrite /expect mulr_sumr; apply/eq_big => [//|x _].
by rewrite mulrA.
Qed.

Lemma mulr_expectl r p F : ('E_(x <- p) F x) * r = 'E_(x <- p) F x * r.
Proof.
rewrite /expect mulr_suml; apply/eq_big => [//|x _].
by rewrite mulrAC.
Qed.

Lemma addr_expect p F1 F2 :
  ('E_(x <- p) F1 x + 'E_(x <- p) F2 x)%R =
  'E_(x <- p) (F1 x + F2 x)%R.
Proof.
rewrite /expect -big_split; apply/eq_big => // x _.
by rewrite mulrDl.
Qed.

Lemma eq_expect_gen p1 p2 F1 F2 :
  (forall x, F1 x * p1 x = F2 x * p2 x) ->
  expect p1 F1 = expect p2 F2.
Proof.
move=> e12.
rewrite (expectE _ (fsubsetUl (finsupp p1) (finsupp p2))).
rewrite (expectE _ (fsubsetUr (finsupp p1) (finsupp p2))).
exact/eq_big.
Qed.

Lemma eq_expect_in p F1 F2 :
  {in finsupp p, F1 =1 F2} ->
  expect p F1 = expect p F2.
Proof.
move=> e12; apply/eq_expect_gen => x.
by case: (finsuppP p x) => [x_nin|x_in]; rewrite ?mulr0 // e12.
Qed.

Lemma eq_expect p F1 F2 : F1 =1 F2 -> expect p F1 = expect p F2.
Proof.
move=> e12; apply: eq_expect_in => ??; exact: e12.
Qed.

Lemma expect_const c p F :
  (forall x, x \in finsupp p -> F x = c) ->
  'E_(x <- p) F x = c.
Proof.
move=> Fc.
rewrite -[c]mul1r -(eqP (valP p)) /mass /= mulr_suml.
rewrite [LHS]big_seq [RHS]big_seq; apply/eq_big => // x /Fc ->.
by rewrite mulrC.
Qed.

Lemma sumr_expect I s (P : I -> bool) p (F : I -> T -> rat) :
  \sum_(i <- s | P i) 'E_(x <- p) F i x =
  'E_(x <- p) \sum_(i <- s | P i) F i x.
Proof.
elim: s => [|i s IH].
  by rewrite big_nil (@expect_const 0) // => ? _; rewrite big_nil.
under [in RHS]eq_expect => x do rewrite big_cons.
rewrite big_cons IH; case: (P i) => //.
by rewrite addr_expect.
Qed.

Lemma expect_ge0 p F :
  (forall x, x \in finsupp p -> 0 <= F x) ->
  0 <= expect p F.
Proof.
move=> F_ge0; apply: Num.Theory.sumr_ge0 => x _.
case: (finsuppP p x) => [_|x_in]; rewrite ?mulr0 //.
by rewrite Num.Theory.mulr_ge0 // ?F_ge0 // distr_ge0.
Qed.

End Expectation.

Notation "''E_' ( x <- p ) F" := (expect p (fun x => F))
  (at level 41, F at level 41, x, p at level 50,
    format "'[' ''E_' ( x  <-  p )  '/  ' F ']'")
  : prob_scope.

Arguments expect_const {T} c.

Lemma expectC (T S : choiceType) p q (F : T -> S -> rat) :
  'E_(x <- p) 'E_(y <- q) F x y =
  'E_(y <- q) 'E_(x <- p) F x y.
Proof.
rewrite /expect.
under [LHS]eq_big => [//|x _] do rewrite GRing.mulr_suml.
under [RHS]eq_big => [//|x _] do rewrite GRing.mulr_suml.
rewrite exchange_big /=; apply/eq_big => // x _.
by under eq_big => [//|y _] do rewrite GRing.mulrAC.
Qed.

Section Sample.

Variables T S : choiceType.
Variable (f : T -> {prob S}) (p : {prob T}).
Implicit Types (x : T) (y : S).

Let Y   : {fset S} := \bigcup_(x <- finsupp p) finsupp (f x).
Let P y : rat      := 'E_(x <- p) f x y.

Lemma sample_subproof1 y : y \in Y -> 0 <= P y.
Proof.
move=> _; apply: Num.Theory.sumr_ge0 => x _.
apply: Num.Theory.mulr_ge0; exact: distr_ge0.
Qed.

Lemma sample_subproof2 : \sum_(y <- Y) P y = 1.
Proof.
rewrite /P sumr_expect (expect_const 1) // => x x_in.
rewrite -(eqP (valP (f x))); apply/esym/massE.
apply/fsubsetP=> y; rewrite mem_finsupp => yP.
by apply/bigfcupP; exists x; rewrite ?x_in // mem_finsupp.
Qed.

Definition sample :=
  mkprob sample_subproof1 sample_subproof2.

Lemma sample_defE0 y : (y \in Y) = (P y != 0).
Proof.
rewrite /P Num.Theory.psumr_eq0 -?has_predC /=; last first.
  move=> x _; apply: Num.Theory.mulr_ge0; exact: distr_ge0.
apply/(sameP bigfcupP)/(iffP hasP).
- case=> /= x x_p n0; exists x; rewrite ?x_p //.
  by move: n0; rewrite GRing.mulf_eq0 negb_or mem_finsupp; case/andP.
- case=> /= x; rewrite andbT !mem_finsupp => x_p y_f.
  by exists x; rewrite 1?mem_finsupp // GRing.mulf_neq0.
Qed.

Lemma sampleE y : sample y = P y.
Proof.
rewrite /sample mkprobE sample_defE0.
by case: (P y =P 0)=> [->|].
Qed.

Lemma finsupp_sample : finsupp sample = Y.
Proof.
apply/fsetP=> x; by rewrite mem_finsupp sample_defE0 sampleE.
Qed.

Lemma finsupp_sampleP y :
  reflect (exists2 x, x \in finsupp p & y \in finsupp (f x)) (y \in finsupp sample).
Proof.
rewrite finsupp_sample; apply/(iffP bigfcupP).
- case=> ?; rewrite andbT; eauto.
- by case=> ???; eexists; rewrite ?andbT //; eauto.
Qed.

End Sample.

Arguments sample {T S}.
Arguments finsupp_sampleP {_ _ _ _ _}.

(** A more convenient notation for sampling. *)

Notation "'sample:' x '<-' t1 ';' t2" :=
  (sample (fun x => t2) t1)
  (at level 20, x binder, t1 at level 100, t2 at level 200,
   right associativity, format "'[' 'sample:'  x  '<-'  '[' t1 ;  ']' ']' '/' t2")
  : prob_scope.

Section SampleProperties.

Variables T S : choiceType.

Import GRing.

Lemma sample_diracL (x : T) (f : T -> {prob S}) : sample f (dirac x) = f x.
Proof.
by apply/eq_prob=> y; rewrite sampleE expect_dirac.
Qed.

Lemma sample_diracR (p : {prob T}) : sample dirac p = p.
Proof.
apply/eq_prob=> x; rewrite sampleE.
under eq_expect do rewrite diracE.
case: (finsuppP p x) => [x_nin|x_in].
  apply/(expect_const 0) => y y_in.
  by case: eqP y_in x_nin => [->|//] ->.
rewrite /expect (big_rem _ x_in) /= eqxx mul1r big_seq big1 ?addr0 // => y.
rewrite mem_rem_uniq ?uniq_fset //= eq_sym.
by case/andP => /negbTE ->; rewrite mul0r.
Qed.

Lemma eq_sample (p : {prob T}) (f g : T -> {prob S}) :
  f =1 g -> sample f p = sample g p.
Proof.
move=> efg; apply/eq_prob=> y.
by rewrite !sampleE; apply/eq_big=> // x _; rewrite efg.
Qed.

Lemma eq_in_sample (p : {prob T}) (f g : T -> {prob S}) :
  {in finsupp p, f =1 g} -> sample f p = sample g p.
Proof.
move=> efg; apply/eq_prob=> y.
by rewrite !sampleE; apply/eq_expect_in => // x /efg ->.
Qed.

Lemma sample_const (px : {prob T}) (py : {prob S}) :
  (sample: _ <- px; py) = py.
Proof.
by apply/eq_prob=> y; rewrite sampleE (expect_const (py y)).
Qed.

Lemma sample_const' (px : {prob T}) (f : T -> {prob S}) (py : {prob S}) :
  (forall x, x \in finsupp px -> f x = py) ->
  (sample: x <- px; f x) = py.
Proof.
move=> fE; under eq_in_sample => x x_in do rewrite fE //.
by rewrite sample_const.
Qed.

Lemma eq_sample_dirac (p : {prob T}) (f : T -> {prob S}) y :
  sample f p = dirac y ->
  forall x, x \in finsupp p -> f x = dirac y.
Proof.
move=> e x x_p.
have {}e: finsupp (sample f p) = finsupp (dirac y) by rewrite e.
rewrite finsupp_sample finsupp_dirac in e.
apply/eqP; rewrite -eq_finsupp_dirac eqEfsubset; apply/andP; split.
  rewrite -e; exact/bigfcup_sup.
rewrite fsub1set; have /fset0Pn [z zP] := finsuppPrN0 (f x).
suff: z \in fset1 y by move=> /fset1P => <-.
by rewrite -e; apply/bigfcupP; exists x; rewrite ?andbT.
Qed.

End SampleProperties.

Lemma expect_sample (T S : choiceType) p (f : T -> {prob S}) (G : S -> rat) :
  'E_(y <- sample f p) G y =
  'E_(x <- p) 'E_(y <- f x) G y.
Proof.
rewrite /expect.
under [LHS]eq_big => [//|x _] do rewrite sampleE mulr_expectr.
rewrite exchange_big /= [LHS]big_seq [RHS]big_seq.
apply/eq_big => // x x_in; rewrite GRing.mulr_suml.
have /fsetIidPl <-: fsubset (finsupp (f x)) (finsupp (sample: x <- p; f x)).
  apply/fsubsetP=> y fxy; rewrite finsupp_sample.
  by apply/bigfcupP; exists x; rewrite ?andbT.
apply/esym/big_fset_incl; rewrite ?fsubsetIr // => y.
rewrite in_fsetI negb_and => ->; case: finsuppP => // _ _.
by rewrite GRing.mulr0 GRing.mul0r.
Qed.

Lemma sampleA (T S R : choiceType) p (f : T -> {prob S}) (g : S -> {prob R}) :
  (sample: y <- (sample: x <- p; f x); g y) =
  (sample: x <- p; sample: y <- f x; g y).
Proof.
apply/eq_prob=> z; rewrite !sampleE expect_sample.
by under [RHS]eq_expect => ? do rewrite sampleE.
Qed.

Lemma sampleC (T S R : choiceType) (p1 : {prob T}) (p2 : {prob S}) (f : T -> S -> {prob R}) :
  (sample: x <- p1; sample: y <- p2; f x y) =
  (sample: y <- p2; sample: x <- p1; f x y).
Proof.
apply/eq_prob=> z; rewrite !sampleE.
under [LHS]eq_expect do rewrite sampleE.
under [RHS]eq_expect do rewrite sampleE.
by rewrite expectC.
Qed.

Section Uniform.

Variable T : choiceType.
Variable X : {fset T}.
Hypothesis Xn0 : X != fset0.

Definition unif_def (x : T) : rat := (size X)%:R^-1.

Lemma unif_subproof1 x : x \in X -> 0 <= unif_def x.
Proof.
move=> _; by rewrite Num.Theory.invr_ge0 Num.Theory.ler0n.
Qed.

Lemma unif_subproof2 : \sum_(x <- X) unif_def x = 1.
Proof.
rewrite big_const_seq count_predT -Monoid.Theory.iteropE.
rewrite -[RHS](@GRing.mulfV _ (size X)%:R) ?GRing.mulr_natl //.
by rewrite Num.Theory.pnatr_eq0 cardfs_eq0.
Qed.

Definition unif := mkprob unif_subproof1 unif_subproof2.

Lemma unifE x : unif x = if x \in X then (size X)%:R^-1 else 0.
Proof. by rewrite mkprobE. Qed.

Lemma finsupp_unif : finsupp unif = X.
Proof.
apply/fsetP => x; rewrite mem_finsupp unifE.
by case: ifP => // _; rewrite GRing.invr_eq0 Num.Theory.pnatr_eq0 cardfs_eq0.
Qed.

End Uniform.

(** To simplify the reasoning about our optimizations, we use probabilistic
couplings.  A coupling is a way of lifting a relation between two sets to a
relation over distributions over these sets.  (NB: We define this relation in
[Type] to avoid issues with the axiom of choice when proving [coupling_sample]
below.)  The definition is useful because (1) it has good composition
properties, as seen by [coupling_dirac] and [coupling_sample], and because (2)
it is strong enough to establish the equality of two distributions, as seen in
[coupling_same]. *)

Variant coupling (T S : choiceType) (R : T -> S -> Prop) pT pS : Type :=
| Coupling p of
  pT = sample (dirac \o fst) p &
  pS = sample (dirac \o snd) p &
  (forall xy, xy \in finsupp p -> R xy.1 xy.2).

Lemma coupling_dirac (T S : choiceType) (R : T -> S -> Prop) x y :
  R x y -> coupling R (dirac x) (dirac y).
Proof.
move=> xy; exists (dirac (x, y)); rewrite ?sample_diracL //.
by move=> [??] /finsupp_diracP [-> ->].
Qed.

Lemma coupling_sample (T1 S1 T2 S2 : choiceType) (R1 : T1 -> S1 -> Prop) (R2 : T2 -> S2 -> Prop) pT pS f g :
  coupling R1 pT pS ->
  (forall x y, x \in finsupp pT -> y \in finsupp pS -> R1 x y ->
    coupling R2 (f x) (g y)) ->
  coupling R2 (sample f pT) (sample g pS).
Proof.
case=> /= p eT eS R1P R12.
pose def xy := sample: x' <- f xy.1; sample: y' <- g xy.2; dirac (x', y').
have WT xy : xy \in finsupp p -> xy.1 \in finsupp pT.
  move=> xyp; rewrite eT; apply/finsupp_sampleP.
  exists xy=> //=; exact/finsupp_diracP.
have WS xy : xy \in finsupp p -> xy.2 \in finsupp pS.
  move=> xyp; rewrite eS; apply/finsupp_sampleP.
  exists xy=> //=; exact/finsupp_diracP.
pose draw xy := if insub xy is Some xy then
                  let xyP := svalP xy in
                  let xP := WT _ xyP in
                  let yP := WS _ xyP in
                  let: Coupling p _ _ _ := R12 _ _ xP yP (R1P _ xyP) in p
                else def xy.
exists (sample draw p).
- rewrite eT !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
  by rewrite sample_diracL insubT /=; case: (R12 _ _ _ _ _).
- rewrite eS !sampleA; apply/eq_in_sample; case=> [x y] /= xy_supp.
  by rewrite sample_diracL insubT /=; by case: (R12 _ _ _ _ _).
case=> x' y' /finsupp_sampleP [] [x y] xy_supp.
rewrite /draw insubT /=.
case: (R12 _ _ _ _ _)=> /= pxy eT' eS' R2P; exact: R2P.
Qed.

Lemma coupling_same (T : choiceType) (p : {prob T}) : coupling eq p p.
Proof.
pose pp := sample: x <- p; dirac (x, x); exists pp; rewrite ?sampleA.
- under eq_sample do rewrite sample_diracL /=.
  by rewrite sample_diracR.
- under eq_sample do rewrite sample_diracL /=.
  by rewrite sample_diracR.
by move=> xx /finsupp_sampleP [] x x_p /finsupp_diracP ->.
Qed.

Lemma coupling_eq (T : choiceType) (p q : {prob T}) : coupling eq p q -> p = q.
Proof.
by case=> pq -> -> {p q} e; apply/eq_in_sample; case=> x y /e /= ->.
Qed.

Lemma coupling_sample_same (T S1 S2 : choiceType) (R : S1 -> S2 -> Prop) (p : {prob T}) f g :
  (forall x, x \in finsupp p -> coupling R (f x) (g x)) ->
  coupling R (sample f p) (sample g p).
Proof.
move=> e; apply: coupling_sample; first exact: coupling_same.
move=> x _ x_p _ <-; exact: e.
Qed.

Lemma coupling_trivial (T S : choiceType) (R : T -> S -> Prop) (pT : {prob T}) (pS : {prob S}) :
  (forall x y, x \in finsupp pT -> y \in finsupp pS -> R x y) ->
  @coupling T S R pT pS.
Proof.
move=> RP.
exists (sample: x <- pT; sample: y <- pS; dirac (x, y)).
- rewrite sampleA; under eq_sample => x.
    rewrite sampleA; under eq_sample do rewrite sample_diracL.
    rewrite /= sample_const; over.
  by rewrite sample_diracR.
- rewrite sampleA; under eq_sample=> x.
    rewrite sampleA; under eq_sample do rewrite sample_diracL.
    rewrite /= sample_diracR; over.
  by rewrite sample_const.
case=> x y /finsupp_sampleP [] x' xP /finsupp_sampleP [] y' yP /=.
move=> /finsupp_diracP [-> ->]; exact: RP.
Qed.

Lemma couplingT T S pT pS : @coupling T S (fun _ _ => True) pT pS.
Proof. by apply: coupling_trivial. Qed.

Lemma coupling_sampleL (T S1 S2 : choiceType) (R : S1 -> S2 -> Prop) (pT : {prob T}) f pS :
  (forall x, x \in finsupp pT -> coupling R (f x) pS) ->
  coupling R (sample: x <- pT; f x) pS.
Proof.
move=> RP; rewrite -[pS](sample_const pS).
apply: coupling_sample (couplingT _ _) _ => x _ xP _ _.
exact: RP.
Qed.

Lemma coupling_sampleR (T S1 S2 : choiceType) (R : S1 -> S2 -> Prop) (pT : {prob T}) f pS :
  (forall x, x \in finsupp pT -> coupling R pS (f x)) ->
  coupling R pS (sample: x <- pT; f x).
Proof.
move=> RP; rewrite -[pS](sample_const pS).
apply: coupling_sample (couplingT _ _) _ => _ x _ xP _.
exact: RP.
Qed.

Lemma couplingW (T S : choiceType) (R1 R2 : T -> S -> Prop) pT pS :
  (forall x y, R1 x y -> R2 x y) ->
  @coupling T S R1 pT pS ->
  coupling R2 pT pS.
Proof. by move=> R12 [p eT eS R1P]; exists p; eauto. Qed.

Lemma in_couplingW (T S : choiceType) (R1 R2 : T -> S -> Prop) (pT : {prob T}) (pS : {prob S}) :
  (forall x y, x \in finsupp pT -> y \in finsupp pS -> R1 x y -> R2 x y) ->
  coupling R1 pT pS ->
  coupling R2 pT pS.
Proof.
move=> R12 [p eT eS R1P]; exists p; eauto.
case=> x y xyP; apply: R12; last exact: R1P.
- rewrite eT; apply/finsupp_sampleP.
  by exists (x, y)=> //; rewrite // finsupp_dirac in_fset1.
- rewrite eS; apply/finsupp_sampleP.
  by exists (x, y)=> //; rewrite // finsupp_dirac in_fset1.
Qed.

(** The following definitions allow us to apply probabilistic computations to
the elements of sequences, maps and other container types.  They will be used to
define the semantics of Imp programs. *)

Section FoldingM.

Variables (T : Type) (S : choiceType).
Implicit Types (f : T -> S -> {prob S}) (x : T) (y : S) (xs : seq T).

Definition foldrM f py0 xs : {prob S} :=
  foldr (sample \o f) py0 xs.

Lemma eq_foldrM f g py0 xs :
  f =2 g ->
  foldrM f py0 xs = foldrM g py0 xs.
Proof.
by move=> fg; elim: xs=> //= x xs ->; under eq_sample => ? do rewrite fg.
Qed.

Lemma foldrM_dirac g y0 xs :
  foldrM (fun x y' => dirac (g x y')) (dirac y0) xs = dirac (foldr g y0 xs).
Proof.
by elim: xs => //= x xs ->; rewrite sample_diracL.
Qed.

Lemma foldrM_cat f py0 xs1 xs2 :
  foldrM f py0 (xs1 ++ xs2) = foldrM f (foldrM f py0 xs2) xs1.
Proof.
by elim: xs1 => /= [|x xs1 IH]; rewrite ?sample_diracR // IH.
Qed.

Lemma foldrM_sample f py0 xs :
  foldrM f py0 xs = sample: y <- py0; foldrM f (dirac y) xs.
Proof.
elim: xs => /= [|x xs IH]; rewrite ?sample_diracR //.
by rewrite IH sampleA.
Qed.

Definition commutative_actp f :=
  forall x1 x2 y, sample (f x1) (f x2 y) = sample (f x2) (f x1 y).

Lemma commutative_actpP f :
  commutative_actp f -> commutative_act (sample \o f).
Proof.
move=> fC x1 x2 py /=; rewrite !sampleA; apply/eq_sample => ?.
by rewrite fC.
Qed.

Lemma foldrMC f py0 xs1 xs2 :
  commutative_actp f ->
  foldrM f py0 (xs1 ++ xs2) = foldrM f py0 (xs2 ++ xs1).
Proof. move=> /commutative_actpP fC; exact: foldrC. Qed.

Definition idempotent_actp f :=
  forall x y, sample (f x) (f x y) = f x y.

Lemma idempotent_actpP f :
  idempotent_actp f -> idempotent_act (sample \o f).
Proof.
move=> fI x py /=; rewrite !sampleA; apply/eq_sample => ?.
by rewrite fI.
Qed.

End FoldingM.

Section FoldingMEq.

Variables (T : eqType) (S : choiceType).
Implicit Types (f : T -> S -> {prob S}) (x : T) (y : S) (xs : seq T).

Lemma foldrM_perm_eq f py0 xs1 xs2 :
  commutative_actp f ->
  perm_eq xs1 xs2 ->
  foldrM f py0 xs1 = foldrM f py0 xs2.
Proof. move=> /commutative_actpP; exact: foldr_perm_eq. Qed.

Lemma foldrM_idem f py0 x s :
  commutative_actp f ->
  idempotent_actp f ->
  x \in s ->
  sample (f x) (foldrM f py0 s) = foldrM f py0 s.
Proof.
move=> /commutative_actpP ? /idempotent_actpP ?; exact: foldr_idem.
Qed.

Lemma foldrM_mem_eq f py0 xs1 xs2 :
  commutative_actp f ->
  idempotent_actp f ->
  xs1 =i xs2 ->
  foldrM f py0 xs1 = foldrM f py0 xs2.
Proof.
move=> /commutative_actpP fC /idempotent_actpP fI.
exact: foldr_mem_eq.
Qed.

End FoldingMEq.

Section FoldingMSet.

Variables (T S : choiceType).
Implicit Types (f : T -> S -> {prob S}) (x : T) (y : S) (xs : seq T).
Implicit Types (X : {fset T}).

Lemma foldrM_fsetU_idem f py0 X1 X2 :
  commutative_actp f ->
  idempotent_actp f ->
  foldrM f py0 (X1 `|` X2) = foldrM f (foldrM f py0 X2) X1.
Proof.
move=> /commutative_actpP fC /idempotent_actpP fI.
exact: foldr_fsetU_idem.
Qed.

Lemma foldrM_fset1U_idem f py0 x X :
  commutative_actp f ->
  idempotent_actp f ->
  foldrM f py0 (x |` X) = sample (f x) (foldrM f py0 X).
Proof.
move=> /commutative_actpP fC /idempotent_actpP fI.
exact: foldr_fset1U_idem.
Qed.

End FoldingMSet.

Section FoldMMap.

Variables (T1 T2 : Type) (S : choiceType).
Implicit Types (h : T1 -> T2) (f : T2 -> S -> {prob S}) (xs : seq T1).

Lemma foldrM_map h f z0 s :
  foldrM f z0 [seq h i | i <- s] =
  foldrM (fun x z => f (h x) z) z0 s.
Proof. exact: foldr_map. Qed.

End FoldMMap.

Fixpoint map_p T
  (S : choiceType) (f : T -> {prob S}) (xs : seq T) : {prob seq S} :=
  match xs with
  | [::] => dirac [::]
  | x :: xs =>
    sample: y  <- f x;
    sample: ys <- map_p f xs;
    dirac (y :: ys)
  end.

Lemma eq_map_p T (S : choiceType) (f g : T -> {prob S}) :
  f =1 g -> map_p f =1 map_p g.
Proof. by move=> fg; elim=> //= x xs IH; rewrite fg IH. Qed.

Lemma map_p_dirac (T : choiceType) (xs : seq T) : map_p dirac xs = dirac xs.
Proof.
elim: xs=> //= x xs IH.
by rewrite sample_diracL IH sample_diracL.
Qed.

Lemma map_p_comp T S (R : choiceType) (f : T -> S) (g : S -> {prob R}) xs :
  map_p g [seq f x | x <- xs] = map_p (g \o f) xs.
Proof. by elim: xs=> //= x xs ->. Qed.

Lemma map_p_sample
  (T S R : choiceType) (g : S -> {prob R}) (f : T -> {prob S}) (xs : seq T) :
  map_p (fun x => sample: y <- f x; g y) xs =
  sample: ys <- map_p f xs; map_p g ys.
Proof.
elim: xs=> [|x xs IH] /=; first by rewrite sample_diracL.
rewrite !sampleA; apply/eq_sample=> y.
rewrite sampleA {}IH.
under eq_sample=> z do rewrite sampleA.
under [in RHS]eq_sample=> zs do rewrite sample_diracL /=.
by rewrite sampleC.
Qed.

Lemma finsupp_map_p T (S : choiceType) (f : T -> {prob S}) xs ys :
  ys \in finsupp (map_p f xs) =
  all2 (fun x y => y \in finsupp (f x)) xs ys.
Proof.
elim: xs ys=> [|x xs IH] [|y ys] /=.
- by rewrite finsupp_dirac in_fset1.
- by rewrite finsupp_dirac in_fset1.
- case: finsupp_sampleP=> //=.
  by case=> y' y'P /finsupp_sampleP [ys' _ /finsupp_diracP].
- rewrite -IH; apply/(sameP finsupp_sampleP)/(iffP andP).
  + case=> [yP ysP]; exists y=> //.
    apply/finsupp_sampleP; exists ys=> //.
    by apply/finsupp_diracP.
  + by case=> [y' y'P /finsupp_sampleP [ys' ys'P /finsupp_diracP [-> ->]]].
Qed.

Section MapMapImProb.

Variable (T : choiceType) (S : Type) (R : choiceType).
Implicit Types (f g : T -> S -> {prob R}) (m : {fmap T -> S}) (rm : {fmap T -> R}).

Definition mapim_p f m : {prob {fmap T -> R}} :=
  let do_pair p := sample: y <- f p.1 p.2; dirac (p.1, y) in
  sample: pairs <- map_p do_pair (graphf m);
  dirac (mkfmap pairs).

Lemma mapim_pE f m :
  mapim_p f m =
  foldrM (fun p rm => sample: z <- f p.1 p.2; dirac rm.[p.1 <- z])
    (dirac [fmap]) (graphf m).
Proof.
rewrite /mapim_p /=.
elim: (graphf m)=> {m} [|[x y] m /= IH] //=.
- by rewrite sample_diracL //.
- rewrite !sampleA [in RHS]sampleC; apply/eq_sample=> z.
  rewrite sample_diracL sampleA -IH sampleA.
  by apply/eq_sample=> pairs; rewrite !sample_diracL.
Qed.

Lemma eq_mapim_p f g : f =2 g -> mapim_p f =1 mapim_p g.
Proof.
move=> fg m; rewrite /mapim_p.
by under eq_map_p => p do rewrite fg.
Qed.

Lemma mapim_p0 f : mapim_p f [fmap] = dirac [fmap].
Proof. by rewrite mapim_pE graphf0. Qed.

Lemma mapim_p_set f m x y :
  mapim_p f m.[x <- y] =
  sample: z <- f x y;
  sample: rm <- mapim_p f m;
  dirac rm.[x <- z].
Proof.
rewrite !mapim_pE /foldrM foldr_set /= 1?sampleC //.
- move=> /= {x y} x1 x2 y1 y2 pm x1x2.
  rewrite !sampleA; apply/eq_sample=> /= rm.
  rewrite !sampleA; under eq_sample do rewrite sample_diracL.
  rewrite sampleC; apply/eq_sample => /= z; rewrite sample_diracL.
  by apply/eq_sample => /= z'; rewrite setfC // (negbTE x1x2).
- move=> /= {}x y1 y2 pm; rewrite sampleA; apply/eq_sample => /= rm.
  rewrite sampleA; under eq_sample => z.
    rewrite sample_diracL; under eq_sample do rewrite setfC eqxx; over.
  by rewrite sample_const.
Qed.

Lemma domf_mapim_p f m rm : rm \in finsupp (mapim_p f m) -> domf rm = domf m.
Proof.
elim/fmap_rect: m => [|m IH x y x_m] /= in rm *.
  by rewrite mapim_p0 finsupp_dirac inE => /eqP ->.
rewrite mapim_p_set; case/finsupp_sampleP=> z z_xy.
case/finsupp_sampleP=> rm' /IH <-; rewrite finsupp_dirac => /fset1P ->.
by rewrite dom_setf.
Qed.

End MapMapImProb.

Lemma mapim_p_dirac (T S : choiceType) (m : {fmap T -> S}) :
  mapim_p (fun _ => dirac) m = dirac m.
Proof.
rewrite /mapim_p.
under eq_map_p => p do rewrite sample_diracL -surjective_pairing.
by rewrite map_p_dirac sample_diracL graphfK.
Qed.

Lemma mapim_p_comp (T S R U : choiceType)
  (g : T -> R -> {prob U}) (f : T -> S -> R) m :
  mapim_p g [fmap x : domf m => f (val x) (m x)] =
  mapim_p (fun x y => g x (f x y)) m.
Proof. by rewrite /mapim_p graphf_map map_p_comp. Qed.

Section MapMapProb.

Variable (T : choiceType) (S : Type) (R : choiceType).
Implicit Types (f g : S -> {prob R}) (m : {fmap T -> S}) (rm : {fmap T -> R}).

Fact mapm_p_key : unit. Proof. exact: tt. Qed.

Definition mapm_p f :=
  locked_with mapm_p_key (mapim_p (fun (x : T) => f)).

Lemma eq_mapm_p f g : f =1 g -> mapm_p f =1 mapm_p g.
Proof.
rewrite /mapm_p !unlock.
by move=> e; apply/eq_mapim_p=> ??; eauto.
Qed.

Lemma mapm_p0 f : mapm_p f [fmap] = dirac [fmap].
Proof. by rewrite /mapm_p [in LHS]unlock mapim_p0. Qed.

Lemma mapm_p_set f m x y :
  mapm_p f m.[x <- y] =
  sample: z <- f y;
  sample: rm <- mapm_p f m;
  dirac rm.[x <- z].
Proof. by rewrite /mapm_p !unlock mapim_p_set. Qed.

Lemma domf_mapm_p f m rm : rm \in finsupp (mapm_p f m) -> domf rm = domf m.
Proof. rewrite /mapm_p [locked_with _ _]unlock; exact: domf_mapim_p. Qed.

Lemma finsupp_mapm_p f m rm :
  rm \in finsupp (mapm_p f m) =
  (domf m == domf rm) &&
  all (fun x => match m.[? x], rm.[? x] with
                | Some y, Some z => z \in finsupp (f y)
                | _, _ => true
                end) (domf m).
Proof.
elim/fmap_rect: m => [|m IH x y x_m] in rm *.
  rewrite /= mapm_p0 finsupp_dirac inE andbT.
  by apply/(sameP eqP)/(iffP eqP)=> [/esym/fmap_nil ->|->].
rewrite [X in X == _]dom_setf [in X in all _ X]dom_setf all_fset1U mapm_p_set.
have [x_rm|x_rm] := fndP rm x; last first.
  have /negbTE -> /= : x |` domf m != domf rm.
    by apply: contraNN x_rm => /eqP <-; rewrite fset1U1.
  apply/negbTE/finsupp_sampleP; case => z z_y.
  case/finsupp_sampleP => /= rm'.
  rewrite finsupp_dirac => /domf_mapm_p domf_rm' /fset1P erm.
  by rewrite erm dom_setf fset1U1 in x_rm.
have -> : (x |` domf m == domf rm) = (domf m == domf rm.[~ x]).
  rewrite domf_rem; apply/(sameP eqP)/(iffP eqP) => [->|<-].
  - exact: fsetD1K.
  - by rewrite fsetU1K.
rewrite fnd_set eqxx; under eq_in_all => x' x'_m.
  have xx': x' != x by apply: contraNN x_m => /eqP <-.
  have ->: rm.[? x'] = rm.[~ x].[? x'] by rewrite fnd_rem1 xx'.
  rewrite fnd_set (negbTE xx'); over.
rewrite andbCA -(IH rm.[~ x]).
apply/(sameP finsupp_sampleP)/(iffP andP).
- case=> z_y rm'_m; exists rm.[x_rm] => //.
  apply/finsupp_sampleP; exists rm.[~ x] => //.
  by rewrite finsupp_dirac in_fset1 setf_rem1 -[X in X == _](setf_get [`x_rm]).
- case=> z z_y /finsupp_sampleP [rm' rm'_m].
  rewrite finsupp_dirac=> /fset1P erm.
  have ->: rm.[x_rm] = z.
    by apply/Some_inj; rewrite -in_fnd erm fnd_set eqxx.
  split; rewrite // erm remf1_set eqxx remf1_id //.
  by move/domf_mapm_p: rm'_m x_m => <-.
Qed.

Lemma finsupp_mapm_pP f m rm :
  reflect (domf m = domf rm /\
           forall x y z, m.[? x] = Some y -> rm.[? x] = Some z ->
                         z \in finsupp (f y))
          (rm \in finsupp (mapm_p f m)).
Proof.
rewrite finsupp_mapm_p; apply/(iffP andP).
- case=> /eqP edomm ecodomm; split=> // x y z yP zP.
  have xP: x \in m by rewrite -fndSome yP.
  by move/allP/(_ _ xP): ecodomm; rewrite yP zP.
- case=> edomm ecodomm; split; first by rewrite edomm.
  apply/allP=> x x_m; case: fndP x_m=> // x_m _.
  set y := m.[x_m].
  move: (x_m); rewrite edomm; case: fndP => // x_rm _.
  apply: ecodomm; by rewrite -in_fnd.
Qed.

End MapMapProb.

Lemma mapm_p_dirac (T S : choiceType) (m : {fmap T -> S}) :
  mapm_p dirac m = dirac m.
Proof. rewrite /mapm_p !unlock; exact/mapim_p_dirac. Qed.

Lemma mapm_p_comp (T S R U : choiceType)
  (g : R -> {prob U}) (f : S -> R) (m : {fmap T -> S}) :
  mapm_p g [fmap x : domf m => f (m x)] = mapm_p (g \o f) m.
Proof.
rewrite /mapm_p [in LHS]unlock [in RHS]unlock; exact/mapim_p_comp.
Qed.

Lemma mapm_p_sample
  (T S R U : choiceType) (g : R -> {prob U}) (f : S -> {prob R}) (m : {fmap T -> S}) :
  mapm_p (fun x => sample: y <- f x; g y) m =
  sample: m' <- mapm_p f m; mapm_p g m'.
Proof.
elim/fmap_rect: m=> [|m IH x y x_m]; first by rewrite !(mapm_p0, sample_diracL).
rewrite !mapm_p_set IH // !sampleA; apply/eq_sample=> m'.
rewrite sampleA; under [in LHS]eq_sample=> ? do rewrite sampleA.
rewrite sampleC; apply/eq_sample=> z.
by rewrite sample_diracL mapm_p_set sampleC.
Qed.

Lemma coupling_mapm_p (T S11 S12 S21 S22 : choiceType)
    (R1 : T -> S11 -> S12 -> Prop) (R2 : T -> S21 -> S22 -> Prop)
    (f1 : S11 -> {prob S21}) (f2 : S12 -> {prob S22}) :
  (forall x y1 y2, R1 x y1 y2 -> coupling (R2 x) (f1 y1) (f2 y2)) ->
  forall (m1 : {fmap _}) (m2 : {fmap _}),
    (forall x y1 y2, m1.[? x] = Some y1 -> m2.[? x] = Some y2 -> R1 x y1 y2) ->
    coupling (fun (m1' : {fmap _}) (m2' : {fmap _}) =>
                forall x y1 y2, m1'.[? x] = Some y1 -> m2'.[? x] = Some y2 -> R2 x y1 y2)
             (mapm_p f1 m1) (mapm_p f2 m2).
Proof.
move=> RP; elim/fmap_rect.
  rewrite mapm_p0; move=> m2 em; apply: coupling_trivial.
  by move=> _ m2' /finsupp_diracP -> _ ???; rewrite not_fnd.
move=> m1 IH x y1 fresh m2 em.
have y1P y2 : m2.[? x] = Some y2 -> R1 x y1 y2.
  by apply: em; rewrite fnd_set eqxx.
have /IH {}em x' y1' y2 : m1.[? x'] = Some y1' -> m2.[? x'] = Some y2 -> R1 x' y1' y2.
  move=> m1x' m2x'; apply: em; rewrite // fnd_set.
  by case: eqP m1x'=> // ->; case: fndP fresh.
rewrite mapm_p_set sampleC; have [x_m2|x_m2] := fndP m2 x.
  rewrite -[m2](setf_get [`x_m2]) /= mapm_p_set (sampleC (f2 _)).
  apply: coupling_sample em _.
  move=> /= m1' m2' _ _ em'; apply: coupling_sample.
    by apply: RP; apply: y1P; rewrite in_fnd.
  move=> y1' y2' _ _ yP; apply: coupling_dirac.
  move=> x' y1'' y2''; rewrite !fnd_set; case: eqP=> [->|_].
    by move=> [<-] [<-].
  exact: em'.
rewrite -[mapm_p _ m2]sample_diracR.
apply: coupling_sample em _ => m1' m2' _ /finsupp_mapm_pP [ed2 _].
move=> {}em; apply: coupling_sampleL=> y1' _; apply: coupling_dirac.
move=> x' y1'' y2''; rewrite fnd_set; case: eqP=> [->|_]; last exact: em.
by case: fndP => // x_m2' _ _; rewrite ed2 x_m2' in x_m2.
Qed.

Lemma coupling_mapm_p_eq (T S1 S2 : choiceType) (f : S1 -> {prob S2}) (m1 m2 : {fmap T -> S1}) (P : T -> bool) :
  {in P, fnd m1 =1 fnd m2} ->
  coupling (fun m1' m2' : {fmap T -> S2} => {in P, fnd m1' =1 fnd m2'})
    (mapm_p f m1) (mapm_p f m2).
Proof.
move=> em.
pose R1 x (y1 y2 : S1) := P x -> y1 = y2.
pose R2 x (y1' y2' : S2) := P x -> y1' = y2'.
have emW x y1 y2 : m1.[? x] = Some y1 -> m2.[? x] = Some y2 -> R1 x y1 y2.
  move=> m1x m2x Px; apply: Some_inj; rewrite -m1x -m2x; exact: em.
have RP x y1 y2 : R1 x y1 y2 -> coupling (R2 x) (f y1) (f y2).
  move=> xP; case: (boolP (P x))=> [{}/xP ->|nPx].
    apply: couplingW; last exact: coupling_same.
    by move=> ?? ->.
  apply: coupling_trivial=> ?? _ _ contra; by rewrite contra in nPx.
apply: in_couplingW; last by apply: coupling_mapm_p emW; eauto.
move=> /= m1' m2' /finsupp_mapm_pP [ed1 _] /finsupp_mapm_pP [ed2 _].
move=> em' x Px; move: (em' x) (em _ Px).
have [[x_m1'|x_m1'] [x_m2'|x_m2'] //=] := (fndP, fndP).
- by move=> /(_ _ _ erefl erefl Px) ->.
- move=> _; rewrite in_fnd ?ed1 // => ?.
  by move: x_m2'; rewrite -ed2; case: (fndP m2 x).
- move=> _; rewrite [m2.[? x]]in_fnd ?ed2 // => ?.
  by move: x_m1'; rewrite -ed1; case: (fndP m1 x).
Qed.
