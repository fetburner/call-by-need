Require Import Arith Relations.
Require Import Autosubst.Autosubst.
From Metatheories Require Import CallByNeed.

Inductive context :=
  | CHole
  | CAppL (c : context) (t : term)
  | CAppR (t : term) (c : context)
  | CLam (c : { bind term in context })
  | CLetL (c : context) (t : { bind term })
  | CLetR (t : term) (c : { bind term in context }).

Instance HSubst_term_in_context : HSubst term context. derive. Defined.

Fixpoint fill_hole c t :=
  match c with
  | CHole => t
  | CAppL c s => App (fill_hole c t) s
  | CAppR s c => App s (fill_hole c t)
  | CLam c => Lam (fill_hole c t)
  | CLetL c s => Let (fill_hole c t) s
  | CLetR s c => Let s (fill_hole c t)
  end.

(* How many free variables are bound during the hole filling *)
Fixpoint bv c :=
  match c with
  | CHole => 0
  | CAppL c _ => bv c
  | CAppR _ c => bv c
  | CLam c => S (bv c)
  | CLetL c _ => bv c
  | CLetR _ c => S (bv c)
  end.

Lemma subst_fill_hole c t : forall s,
  (fill_hole c t).[s] = fill_hole c.|[s] t.[upn (bv c) s].
Proof.
  induction c; simpl; intros ?; f_equal; eauto.
  - rewrite IHc. rewrite fold_upn_up. eauto.
  - rewrite IHc. rewrite fold_upn_up. eauto.
Qed.

(* A formalization of Ariola and Felleisen's call-by-need lambda calculus *)

(* evaluation context *)
Inductive evalctx : context -> Prop :=
  | EC_Hole : evalctx CHole
  | EC_AppL E t :
      evalctx E ->
      evalctx (CAppL E t)
  | EC_letL E E' t :
      evalctx E ->
      evalctx E' ->
      t = fill_hole E' (Var (bv E')) ->
      evalctx (CLetL E t)
  | EC_letR E t :
      evalctx E ->
      evalctx (CLetR t E).

(* standard reduction rules *)

Inductive reduceI' : term -> term -> Prop :=
  | ReduceI'_I t1 t2 :
      reduceI' (App (Lam t1) t2) (Let t2 t1).

Inductive reduceVCA' : term -> term -> Prop :=
  | ReduceVCA'_V E v1 t2 t2' :
      value v1 ->
      evalctx E ->
      t2 = fill_hole E (Var (bv E)) ->
      t2' = fill_hole E (rename (+ S (bv E)) v1) ->
      reduceVCA' (Let v1 t2) (Let v1 t2')
  | ReduceVCA'_C t1 a2 t3 t3' :
      answer a2 ->
      t3' = rename (+1)t3 ->
      reduceVCA' (App (Let t1 a2) t3) (Let t1 (App a2 t3'))
  | ReduceVCA'_A E t1 a2 t3 t3' :
      answer a2 ->
      evalctx E ->
      t3 = fill_hole E (Var (bv E)) ->
      t3' = rename (upren (+1)) t3 ->
      reduceVCA' (Let (Let t1 a2) t3) (Let t1 (Let a2 t3')).

Hint Constructors evalctx reduceI' reduceVCA'.

(* the correspondence with the context free formalism *)

Lemma needs_evalctx t x :
  needs t x ->
  exists E, evalctx E /\ t = fill_hole E (Var (bv E + x)).
Proof.
  induction 1 as [ | ? t2 ? ? [ E [ ] ] | ? t2 ? ? [ E [ ] ] ? [ E' [ ] ] | t1 ? ? ? [ E [ ] ] ]; simpl.
  - exists CHole. simpl. eauto.
  - exists (CAppL E t2). simpl. subst. eauto.
  - exists (CLetL E t2). simpl. subst. rewrite plusnO. eauto.
  - exists (CLetR t1 E). simpl. subst. rewrite plusnS. eauto.
Qed.

Lemma evalctx_needs E :
  evalctx E ->
  forall x, needs (fill_hole E (Var (bv E + x))) x.
Proof.
  induction 1; intros x; simpl; subst; eauto.
  - specialize (IHevalctx2 0). rewrite plusnO in *. eauto.
  - specialize (IHevalctx (S x)). rewrite plusnS in *. eauto.
Qed.

Corollary evalctx_needs0 E :
  evalctx E -> needs (fill_hole E (Var (bv E))) 0.
Proof. intros Hevalctx. specialize (evalctx_needs _ Hevalctx 0). rewrite plusnO. eauto. Qed.

Lemma reduceI_reduceI' t t' :
  reduceI t t' ->
  exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ reduceI' t1 t1'.
Proof.
  induction 1 as [ | ? ? t2 ? [ E [ ? [ ? [ ? [ ? [ ] ] ] ] ] ] | ? ? t2 ? [ E [ ? [ ? [ ? [ ? [ ] ] ] ] ] ] Hneeds | t1 ? ? ? [ E [ ? [ ? [ ? [ ? [ ] ] ] ] ] ] ]; simpl; subst.
  - exists CHole. simpl. eauto 6.
  - exists (CAppL E t2). simpl. eauto 7.
  - exists (CLetL E t2). simpl. destruct (needs_evalctx _ _ Hneeds) as [ ? [ ] ]. subst. rewrite plusnO. eauto 8.
  - exists (CLetR t1 E). simpl. eauto 7.
Qed.

Lemma reduceI'_reduceI E t t' :
  evalctx E ->
  reduceI' t t' ->
  reduceI (fill_hole E t) (fill_hole E t').
Proof.
  induction 1 as [ | | ? ? ? ? ? Hevalctx | ]; simpl; subst; eauto.
  - inversion 1. eauto.
  - specialize (evalctx_needs0 _ Hevalctx). eauto.
Qed.

Lemma reduceVCA_reduceVCA' t t' :
  reduceVCA t t' ->
  exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ reduceVCA' t1 t1'.
Proof.
  induction 1 as [ ? ? ? ? Hneeds | | ? ? ? ? ? Hneeds | ? ? t2 ? [ E [ ? [ ? [ ? [ ] ] ] ] ] | ? ? t2 ? [ E [ ? [ ? [ ? [ ] ] ] ] ] Hneeds | t1 ? ? ? [ E [ ? [ ? [ ? [ ] ] ] ] ] ].
  - destruct (needs_evalctx _ _ Hneeds) as [ ? [ ] ]. rewrite plusnO in *.
    exists CHole. simpl. eauto 6.
  - exists CHole. simpl. eauto 6.
  - destruct (needs_evalctx _ _ Hneeds) as [ ? [ ] ]. rewrite plusnO in *.
    exists CHole. simpl. eauto 6.
  - exists (CAppL E t2). simpl. subst. eauto 6.
  - destruct (needs_evalctx _ _ Hneeds) as [ ? [ ] ]. rewrite plusnO in *.
    exists (CLetL E t2). simpl. subst. eauto 6.
  - exists (CLetR t1 E). simpl. subst. eauto 6.
Qed.

Lemma reduceVCA'_reduceVCA E t1 t1':
  reduceVCA' t1 t1' ->
  evalctx E ->
  exists t', reduceVCA (fill_hole E t1) t'.
Proof.
  intros Hred; induction 1 as [ | ? ? ? [ ] | ? ? ? ? [] Hevalctx [] | ? ? ? [] ]; simpl; eauto.
  - inversion Hred as [ ? ? ? ? ? Hevalctx | | ? ? ? ? ? ? Hevalctx ]; subst; eauto.
    + specialize (evalctx_needs0 _ Hevalctx). eauto.
    + specialize (evalctx_needs0 _ Hevalctx). eauto.
  - specialize (evalctx_needs0 _ Hevalctx). subst. eauto.
Qed.