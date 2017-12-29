Require Import Arith Relations.
Require Import Autosubst.Autosubst.

Inductive term :=
  | Var (x : var)
  | App (s t : term)
  | Lam (s : {bind term})
  | Let (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

(* A context free formalizations of a variant of Ariola and Felleisen's call-by-need lambda calculus *)

Inductive value : term -> Prop :=
  | Value_lam t : value (Lam t).

Inductive answer : term -> Prop :=
  | Answer_lam t : answer (Lam t)
  | Answer_app t a :
      answer a ->
      answer (Let t a).

Inductive needs : term -> var -> Prop :=
  | Needs_var x : needs (Var x) x
  | Needs_appL t1 t2 x :
      needs t1 x ->
      needs (App t1 t2) x
  | Needs_letL t1 t2 x :
      needs t1 x ->
      needs t2 0 ->
      needs (Let t1 t2) x
  | Needs_letR t1 t2 x :
      needs t2 (S x) ->
      needs (Let t1 t2) x.

Inductive reduceVCA : term -> term -> Prop :=
  | ReduceVCA_V v1 t2 t2' :
      value v1 ->
      needs t2 0 ->
      t2' = t2.[v1/] ->
      reduceVCA (Let v1 t2) t2'
  | ReduceVCA_C t1 a2 t3 t3' :
      answer a2 ->
      t3' = rename (+1)t3 ->
      reduceVCA (App (Let t1 a2) t3) (Let t1 (App a2 t3'))
  | ReduceVCA_A t1 a2 t3 t3' :
      answer a2 ->
      needs t3 0 ->
      t3' = rename (upren (+1)) t3 ->
      reduceVCA (Let (Let t1 a2) t3) (Let t1 (Let a2 t3'))
  | ReduceVCA_appL t1 t1' t2 :
      reduceVCA t1 t1' ->
      reduceVCA (App t1 t2) (App t1' t2)
  | ReduceVCA_letL t1 t1' t2 :
      reduceVCA t1 t1' ->
      needs t2 0 ->
      reduceVCA (Let t1 t2) (Let t1' t2)
  | ReduceVCA_letR t1 t2 t2' :
      reduceVCA t2 t2' ->
      reduceVCA (Let t1 t2) (Let t1 t2').

Inductive reduceI : term -> term -> Prop :=
  | RedNeed_I t1 t2 :
      reduceI (App (Lam t1) t2) (Let t2 t1)
  | RedNeed_appL t1 t1' t2 :
      reduceI t1 t1' ->
      reduceI (App t1 t2) (App t1' t2)
  | RedNeed_letL t1 t1' t2 :
      reduceI t1 t1' ->
      needs t2 0 ->
      reduceI (Let t1 t2) (Let t1' t2)
  | RedNeed_letR t1 t2 t2' :
      reduceI  t2 t2' ->
      reduceI (Let t1 t2) (Let t1 t2').

Hint Constructors value answer needs reduceVCA reduceI.
Local Hint Constructors clos_refl_trans.

Lemma reduceVCA_letL_multi t1 t1' t2 :
  needs t2 0 ->
  clos_refl_trans _ reduceVCA t1 t1' ->
  clos_refl_trans _ reduceVCA (Let t1 t2) (Let t1' t2).
Proof. induction 2; eauto. Qed.

Lemma reduceVCA_letR_multi t1 t2 t2' :
  clos_refl_trans _ reduceVCA t2 t2' ->
  clos_refl_trans _ reduceVCA (Let t1 t2) (Let t1 t2').
Proof. induction 1; eauto. Qed.

Hint Resolve reduceVCA_letL_multi reduceVCA_letR_multi.

Lemma value_impl_answer v : value v -> answer v.
Proof. inversion 1. constructor. Qed.
Hint Resolve value_impl_answer.

Lemma answer_needs_disjoint a :
  answer a ->
  forall x,
  needs a x ->
  False.
Proof. induction 1; inversion 1; subst; eauto. Qed.
Hint Resolve answer_needs_disjoint.

Lemma answer_reduceVCA_disjoint a :
  answer a ->
  forall t,
  reduceVCA a t ->
  False.
Proof. induction 1; inversion 1; subst; eauto. Qed.

Lemma answer_reduceI_disjoint a :
  answer a ->
  forall t,
  reduceI a t ->
  False.
Proof. induction 1; inversion 1; subst; eauto. Qed.

Lemma needs_unique x t :
  needs t x ->
  forall y,
  needs t y ->
  x = y.
Proof.
  induction 1; inversion 1; subst;
    repeat match goal with
    | H : needs ?t _, IH : forall x, needs ?t x -> _ = x |- _ => apply IH in H
    end; congruence.
Qed.

Lemma needs_reduceVCA_disjoint t x :
  needs t x ->
  forall t',
  reduceVCA t t' ->
  False.
Proof.
  induction 1; inversion 1; subst;
    repeat match goal with
    | H : needs ?t 0, H' : needs ?t (S _) |- _ => apply (needs_unique _ _ H) in H'; congruence
    end; eauto.
Qed.

Lemma needs_reduceI_disjoint t x :
  needs t x ->
  forall t',
  reduceI t t' ->
  False.
Proof.
  induction 1; inversion 1; subst;
    repeat match goal with
    | H : needs ?t 0, H' : needs ?t (S _) |- _ => apply (needs_unique _ _ H) in H'; congruence
    end; eauto.
Qed.

Lemma reduceVCA_reduceI_disjoint t t' :
  reduceVCA t t' ->
  forall t'',
  reduceI t t'' ->
  False.
Proof.
  Local Hint Resolve answer_reduceI_disjoint needs_reduceI_disjoint needs_reduceVCA_disjoint.
  induction 1; inversion 1; subst; eauto.
  - inversion H.
Qed.

Lemma reduceVCA_unique t t' :
  reduceVCA t t' ->
  forall t'',
  reduceVCA t t'' ->
  t' = t''.
Proof.
  induction 1; inversion 1; subst; f_equal;
    repeat match goal with
    | H : value (Let _ _) |- _ => inversion H
    | H : reduceVCA ?t _ |- _ =>
        let H' := fresh in
        assert (H' : answer t) by eauto;
        destruct (answer_reduceVCA_disjoint _ H' _ H)
    | H : needs ?t _, H' : reduceVCA ?t _ |- _ => destruct (needs_reduceVCA_disjoint _ _ H _ H')
    end; eauto.
Qed.

Lemma reduceI_unique t t' :
  reduceI t t' ->
  forall t'',
  reduceI t t'' ->
  t' = t''.
Proof.
  induction 1; inversion 1; subst; f_equal;
    repeat match goal with
    | H : reduceI (Lam _) _ |- _ => inversion H
    | H : needs ?t _, H' : reduceI ?t _ |- _ => destruct (needs_reduceI_disjoint _ _ H _ H')
    end; eauto.
Qed.

Theorem answer_or_stuck_or_reducible t :
  answer t \/
  (exists x, needs t x) \/
  (exists t', reduceVCA t t') \/
  (exists t', reduceI t t').
Proof.
  induction t as
    [ | ? [ Hanswer | [ [ ] | [ [ ] | [ ] ] ] ]
    | | ? [ Hanswer | [ [ ] | [ [ ] | [ ] ] ] ] ? [ | [ [ [ ] ] | [ [ ] | [ ] ] ] ] ]; eauto 6;
    inversion Hanswer; subst; eauto 6.
Qed.

