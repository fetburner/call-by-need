Require Import Autosubst.Autosubst.

Inductive term :=
  | tvar (x : var)
  | tapp (s t : term)
  | tabs (s : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.