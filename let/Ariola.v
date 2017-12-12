Require Import Autosubst.Autosubst.
Require Import Program Omega Relations.
From Metatheories Require Import ARS Term Reduction CBN Standardization.

Inductive term :=
  | Var (x : var)
  | App (s t : term)
  | Lam (s : {bind term})
  | Let (s : term) (t : {bind term}).

Instance Ids_term : Ids term. derive. Defined.
Instance Rename_term : Rename term. derive. Defined.
Instance Subst_term : Subst term. derive. Defined.
Instance SubstLemmas_term : SubstLemmas term. derive. Qed.

Inductive value : term -> Prop :=
  | Value_lam t : value (Lam t).

Inductive answer : term -> Prop :=
  | Answer_lam t : answer (Lam t)
  | Answer_app t a :
      answer a ->
      answer (Let t a).

Inductive demands : var -> term -> Prop :=
  | Demands_var x : demands x (Var x)
  | Demands_appL t1 t2 x :
      demands x t1 ->
      demands x (App t1 t2)
  | Demands_letL t1 t2 x :
      demands x t1 ->
      demands 0 t2 ->
      demands x (Let t1 t2)
  | Demands_letR t1 t2 x :
      demands (S x) t2 ->
      demands x (Let t1 t2).

Inductive reassoc : term -> term -> Prop :=
  | Reassoc_V v1 t2 t2' :
      value v1 ->
      demands 0 t2 ->
      t2' = t2.[v1/] ->
      reassoc (Let v1 t2) t2'
  | Reassoc_C t1 a2 t3 t3' :
      answer a2 ->
      t3' = rename (+1)t3 ->
      reassoc (App (Let t1 a2) t3) (Let t1 (App a2 t3'))
  | Reassoc_A t1 a2 t3 t3' :
      answer a2 ->
      demands 0 t3 ->
      t3' = rename (upren (+1)) t3 ->
      reassoc (Let (Let t1 a2) t3) (Let t1 (Let a2 t3'))
  | Reassoc_appL t1 t1' t2 :
      reassoc t1 t1' ->
      reassoc (App t1 t2) (App t1' t2)
  | Reassoc_letL t1 t1' t2 :
      reassoc t1 t1' ->
      demands 0 t2 ->
      reassoc (Let t1 t2) (Let t1' t2)
  | Reassoc_letR t1 t2 t2' :
      reassoc t2 t2' ->
      reassoc (Let t1 t2) (Let t1 t2').

Inductive red_need : term -> term -> Prop :=
  | RedNeed_I t1 t2 :
      red_need (App (Lam t1) t2) (Let t2 t1)
  | RedNeed_appL t1 t1' t2 :
      red_need t1 t1' ->
      red_need (App t1 t2) (App t1' t2)
  | RedNeed_letL t1 t1' t2 :
      red_need t1 t1' ->
      demands 0 t2 ->
      red_need (Let t1 t2) (Let t1' t2)
  | RedNeed_letR t1 t2 t2' :
      red_need  t2 t2' ->
      red_need (Let t1 t2) (Let t1 t2').

Hint Constructors value answer demands reassoc red_need clos_refl_trans.

Lemma reassoc_letL_multi t1 t1' t2 :
  demands 0 t2 ->
  clos_refl_trans _ reassoc t1 t1' ->
  clos_refl_trans _ reassoc (Let t1 t2) (Let t1' t2).
Proof. induction 2; eauto. Qed.

Lemma reassoc_letR_multi t1 t2 t2' :
  clos_refl_trans _ reassoc t2 t2' ->
  clos_refl_trans _ reassoc (Let t1 t2) (Let t1 t2').
Proof. induction 1; eauto. Qed.

Hint Resolve reassoc_letL_multi reassoc_letR_multi.

Section CallByNeedDeterminism.
  Lemma value_impl_answer v : value v -> answer v.
  Proof. inversion 1. constructor. Qed.
  Hint Resolve value_impl_answer.

  Lemma answer_demands_disjoint a :
    answer a ->
    forall x,
    demands x a ->
    False.
  Proof. induction 1; inversion 1; subst; eauto. Qed.
  Hint Resolve answer_demands_disjoint.

  Lemma answer_reassoc_disjoint a :
    answer a ->
    forall t,
    reassoc a t ->
    False.
  Proof. induction 1; inversion 1; subst; eauto. Qed.

  Lemma answer_red_need_disjoint a :
    answer a ->
    forall t,
    red_need a t ->
    False.
  Proof. induction 1; inversion 1; subst; eauto. Qed.

  Lemma demands_unique x t :
    demands x t ->
    forall y,
    demands y t ->
    x = y.
  Proof.
    induction 1; inversion 1; subst;
      repeat match goal with
      | H : demands _ ?t, IH : forall x, demands x ?t -> _ = x |- _ => apply IH in H
      end; congruence.
  Qed.

  Lemma demands_reassoc_disjoint x t :
    demands x t ->
    forall t',
    reassoc t t' ->
    False.
  Proof.
    induction 1; inversion 1; subst;
      repeat match goal with
      | H : demands 0 ?t, H' : demands (S _) ?t |- _ => apply (demands_unique _ _ H) in H'; congruence
      end; eauto.
  Qed.

  Lemma demands_red_need_disjoint x t :
    demands x t ->
    forall t',
    red_need t t' ->
    False.
  Proof.
    induction 1; inversion 1; subst;
      repeat match goal with
      | H : demands 0 ?t, H' : demands (S _) ?t |- _ => apply (demands_unique _ _ H) in H'; congruence
      end; eauto.
  Qed.

  Lemma reassoc_red_need_disjoint t t' :
    reassoc t t' ->
    forall t'',
    red_need t t'' ->
    False.
  Proof.
    Local Hint Resolve answer_red_need_disjoint demands_red_need_disjoint demands_reassoc_disjoint.
    induction 1; inversion 1; subst; eauto.
    - inversion H.
  Qed.

  Lemma reassoc_unique t t' :
    reassoc t t' ->
    forall t'',
    reassoc t t'' ->
    t' = t''.
  Proof.
    induction 1; inversion 1; subst; f_equal;
      repeat match goal with
      | H : value (Let _ _) |- _ => inversion H
      | H : reassoc ?t _ |- _ =>
          let H' := fresh in
          assert (H' : answer t) by eauto;
          destruct (answer_reassoc_disjoint _ H' _ H)
      | H : demands _ ?t, H' : reassoc ?t _ |- _ => destruct (demands_reassoc_disjoint _ _ H _ H')
      end; eauto.
  Qed.

  Lemma red_need_unique t t' :
    red_need t t' ->
    forall t'',
    red_need t t'' ->
    t' = t''.
  Proof.
    induction 1; inversion 1; subst; f_equal;
      repeat match goal with
      | H : red_need (Lam _) _ |- _ => inversion H
      | H : demands _ ?t, H' : red_need ?t _ |- _ => destruct (demands_red_need_disjoint _ _ H _ H')
      end; eauto.
  Qed.
  
  Theorem answer_or_reducible_or_stuck t :
    answer t \/
    (exists x, demands x t) \/
    (exists t', reassoc t t') \/
    (exists t', red_need t t').
  Proof.
    induction t as
      [ | ? [ Hanswer | [ [ ] | [ [ ] | [ ] ] ] ]
      | | ? [ Hanswer | [ [ ] | [ [ ] | [ ] ] ] ] ? [ | [ [ [ ] ] | [ [ ] | [ ] ] ] ] ]; eauto 6;
      inversion Hanswer; subst; eauto 6.
  Qed.
End CallByNeedDeterminism.

Section ReassocTerminating.
  Fixpoint weight env t :=
    match t with
    | Var x => env x
    | App t1 t2 => 2 * weight env t1 + 2 * weight env t2
    | Lam t => weight (1 .: env) t
    | Let t1 t2 => 2 * weight env t1 + weight (S (weight env t1) .: env) t2
    end.

  Lemma weight_least t : forall env,
    (forall x, 0 < env x) ->
    0 < weight env t.
  Proof.
    induction t as [ | ? IHt1 | ? IHt | ? IHt1 ? IHt2 ]; simpl; intros ? Henv; eauto.
    - specialize (IHt1 _ Henv).
      omega.
    - apply IHt.
      intros [ | ? ]; simpl; eauto.
    - specialize (IHt1 _ Henv).
      omega.
  Qed.

  Lemma weight_monotone t : forall env env',
    (forall x, env x <= env' x) ->
    weight env t <= weight env' t.
  Proof.
    Local Hint Resolve le_n_S.
    induction t as [ | | ? IHt | ? ? ? IHt2 ]; intros ? ? Henv; simpl;
      repeat match goal with
      | |- ?n + ?m <= ?n' + ?m' =>
          assert (n <= n');
          [| assert (m <= m'); [| omega ]]
      end; eauto.
    - apply IHt.
      intros [ | ? ]; simpl; eauto.
    - apply IHt2.
      intros [ | ? ]; simpl in *; eauto.
  Qed.

  Corollary weight_ext  env env' t:
    (forall x, env x = env' x) ->
    weight env t = weight env' t.
  Proof.
    intros Henv.
    assert (weight env t <= weight env' t);
    [ | assert (weight env' t <= weight env t) ];
    solve [ apply weight_monotone; intros ?; rewrite Henv; omega | omega ].
  Qed.

  Lemma weight_rename t : forall r env,
    weight env (rename r t) = weight (r >>> env) t.
  Proof.
    induction t as [ | | ? IHt | ? IHt1 ? IHt2 ]; intros ? ?; simpl;
      repeat (rewrite plusnO || rewrite plus_assoc); eauto.
    - rewrite IHt.
      apply weight_ext.
      intros [ | ? ]; reflexivity.
    - rewrite IHt1.
      rewrite IHt2.
      f_equal.
      apply weight_ext.
      intros [ | ? ]; reflexivity.
  Qed.

  Lemma weight_subst t : forall s env,
    weight env t.[s] = weight (fun x => weight env (s x)) t.
  Proof.
    induction t as [ | | ? IHt | ? ? ? IHt2 ]; simpl; intros ? ?;
      repeat match goal with
      | |- ?n + ?m = ?n' + ?m' =>
          assert (n = n');
          [| assert (m = m'); [| omega ]]
      end; eauto.
    - rewrite IHt.
      apply weight_ext.
      intros [ | ? ]; simpl; eauto.
      apply weight_rename.
    - rewrite IHt2.
      apply weight_ext.
      intros [ | ? ]; simpl; eauto.
      apply weight_rename.
  Qed.

  Lemma weight_demands x t :
    demands x t ->
    forall env env',
    (forall x, env x <= env' x) ->
    env x < env' x ->
    weight env t < weight env' t.
  Proof.
    Local Hint Resolve le_n_S weight_monotone.
    induction 1; simpl; intros ? ? Henv ?;
      repeat (rewrite plusnO || rewrite <- plus_assoc);
      repeat match goal with
      | Hd : demands ?x ?t, He : ?env ?x < ?env' ?x |- weight ?env ?t + _ < weight ?env' ?t + _ => apply plus_lt_le_compat
      | |- _ + _ < _ + _ => apply plus_le_lt_compat
      | |- _ + _ <= _ + _ => apply plus_le_compat
      end; eauto.
    - apply weight_monotone.
      intros [|?]; simpl; eauto.
    - apply IHdemands; simpl; eauto.
      intros [|?]; simpl; eauto.
  Qed.

  Lemma reassoc_well_founded_aux t t' :
    reassoc t t' ->
    forall env, (forall x, 0 < env x) -> weight env t' < weight env t.
  Proof.
    induction 1; simpl; subst; intros env Henv;
      repeat (rewrite plusnO || rewrite plus_assoc || rewrite weight_rename); eauto.
    - rewrite weight_subst.
      rewrite plus_comm.
      apply lt_plus_trans.
      apply (weight_demands _ _ H0); simpl.
      + intros [|?]; simpl; omega.
      + omega.
    - generalize (weight_least t1 _ Henv). intros ?.
      replace (((+1) >>> S (weight env t1) .: env)) with env by autosubst.
      omega.
    - generalize (weight_least t1 _ Henv). intros ?.
      assert (weight (upren (+1) >>> S (weight (S (weight env t1) .: env) a2) .: S (weight env t1) .: env) t3 <= weight (S (weight env t1 + weight env t1 + weight (S (weight env t1) .: env) a2) .: env) t3).
      { apply weight_monotone.
        intros [|?]; simpl; omega. }
      omega.
    - specialize (IHreassoc _ Henv).
      omega.
    - generalize (IHreassoc _ Henv). intros ?.
      apply plus_lt_le_compat.
      + omega.
      + apply weight_monotone.
        intros [|?]; simpl; omega.
    - apply plus_lt_compat_l.
      apply IHreassoc.
      intros [|?]; simpl; eauto.
      omega.
  Qed.

  Theorem reassoc_well_founded : well_founded (fun t t' => reassoc t' t).
  Proof.
    intros t.
    induction t as [ ? IH ] using (well_founded_induction (well_founded_ltof _ (weight (fun _ => 1)))).
    constructor.
    intros ? Hreassoc.
    apply IH.
    apply reassoc_well_founded_aux; eauto.
  Qed.
End ReassocTerminating.

Section CallByNeedCorrectness.
  Fixpoint expand_let t :=
    match t with
    | Var x => tvar x
    | App t1 t2 => tapp (expand_let t1) (expand_let t2)
    | Lam t => tabs (expand_let t)
    | Let t1 t2 => (expand_let t2).[expand_let t1/]
    end.

  Lemma expand_let_rename t : forall r,
    expand_let (rename r t) = rename r (expand_let t).
  Proof.
    induction t as [ | | | ? IHt1 ? IHt2 ]; simpl; intros ?; f_equal; eauto.
    - rewrite IHt1.
      rewrite IHt2.
      autosubst.
  Qed.

  Lemma expand_let_subst t : forall s,
    expand_let (t.[s]) = (expand_let t).[s >>> expand_let].
  Proof.
    induction t as [ | | ? IHt | ? IHt1 ? IHt2 ]; intros ?; simpl; try solve [ f_equal; eauto ].
    - rewrite IHt.
      do 2 f_equal.
      f_ext.
      intros [ | ? ]; simpl; eauto.
      apply expand_let_rename.
    - rewrite IHt1.
      rewrite IHt2.
      repeat rewrite subst_comp.
      f_equal.
      f_ext.
      unfold up.
      intros [ | ? ]; simpl; eauto.
      rewrite expand_let_rename.
      autosubst.
  Qed.

  Corollary expand_let_subst_single t1 t2 : expand_let (t1.[t2/]) = (expand_let t1).[expand_let t2/].
  Proof.
    rewrite expand_let_subst.
    autosubst.
  Qed.

  Lemma expand_let_reassoc t t' : reassoc t t' -> expand_let t = expand_let t'.
  Proof.
    induction 1; subst; simpl;
      try solve [ repeat rewrite <- expand_let_subst_single; repeat (f_equal; autosubst) ];
      congruence.
  Qed.

  Lemma expand_let_answer a :
    answer a ->
    exists t, expand_let a = tabs t.
  Proof.
    induction 1 as [ | ? ? ? [ ? IHanswer ] ]; simpl; eauto.
    rewrite IHanswer. simpl. eauto.
  Qed.

  Lemma expand_let_demands x t :
    demands x t ->
    stuck_in_var x (expand_let t).
  Proof.
    induction 1; simpl; eauto.
    - eapply stuck_in_var_subst; eauto.
    - apply stuck_in_var_subst with (x := S x); simpl; eauto.
  Qed.

  Lemma expand_let_red_need t t' :
    red_need t t' ->
    exists t0, cbn (expand_let t) t0 /\ clos_refl_trans _ red t0 (expand_let t').
  Proof.
    induction 1 as
      [ | ? ? ? ? [ ? [ ] ]
        | ? ? ? ? [ ? [ ] ]
        | ? ? ? ? [ ? [ ] ] ]; simpl; eauto.
    - eapply cbn_subst' with (x := 0); simpl; eauto.
      + intros [ ]; eauto.
      + apply expand_let_demands; eauto.
    - eexists.  split.
      + apply cbn_subst. eauto.
      + eapply red_subst_multi; eauto.
  Qed.

  Lemma red_need_sound_aux t t' :
    clos_refl_trans _ (fun t t' => reassoc t t' \/ red_need t t') t t' ->
    clos_refl_trans _ red (expand_let t) (expand_let t').
  Proof.
    intros Hrt.
    apply clos_rt_rt1n in Hrt.
    induction Hrt as [ | ? ? ? [ Hreassoc | Hred ] ]; eauto.
    - apply expand_let_reassoc in Hreassoc. congruence.
    - destruct (expand_let_red_need _ _ Hred) as [ ? [ ] ]. eauto.
  Qed.

  Theorem red_need_sound t t' :
    clos_refl_trans _ (fun t t' => reassoc t t' \/ red_need t t') t t' ->
    answer t' ->
    exists t0, clos_refl_trans _ cbn (expand_let t) (tabs t0) /\ clos_refl_trans _ red (tabs t0) (expand_let t').
  Proof.
    intros Hrt Hanswer.
    destruct (expand_let_answer _ Hanswer) as [ ? Heq ].
    apply red_need_sound_aux in Hrt.
    rewrite Heq in Hrt.
    destruct (call_by_name_property _ _ Hrt) as [ ? [ ? Hrt' ] ].
    apply red_abs_multi in Hrt'.
    rewrite <- Heq in Hrt'.
    eauto.
  Qed.
  
  Lemma red_need_normalize t0 :
    Acc (fun t3 t1 => exists t2, cbn t1 t2 /\ clos_refl_trans _ red t2 t3) t0 ->
    forall t, expand_let t = t0 ->
    exists t', clos_refl_trans _ (fun t t' => reassoc t t' \/ red_need t t') t t' /\ in_normal_form _ (fun t t' => reassoc t t' \/ red_need t t') t'.
  Proof.
    induction 1 as [ ? ? IH ]. intros t ?. subst.
    induction t as [ ? IH' ] using (well_founded_induction reassoc_well_founded).
    destruct (answer_or_reducible_or_stuck t) as [ ? | [ [ ? ? ] | [ [ ? Hreassoc ] | [ ? Hred ] ] ] ]; eauto.
    - exists t. split; eauto.
      intros ? [ ? | ? ].
      + eapply answer_reassoc_disjoint; eauto.
      + eapply answer_red_need_disjoint; eauto.
    - exists t. split; eauto.
      intros ? [ ? | ? ].
      + eapply demands_reassoc_disjoint; eauto.
      + eapply demands_red_need_disjoint; eauto.
    - destruct (IH' _ Hreassoc) as [ ? [ ] ];
        try rewrite <- (expand_let_reassoc _ _ Hreassoc) in *;
        eauto 6.
    - destruct (IH _ (expand_let_red_need _ _ Hred) _ eq_refl) as [ ? [ ] ]. eauto 6.
  Qed.

  Theorem red_need_complete t t0 :
    clos_refl_trans _ cbn (expand_let t) (tabs t0) ->
    exists t', clos_refl_trans _ (fun t t' => reassoc t t' \/ red_need t t') t t' /\ answer t' /\ clos_refl_trans _ red (tabs t0) (expand_let t').
  Proof.
    intros Hnormalizing.
    edestruct red_need_normalize with (t := t) as [ t' [ Hrt Hnf ] ]; eauto.
    - apply quasi_cbn_theorem'.
      eapply normalizing_and_deterministic_impl_terminating; eauto.
      + intros ? ? ? ?. apply cbn_det; eauto.
      + inversion 1.
    - destruct (answer_or_reducible_or_stuck t') as [ Hanswer | [ [ ? Hdemands ] | [ [ ? Hreassoc ] | [ ? Hred ] ] ] ].
      + destruct (red_need_sound _ _ Hrt Hanswer) as [ ? [ Hnormalizing' ] ].
        destruct (cbn_confluent _ _ _ Hnormalizing Hnormalizing') as [ ? [ Hrefl Hrefl' ] ].
        destruct (strip_lemma _ _ _ _ Hrefl) as [ | [ ? [ Hcontra ]] ]; [ subst | inversion Hcontra ].
        destruct (strip_lemma _ _ _ _ Hrefl') as [ Heq | [ ? [Hcontra ] ] ]; [ rewrite Heq in * | inversion Hcontra ].  eauto.
      + apply red_need_sound_aux in Hrt.
        destruct (red_confluent _ _ _ (cbn_multi_impl_red_multi _ _ Hnormalizing) Hrt) as [ ? [ Hrt' Hrt'' ] ].
        destruct (red_abs_multi_inv _ _ Hrt' _ eq_refl) as [? [ ] ]. subst.
        specialize (stuck_in_var_preserved_by_red_multi _ _ _ Hrt'' (expand_let_demands _ _ Hdemands)).
        inversion 1.
      + edestruct Hnf; simpl; eauto.
      + edestruct Hnf; simpl; eauto.
  Qed.
End CallByNeedCorrectness.
