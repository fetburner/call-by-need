Require Import Arith Relations Omega.
Require Import Autosubst.Autosubst.
From Metatheories Require Import CallByNeed CallByNeedContext.

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

Lemma weight_needs x t :
  needs t x ->
  forall env env',
  (forall x, env x <= env' x) ->
  env x < env' x ->
  weight env t < weight env' t.
Proof.
  Local Hint Resolve le_n_S weight_monotone.
  induction 1; simpl; intros ? ? Henv ?;
    repeat (rewrite plusnO || rewrite <- plus_assoc);
    repeat match goal with
    | Hd : needs ?t ?x, He : ?env ?x < ?env' ?x |- weight ?env ?t + _ < weight ?env' ?t + _ => apply plus_lt_le_compat
    | |- _ + _ < _ + _ => apply plus_le_lt_compat
    | |- _ + _ <= _ + _ => apply plus_le_compat
    end; eauto.
  - apply weight_monotone.
    intros [ | ? ]; simpl; eauto.
  - apply IHneeds; simpl; eauto.
    intros [ | ? ]; simpl; eauto.
Qed.

Lemma weight_context C t t' : forall env,
  (forall env',
    (forall x, x < bv C -> 0 < env' x) ->
    (forall x, env' (bv C + x) = env x) ->
    weight env' t < weight env' t') ->
  weight env (fill_hole C t) < weight env (fill_hole C t').
Proof.
  induction C; intros env Henv; simpl in *; eauto.
  - apply Henv; eauto.
    intros. omega.
  - specialize (IHC _ Henv). omega.
  - specialize (IHC _ Henv). omega.
  - apply IHC. intros ? H1 Henv'. apply Henv.
    + intros x ?. destruct (Nat.eq_dec x (bv c)).
      * subst. specialize (Henv' 0). simpl in *. rewrite plusnO in *. omega.
      * apply H1. omega.
    + intros ?. rewrite <- plusnS. apply Henv'.
  - specialize (IHC _ Henv). apply plus_lt_le_compat; try omega.
    apply weight_monotone. intros [ | ? ]; simpl; omega.
  - apply plus_le_lt_compat; try omega.
    apply IHC. intros ? H1 Henv'. apply Henv.
    + intros x ?. destruct (Nat.eq_dec x (bv c)).
      * subst. specialize (Henv' 0). simpl in *. rewrite plusnO in *. omega.
      * apply H1. omega.
    + intros ?. rewrite <- plusnS. apply Henv'.
Qed.

Lemma reduceVCA_well_founded_aux t t' :
  reduceVCA t t' ->
  forall env, (forall x, 0 < env x) -> weight env t' < weight env t.
Proof.
  induction 1; simpl; subst; intros env Henv;
    repeat (rewrite plusnO || rewrite plus_assoc || rewrite weight_rename); eauto.
  - rewrite weight_subst.
    rewrite plus_comm.
    apply lt_plus_trans.
    apply (weight_needs _ _ H0); simpl.
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
  - specialize (IHreduceVCA _ Henv).
    omega.
  - generalize (IHreduceVCA _ Henv). intros ?.
    apply plus_lt_le_compat.
    + omega.
    + apply weight_monotone.
      intros [|?]; simpl; omega.
  - apply plus_lt_compat_l.
    apply IHreduceVCA.
    intros [|?]; simpl; eauto.
    omega.
Qed.

Theorem reduceVCA_well_founded : well_founded (fun t t' => reduceVCA t' t).
Proof.
  intros t.
  induction t as [ ? IH ] using (well_founded_induction (well_founded_ltof _ (weight (fun _ => 1)))).
  constructor.
  intros ? HreduceVCA.
  apply IH.
  apply reduceVCA_well_founded_aux; eauto.
Qed.

Lemma reduceVCA'_well_founded_aux t t' :
  reduceVCA' t t' ->
  forall env, (forall x, 0 < env x) -> weight env t' < weight env t.
Proof.
  induction 1; simpl; subst; intros env Henv;
    repeat (rewrite plusnO || rewrite plus_assoc || rewrite weight_rename); eauto.
  - apply plus_lt_compat_l; try omega.
    apply weight_context. simpl. intros ? H1 Henv'.
    rewrite weight_rename. rewrite weight_ext with (env' := env).
    + specialize (Henv' 0). rewrite plusnO in *. simpl in *. omega.
    + intros x. specialize (Henv' (S x)). simpl in *. rewrite plusnS in *. eauto.
  - replace (((+1) >>> S (weight env t1) .: env)) with env by autosubst.
    generalize (weight_least t1 _ Henv). omega.
  - assert (weight (upren (+1) >>> S (weight (S (weight env t1) .: env) a2) .: S (weight env t1) .: env) (fill_hole E (Var (bv E)))
       <= weight (S (weight env t1 + weight env t1 + weight (S (weight env t1) .: env) a2) .: env) (fill_hole E (Var (bv E)))).
    { apply weight_monotone.
      intros [ | ? ]; simpl; omega. }
    generalize (weight_least t1 _ Henv). omega.
Qed.

Lemma reduceVCA'_well_founded :
  well_founded (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1' /\ t' = fill_hole E t1 /\ reduceVCA' t1 t1').
Proof.
  intros t. induction t as [ ? IH ] using (well_founded_induction (well_founded_ltof _ (weight (fun _ => 1)))).
  constructor. intros ? [ E [ ? [ ? [ ? [ ? [ ? ? ]]]]]]. subst. apply IH.
  unfold ltof. apply weight_context. intros ? H1 Henv. apply reduceVCA'_well_founded_aux; eauto.
  intros y. destruct (lt_dec y (bv E)); eauto.
  specialize (Henv (y - bv E)). replace (bv E + (y - bv E)) with y in *.
  - omega.
  - apply le_plus_minus. omega.
Qed.
