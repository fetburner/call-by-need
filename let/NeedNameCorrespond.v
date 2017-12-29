Require Import Autosubst.Autosubst.
Require Import Program Omega Relations.
From Metatheories Require Import ARS Term Reduction CBN Standardization CallByNeed CallByNeedContext VCANormal.

Local Hint Constructors clos_refl_trans.

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

Lemma expand_let_reduceVCA t t' : reduceVCA t t' -> expand_let t = expand_let t'.
Proof.
  induction 1; subst; simpl;
    try solve [ repeat rewrite <- expand_let_subst_single; repeat (f_equal; autosubst) ];
    congruence.
Qed.

Lemma expand_let_reduceVCA' E t t' :
  evalctx E ->
  reduceVCA' t t' ->
  expand_let (fill_hole E t) = expand_let (fill_hole E t').
Proof.
  induction 1; simpl.
  - inversion 1; subst; simpl.
    + repeat rewrite <- expand_let_subst_single.
      repeat rewrite subst_fill_hole.
      replace ((Var (bv E)).[upn (bv E) (v1 .: ids)]) with ((Var 0).[ren (+ bv E) >> upn (bv E) (v1 .: ids)])
        by (simpl; rewrite plusnO; reflexivity).
      rewrite up_liftn. simpl.
      replace ((rename (+S (bv E)) v1).[upn (bv E) (v1 .: ids)]) with (v1.[ren ( +1 )].[ren (+ bv E) >> upn (bv E) (v1 .: ids)]) by autosubst.
      rewrite up_liftn. autosubst.
    + repeat rewrite <- expand_let_subst_single.
      f_equal. autosubst.
    + repeat rewrite <- expand_let_subst_single.
      f_equal. autosubst.
  - intros. repeat rewrite <- expand_let_subst_single.
    f_equal. eauto.
  - intros. do 2 f_equal. eauto.
  - intros. f_equal. eauto.
Qed.

Lemma expand_let_answer a :
  answer a ->
  exists t, expand_let a = tabs t.
Proof.
  induction 1 as [ | ? ? ? [ ? IHanswer ] ]; simpl; eauto.
  rewrite IHanswer. simpl. eauto.
Qed.

Lemma expand_let_needs x t :
  needs t x ->
  needsn (expand_let t) x.
Proof.
  induction 1; simpl; eauto.
  - eapply needsn_subst; eauto.
  - apply needsn_subst with (x := S x); simpl; eauto.
Qed.

Lemma expand_let_reduceI t t' :
  reduceI t t' ->
  exists t0, cbn (expand_let t) t0 /\ clos_refl_trans _ red t0 (expand_let t').
Proof.
  induction 1 as
    [ | ? ? ? ? [ ? [ ] ]
      | ? ? ? ? [ ? [ ] ]
      | ? ? ? ? [ ? [ ] ] ]; simpl; eauto.
  - eapply cbn_subst' with (x := 0); simpl; eauto.
    + intros [ ]; eauto.
    + apply expand_let_needs; eauto.
  - eexists.  split.
    + apply cbn_subst. eauto.
    + eapply red_subst_multi; eauto.
Qed.

Lemma red_need_sound_aux t t' :
  clos_refl_trans _ (fun t t' => reduceVCA t t' \/ reduceI t t') t t' ->
  clos_refl_trans _ red (expand_let t) (expand_let t').
Proof.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  induction Hrt as [ | ? ? ? [ HreduceVCA | Hred ] ]; eauto.
  - apply expand_let_reduceVCA in HreduceVCA. congruence.
  - destruct (expand_let_reduceI _ _ Hred) as [ ? [ ] ]. eauto.
Qed.

Theorem red_need_sound t t' :
  clos_refl_trans _ (fun t t' => reduceVCA t t' \/ reduceI t t') t t' ->
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
  exists t', clos_refl_trans _ (fun t t' => reduceVCA t t' \/ reduceI t t') t t' /\ in_normal_form _ (fun t t' => reduceVCA t t' \/ reduceI t t') t'.
Proof.
  induction 1 as [ ? ? IH ]. intros t ?. subst.
  induction t as [ ? IH' ] using (well_founded_induction reduceVCA_well_founded).
  destruct (answer_or_stuck_or_reducible t) as [ ? | [ [ ? ? ] | [ [ ? HreduceVCA ] | [ ? Hred ] ] ] ]; eauto.
  - exists t. split; eauto.
    intros ? [ ? | ? ].
    + eapply answer_reduceVCA_disjoint; eauto.
    + eapply answer_reduceI_disjoint; eauto.
  - exists t. split; eauto.
    intros ? [ ? | ? ].
    + eapply needs_reduceVCA_disjoint; eauto.
    + eapply needs_reduceI_disjoint; eauto.
  - destruct (IH' _ HreduceVCA) as [ ? [ ] ];
      try rewrite <- (expand_let_reduceVCA _ _ HreduceVCA) in *;
      eauto 6.
  - destruct (IH _ (expand_let_reduceI _ _ Hred) _ eq_refl) as [ ? [ ] ]. eauto 6.
Qed.

Theorem red_need_complete t t0 :
  clos_refl_trans _ cbn (expand_let t) (tabs t0) ->
  exists t', clos_refl_trans _ (fun t t' => reduceVCA t t' \/ reduceI t t') t t' /\ answer t' /\ clos_refl_trans _ red (tabs t0) (expand_let t').
Proof.
  intros Hnormalizing.
  edestruct red_need_normalize with (t := t) as [ t' [ Hrt Hnf ] ]; eauto.
  - apply quasi_cbn_theorem'.
    eapply normalizing_and_deterministic_impl_terminating; eauto.
    + intros ? ? ? ?. apply cbn_det; eauto.
    + inversion 1.
  - destruct (answer_or_stuck_or_reducible t') as [ Hanswer | [ [ ? Hneeds ] | [ [ ? HreduceVCA ] | [ ? Hred ] ] ] ].
    + destruct (red_need_sound _ _ Hrt Hanswer) as [ ? [ Hnormalizing' ] ].
      destruct (cbn_confluent _ _ _ Hnormalizing Hnormalizing') as [ ? [ Hrefl Hrefl' ] ].
      destruct (strip_lemma _ _ _ _ Hrefl) as [ | [ ? [ Hcontra ]] ]; [ subst | inversion Hcontra ].
      destruct (strip_lemma _ _ _ _ Hrefl') as [ Heq | [ ? [Hcontra ] ] ]; [ rewrite Heq in * | inversion Hcontra ].  eauto.
    + apply red_need_sound_aux in Hrt.
      destruct (red_confluent _ _ _ (cbn_multi_impl_red_multi _ _ Hnormalizing) Hrt) as [ ? [ Hrt' Hrt'' ] ].
      destruct (red_abs_multi_inv _ _ Hrt' _ eq_refl) as [? [ ] ]. subst.
      specialize (needsn_preserved_by_red_multi _ _ _ Hrt'' (expand_let_needs _ _ Hneeds)).
      inversion 1.
    + edestruct Hnf; simpl; eauto.
    + edestruct Hnf; simpl; eauto.
Qed.
