Require Import Arith Relations.
Require Import Autosubst.Autosubst.
From Metatheories Require Import ARS Term Reduction CBN Standardization CallByNeed CallByNeedContext VCANormal NeedNameCorrespond.

Local Hint Constructors clos_refl_trans clos_refl_trans_1n.

Lemma contextfree_sound_aux t t' :
  clos_refl_trans _ (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ (reduceI' t1 t1' \/ reduceVCA' t1 t1')) t t' ->
  clos_refl_trans _ red (expand_let t) (expand_let t').
Proof.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  induction Hrt as [ | ? ? ? [ ? [ ? [ ? [ Hevalctx [ ? [ ? [ HredI | HredVCA ]]]]]]]]; subst; eauto.
  - destruct (expand_let_reduceI _ _ (reduceI'_reduceI _ _ _ Hevalctx HredI)) as [ ? [ ] ]. eauto.
  - rewrite (expand_let_reduceVCA' _ _ _ Hevalctx HredVCA). eauto.
Qed.

Lemma contextfree_sound t t' :
  clos_refl_trans _ (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ (reduceI' t1 t1' \/ reduceVCA' t1 t1')) t t' ->
  answer t' ->
  exists t0, clos_refl_trans _ cbn (expand_let t) (tabs t0) /\ clos_refl_trans _ red (tabs t0) (expand_let t').
Proof.
  intros Hrt Hanswer.
  destruct (expand_let_answer _ Hanswer) as [ ? Heq ].
  apply contextfree_sound_aux in Hrt.
  rewrite Heq in Hrt.
  destruct (call_by_name_property _ _ Hrt) as [ ? [ ? Hrt' ] ].
  apply red_abs_multi in Hrt'.
  rewrite <- Heq in Hrt'.
  eauto.
Qed.

Lemma contextfree_normalize t0 :
  Acc (fun t3 t1 => exists t2, cbn t1 t2 /\ clos_refl_trans _ red t2 t3) t0 ->
  forall t, expand_let t = t0 ->
  exists t', clos_refl_trans _ (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ (reduceI' t1 t1' \/ reduceVCA' t1 t1')) t t'
    /\ in_normal_form _ (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ (reduceI' t1 t1' \/ reduceVCA' t1 t1')) t'.
Proof.
  induction 1 as [ ? ? IH ]. intros t ?. subst.
  induction t as [ ? IH' ] using (well_founded_induction reduceVCA'_well_founded).
  destruct (answer_or_stuck_or_reducible t) as [ | [ [ ] | [ [ ? HreduceVCA ] | [ ? Hred ] ] ] ]; eauto.
  - exists t. split; eauto.
    intros ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? | HredVCA ] ] ] ] ] ] ].
    + eapply answer_reduceI_disjoint; eauto.
      subst. eapply reduceI'_reduceI; eauto.
    + edestruct reduceVCA'_reduceVCA; eauto.
      subst. eapply answer_reduceVCA_disjoint; eauto.
  - exists t. split; eauto.
    intros ? [ ? [ ? [ ? [ ? [ ? [ ? [ ? | HredVCA ] ] ] ] ] ] ].
    + eapply needs_reduceI_disjoint; eauto.
      subst. eapply reduceI'_reduceI; eauto.
    + edestruct reduceVCA'_reduceVCA; eauto.
      subst. eapply needs_reduceVCA_disjoint; eauto.
  - destruct (reduceVCA_reduceVCA' _ _ HreduceVCA) as [ ? [ ? [ ? [ Hevalctx  [ ? HreduceVCA' ] ] ] ] ]. subst.
    edestruct IH' as [ ? [ ] ]; [ eauto 7 | | | ];
      try rewrite <- (expand_let_reduceVCA' _ _ _ Hevalctx HreduceVCA'); eauto 6.
    repeat eexists; try eassumption.
    eapply rt_trans.
    + apply rt_step. repeat eexists; eauto.
    + eauto.
  - destruct (IH _ (expand_let_reduceI _ _ Hred) _ eq_refl) as [ ? [ ] ].
    destruct (reduceI_reduceI' _ _ Hred) as [ ? [ ? [ ? [ ? [ ? [ ] ] ] ] ] ]. subst.
    repeat eexists; try eassumption.
    eapply rt_trans.
    + eapply rt_step. repeat eexists; eauto.
    + eauto.
Qed.

Theorem contextfree_complete t t0 :
  clos_refl_trans _ cbn (expand_let t) (tabs t0) ->
  exists t', clos_refl_trans _ (fun t t' => exists E t1 t1', evalctx E /\ t = fill_hole E t1 /\ t' = fill_hole E t1' /\ (reduceI' t1 t1' \/ reduceVCA' t1 t1')) t t' /\ answer t' /\ clos_refl_trans _ red (tabs t0) (expand_let t').
Proof.
  intros Hnormalizing.
  edestruct contextfree_normalize with (t := t) as [ t' [ Hrt Hnf ] ]; eauto.
  - apply quasi_cbn_theorem'.
    eapply normalizing_and_deterministic_impl_terminating; eauto.
    + intros ? ? ? ?. apply cbn_det; eauto.
    + inversion 1.
  - destruct (answer_or_stuck_or_reducible t') as [ Hanswer | [ [ ? Hneeds ] | [ [ ? HreduceVCA ] | [ ? Hred ] ] ] ].
    + destruct (contextfree_sound _ _ Hrt Hanswer) as [ ? [ Hnormalizing' ] ].
      destruct (cbn_confluent _ _ _ Hnormalizing Hnormalizing') as [ ? [ Hrefl Hrefl' ] ].
      destruct (strip_lemma _ _ _ _ Hrefl) as [ | [ ? [ Hcontra ]] ]; [ subst | inversion Hcontra ].
      destruct (strip_lemma _ _ _ _ Hrefl') as [ Heq | [ ? [Hcontra ] ] ]; [ rewrite Heq in * | inversion Hcontra ].  eauto.
    + apply contextfree_sound_aux in Hrt.
      destruct (red_confluent _ _ _ (cbn_multi_impl_red_multi _ _ Hnormalizing) Hrt) as [ ? [ Hrt' Hrt'' ] ].
      destruct (red_abs_multi_inv _ _ Hrt' _ eq_refl) as [? [ ] ]. subst.
      specialize (needsn_preserved_by_red_multi _ _ _ Hrt'' (expand_let_needs _ _ Hneeds)).
      inversion 1.
    + edestruct reduceVCA_reduceVCA' as [ ? [ ? [ ? [ ? [ ] ] ] ] ]; eauto. subst.
      edestruct Hnf; simpl; eauto 8.
    + edestruct reduceI_reduceI' as [ ? [ ? [ ? [ ? [ ? [ ] ] ] ] ] ]; eauto. subst.
      edestruct Hnf; simpl; eauto 8.
Qed.