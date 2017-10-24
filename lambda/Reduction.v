Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import ARS Term.

Inductive red : relation term :=
  | red_appabs t11 t2 : red (tapp (tabs t11) t2) (t11.[t2/])
  | red_appl t1 t1' t2 :
      red t1 t1' ->
      red (tapp t1 t2) (tapp t1' t2)
  | red_appr t1 t2 t2' :
      red t2 t2' ->
      red (tapp t1 t2) (tapp t1 t2')
  | red_abs t t' :
      red t t' ->
      red (tabs t) (tabs t').
Hint Constructors red.
Local Hint Constructors clos_refl_trans clos_refl_sym_trans.

Lemma ered_appabs t11 t2 t :
  t = t11.[t2/] ->
  red (tapp (tabs t11) t2) t.
Proof. intros. subst. econstructor. Qed.

Lemma ered_appr t1 t2 t2' t' :
  red t2 t2' ->
  t' = tapp t1 t2' ->
  red (tapp t1 t2) t'.
Proof. intros. subst. eauto. Qed.

Lemma red_abs_multi t t' :
  clos_refl_trans _ red t t' ->
  clos_refl_trans _ red (tabs t) (tabs t').
Proof. induction 1; eauto. Qed.

Lemma red_appl_multi t1 t1' t2 :
  clos_refl_trans _ red t1 t1' ->
  clos_refl_trans _ red (tapp t1 t2) (tapp t1' t2).
Proof. induction 1; eauto. Qed.

Lemma red_appr_multi t1 t2 t2' :
  clos_refl_trans _ red t2 t2' ->
  clos_refl_trans _ red (tapp t1 t2) (tapp t1 t2').
Proof. induction 1; eauto. Qed.

Corollary red_app_multi t1 t2 t1' t2' :
  clos_refl_trans _ red t1 t1' ->
  clos_refl_trans _ red t2 t2' ->
  clos_refl_trans _ red (tapp t1 t2) (tapp t1' t2').
Proof.
  intros ? ?.
  eapply rt_trans with (y := tapp t1' t2).
  - apply red_appl_multi; eauto.
  - apply red_appr_multi; eauto.
Qed.

Lemma red_app_equiv t1 t1' t2 t2' :
  clos_refl_sym_trans _ red t1 t1' ->
  clos_refl_sym_trans _ red t2 t2' ->
  clos_refl_sym_trans _ red (tapp t1 t2) (tapp t1' t2').
Proof.
  intros Hrstc Hrstc'.
  apply rst_trans with (y := tapp t1' t2).
  - induction Hrstc; eauto.
  - induction Hrstc'; eauto.
Qed.

Hint Resolve red_abs_multi red_appl_multi red_appr_multi red_app_multi red_app_equiv.

Lemma red_abs_multi_inv t t' :
  clos_refl_trans _ red t t' ->
  forall t1, t = tabs t1 ->
  exists t1', t' = tabs t1' /\ clos_refl_trans _ red t1 t1'.
Proof.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  induction Hrt; intros ? ?; subst; eauto.
  - inversion H; subst.
    destruct (IHHrt _ eq_refl) as [? []]; eauto.
Qed.

Lemma red_rename t t' :
  red t t' ->
  forall r,
  red (rename r t) (rename r t').
Proof.
  induction 1; simpl; intros ?; eauto.
  - apply ered_appabs.
    autosubst.
Qed.

Lemma red_rename_multi r t t' :
  clos_refl_trans _ red t t' ->
  clos_refl_trans _ red (rename r t) (rename r t').
Proof.
  Local Hint Resolve red_rename.
  induction 1; simpl; eauto.
Qed.

Lemma red_subst t t' :
  red t t' ->
  forall s,
  red t.[s] t'.[s].
Proof.
  induction 1; simpl; intros ?; eauto.
  - apply ered_appabs.
    autosubst.
Qed.

Lemma red_subst_multi_aux t : forall s s',
  (forall x, clos_refl_trans _ red (s x) (s' x)) ->
  clos_refl_trans _ red t.[s] t.[s'].
Proof.
  induction t; simpl; eauto 6.
  - intros.
    apply red_abs_multi.
    apply IHt.
    intros [| ?].
    + apply rt_refl.
    + apply red_rename_multi. eauto.
Qed.

Lemma red_subst_multi t t' s s' :
  clos_refl_trans _ red t t' ->
  (forall x, clos_refl_trans _ red (s x) (s' x)) ->
  clos_refl_trans _ red t.[s] t'.[s'].
Proof.
  Local Hint Resolve red_subst.
  intros Hrt ?.
  eapply rt_trans.
  - apply red_subst_multi_aux. eauto.
  - apply clos_rt_rt1n in Hrt.
    induction Hrt; eauto.
Qed.
    
Section Confluence.
  Inductive pr : relation term :=
    | pr_appabs t11 t11' t2 t2' :
        pr t11 t11' ->
        pr t2 t2' ->
        pr (tapp (tabs t11) t2) (t11'.[t2'/])
    | pr_var x : pr (tvar x) (tvar x)
    | pr_app t1 t1' t2 t2' :
        pr t1 t1' ->
        pr t2 t2' ->
        pr (tapp t1 t2) (tapp t1' t2')
    | pr_abs t t' :
        pr t t' ->
        pr (tabs t) (tabs t').
  Local Hint Constructors pr.

  Lemma epr_appabs t11 t11' t2 t2' t' :
    pr t11 t11' ->
    pr t2 t2' ->
    t' = t11'.[t2'/] ->
    pr (tapp (tabs t11) t2) t'.
  Proof. intros. subst. eauto. Qed.
    
  Lemma pr_refl t : pr t t.
  Proof. induction t; eauto. Qed.
  Local Hint Resolve pr_refl.

  Lemma red_pr t t' : red t t' -> pr t t'.
  Proof. induction 1; eauto. Qed.
  Local Hint Resolve red_pr.

  Lemma pr_red_multi t t' : pr t t' -> clos_refl_trans _ red t t'.
  Proof. induction 1; eauto 7. Qed.
  Local Hint Resolve pr_red_multi.

  Lemma pr_multi_red_multi t t' : clos_refl_trans _ pr t t' -> clos_refl_trans _ red t t'.
  Proof.
    intros ?.
    apply clos_rt_idempotent.
    eapply clos_rt_impl.
    - apply pr_red_multi.
    - eauto.
  Qed.

  Lemma red_multi_pr_multi t t' : clos_refl_trans _ red t t' -> clos_refl_trans _ pr t t'.
  Proof. induction 1; eauto. Qed.

  Lemma pr_rename t t' :
    pr t t' ->
    forall r,
    pr (rename r t) (rename r t').
  Proof.
    induction 1; simpl; intros ?; eauto.
    - eapply epr_appabs; eauto.
      autosubst.
  Qed.

  Lemma pr_subst t t' :
    pr t t' ->
    forall s s',
    (forall x, pr (s x) (s' x)) ->
    pr t.[s] t'.[s'].
  Proof.
    induction 1; simpl; intros ? ? Hsub; eauto 6.
    - apply epr_appabs with (t11' := t11'.[up s']) (t2' := t2'.[s']); eauto.
      + apply IHpr1.
        intros [| ?].
        * apply pr_refl.
        * apply pr_rename. eauto.
      + autosubst.
    - constructor.
      apply IHpr.
      intros [| ?].
      + apply pr_refl.
      + apply pr_rename. eauto.
  Qed.
      
  Fixpoint development t :=
    match t with
    | tvar x => tvar x
    | tabs t1 => tabs (development t1)
    | tapp (tabs t11) t2 => (development t11).[development t2/]
    | tapp t1 t2 => tapp (development t1) (development t2)
    end.

  Lemma finite_development t t' :
    pr t t' ->
    pr t' (development t).
  Proof.
    induction 1; simpl; eauto.
    - apply pr_subst; eauto.
      intros [| ?].
      + apply IHpr2.
      + apply pr_refl.
    - destruct t1; simpl in *; eauto.
      inversion H; subst.
      inversion IHpr1; subst.
      eauto.
  Qed.

  Corollary pr_diamond : diamond_property _ pr.
  Proof.
    intros H H'.
    repeat eexists; apply finite_development; eauto.
  Qed.

  Definition pr_confluent := diamond_property_impl_confluent _ _ pr_diamond.

  Theorem red_confluent : confluent _ red.
  Proof.
    eapply confluent_same_relation.
    - apply pr_confluent.
    - intros.
      split.
      + apply pr_multi_red_multi.
      + apply red_multi_pr_multi.
  Qed.
End Confluence.
