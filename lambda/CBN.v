Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import ARS Term Reduction.

Inductive cbn : relation term :=
  | cbn_appabs t11 t2 : cbn (tapp (tabs t11) t2) (t11.[t2/])
  | cbn_app t1 t1' t2 :
      cbn t1 t1' ->
      cbn (tapp t1 t2) (tapp t1' t2).

Inductive stuck_in_var : var -> term -> Prop :=
  | stuck_in_var_here x : stuck_in_var x (tvar x)
  | stuck_in_var_app x t1 t2 :
      stuck_in_var x t1 ->
      stuck_in_var x (tapp t1 t2).

Hint Constructors cbn stuck_in_var.
Local Hint Constructors clos_refl_trans.

Lemma ecbn_appabs t11 t2 t' :
  t' = t11.[t2/] ->
  cbn (tapp (tabs t11) t2) t'.
Proof. intros. subst. eauto. Qed.

Lemma cbn_app_multi t1 t1' t2 :
  clos_refl_trans _ cbn t1 t1' ->
  clos_refl_trans _ cbn (tapp t1 t2) (tapp t1' t2).
Proof. induction 1; eauto. Qed.

Lemma cbn_abs_multi_inv t1 t' :
  clos_refl_trans _ cbn (tabs t1) t' ->
  t' = tabs t1.
Proof.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  inversion Hrt; subst; eauto.
  - inversion H.
Qed.

Lemma cbn_rename t t' r :
  cbn t t' ->
  cbn (rename r t) (rename r t').
Proof.
  induction 1; simpl; eauto.
  - apply ecbn_appabs.
    autosubst.
Qed.
Hint Resolve cbn_rename.

Lemma cbn_multi_rename t t' r :
  clos_refl_trans _ cbn t t' ->
  clos_refl_trans _ cbn (rename r t) (rename r t').
Proof. induction 1; eauto. Qed.
Hint Resolve cbn_multi_rename.

Lemma stuck_in_var_subst x y s t :
  stuck_in_var x t ->
  stuck_in_var y (s x) ->
  stuck_in_var y t.[s].
Proof. induction 1; simpl; eauto. Qed.

Lemma cbn_subst t t' s :
  cbn t t' ->
  cbn t.[s] t'.[s].
Proof.
  induction 1; simpl; eauto.
  - apply ecbn_appabs.
    autosubst.
Qed.
Hint Resolve cbn_subst.

Lemma cbn_subst' x s s' t t0 :
  (forall x, clos_refl_trans _ red (s x) (s' x)) ->
  cbn (s x) t0 ->
  clos_refl_trans _ red t0 (s' x) ->
  stuck_in_var x t ->
  exists t', cbn t.[s] t' /\ clos_refl_trans _ red t' t.[s'].
Proof.
  induction 4; simpl in *; eauto.
  destruct IHstuck_in_var as [? []]; auto.
  eexists.
  split; [eauto |].
  eapply rt_trans.
  - apply red_appl_multi.
    eassumption.
  - apply red_appr_multi.
    apply red_subst_multi; eauto.
Qed.

Lemma stuck_in_var_preserved_by_red x t :
  stuck_in_var x t ->
  forall t', red t t' ->
  stuck_in_var x t'.
Proof.
  induction 1; inversion 1; subst; eauto.
  inversion H.
Qed.

Lemma stuck_in_var_preserved_by_red_multi x t t' :
  clos_refl_trans _ red t t' ->
  stuck_in_var x t ->
  stuck_in_var x t'.
Proof.
  Local Hint Resolve stuck_in_var_preserved_by_red.
  intros Hrt.
  apply clos_rt_rt1n in Hrt.
  induction Hrt; eauto.
Qed.

Lemma cbn_multi_subst t1 t1' s :
  clos_refl_trans _ cbn t1 t1' ->
  clos_refl_trans _ cbn (t1.[s]) (t1'.[s]).
Proof. induction 1; eauto. Qed.
Hint Resolve cbn_multi_subst.

Lemma cbn_red t t' : cbn t t' -> red t t'.
Proof. induction 1; eauto. Qed.

Definition cbn_multi_impl_red_multi t t' Hrt := clos_rt_impl _ _ _ t t' cbn_red Hrt.
Hint Resolve cbn_red cbn_multi_impl_red_multi.

Lemma cbn_det : deterministic _ cbn.
Proof.
  intros ? ? z Hcbn.
  generalize dependent z.
  induction Hcbn; inversion 1; subst;
    try match goal with
    | H : cbn (tabs _) _ |- _ => inversion H
    end; f_equal; eauto.
Qed.

Definition cbn_confluent := deterministic_impl_confluent _ _ cbn_det.

Section CBNInternal.
  Inductive internal : relation term :=
  | internal_abs t t' :
      red t t' ->
      internal (tabs t) (tabs t')
  | internal_appl t1 t1' t2 :
      internal t1 t1' ->
      internal (tapp t1 t2) (tapp t1' t2)
  | internal_appr t1 t2 t2' :
      red t2 t2' ->
      internal (tapp t1 t2) (tapp t1 t2').
  Local Hint Constructors internal.

  Lemma internal_red t t' :
    internal t t' ->
    red t t'.
  Proof. induction 1; eauto. Qed.
  Hint Resolve internal_red.

  Lemma cbn_or_internal t t' :
    red t t' ->
    cbn t t' \/ internal t t'.
  Proof.
    induction 1; eauto.
    - destruct IHred; eauto.
  Qed.

  Lemma internal_swap t1 t2 :
    internal t1 t2 ->
    forall t3,
    cbn t2 t3 ->
    exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
  Proof.
    Local Hint Resolve red_subst.
    induction 1; inversion 1; subst.
    - inversion H; subst; eauto.
    - edestruct IHinternal as [? []]; eauto.
    - eexists.
      split; eauto.
      apply red_subst_multi; eauto.
      intros [| ?]; simpl; eauto.
    - eauto 7.
  Qed.

  Corollary red_swap t1 t2 :
    red t1 t2 ->
    forall t3,
    cbn t2 t3 ->
    exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
  Proof.
    intros Hred ? Hcbn.
    destruct (cbn_or_internal _ _ Hred); eauto 6.
    eapply internal_swap; eauto.
  Qed.

  Lemma red_multi_swap t1 t2 :
    clos_refl_trans _ red t1 t2 ->
    forall t3,
    cbn t2 t3 ->
    exists t2', cbn t1 t2' /\ clos_refl_trans _ red t2' t3.
  Proof.
    intros Hrt.
    apply clos_rt_rt1n in Hrt.
    induction Hrt; eauto.
    - intros ? ?.
      edestruct IHHrt as [? [? ?]]; eauto.
      edestruct red_swap as [? [? ?]]; eauto.
  Qed.

  Theorem quasi_cbn_theorem t :
    Acc (fun t2 t1 => cbn t1 t2) t ->
    Acc (fun t3 t1 => exists t2, clos_refl_trans _ red t1 t2 /\ cbn t2 t3) t.
  Proof.
    induction 1 as [t ? IH].
    constructor.
    intros ? [? [Hred Hcbn]].
    destruct (red_multi_swap _ _ Hred _ Hcbn) as [? [Hcbn']].
    destruct (IH _ Hcbn') as [IH'].
    constructor.
    intros ? [? [? ?]].
    eauto.
  Qed.

  Lemma quasi_cbn_theorem'_aux t :
    Acc (fun t3 t1 => exists t2, clos_refl_trans _ red t1 t2 /\ cbn t2 t3) t ->
    forall t', clos_refl_trans _ red t t' ->
    Acc (fun t3 t1 => exists t2, cbn t1 t2 /\ clos_refl_trans _ red t2 t3) t'.
  Proof.
    induction 1 as [? ? IH].
    intros ? ?.
    constructor.
    intros ? [? [? ?]].
    eauto.
  Qed.

  Corollary quasi_cbn_theorem' t :
    Acc (fun t2 t1 => cbn t1 t2) t ->
    Acc (fun t3 t1 => exists t2, cbn t1 t2 /\ clos_refl_trans _ red t2 t3) t.
  Proof.
    intros ?.
    eapply quasi_cbn_theorem'_aux.
    - apply quasi_cbn_theorem.
      eauto.
    - eauto.
  Qed.
End CBNInternal.
