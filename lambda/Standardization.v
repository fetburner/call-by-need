Require Import Autosubst.Autosubst.
Require Import Relations.
From Metatheories Require Import ARS Term Reduction CBN.

Inductive st : relation term :=
  | st_var t x :
      clos_refl_trans _ cbn t (tvar x) ->
      st t (tvar x)
  | st_app t t1 t2 t1' t2' :
      clos_refl_trans _ cbn t (tapp t1 t2) ->
      st t1 t1' ->
      st t2 t2' ->
      st t (tapp t1' t2')
  | st_abs t t1 t1' :
      clos_refl_trans _ cbn t (tabs t1) ->
      st t1 t1' ->
      st t (tabs t1').
Hint Constructors st.
Local Hint Constructors clos_refl_trans.

Lemma st_beta_multi t t' :
  st t t' ->
  clos_refl_trans _ red t t'.
Proof. induction 1; eauto. Qed.
Hint Resolve st_beta_multi.

Lemma st_refl t : st t t.
Proof. induction t; eauto. Qed.

Lemma st_abs_inv t1 t' :
  st (tabs t1) t' ->
  exists t1', t' = tabs t1'.
Proof.
  inversion 1; subst; eauto.
  - apply cbn_abs_multi_inv in H0.
    congruence.
  - apply cbn_abs_multi_inv in H0.
    congruence.
Qed.

Lemma cbn_multi_st_comp t1 t2 t3 :
  clos_refl_trans _ cbn t1 t2 ->
  st t2 t3 ->
  st t1 t3.
Proof. inversion 2; eauto. Qed.

Lemma st_rename t t' :
  st t t' ->
  forall r,
  st (rename r t) (rename r t').
Proof.
  induction 1; intros ?; simpl.
  - eapply cbn_multi_st_comp.
    + apply cbn_multi_rename.
      eassumption.
    + apply st_refl.
  - econstructor; eauto.
    apply (cbn_multi_rename _ _ _ H).
  - econstructor; eauto.
    apply (cbn_multi_rename _ _ _ H).
Qed.

Lemma st_subst t1 t1' :
  st t1 t1' ->
  forall s s',
  (forall x, st (s x) (s' x)) ->
  st (t1.[s]) (t1'.[s']).
Proof.
  induction 1; simpl; intros ? ? Hsub.
  - eapply cbn_multi_st_comp.
    + apply cbn_multi_subst.
      eassumption.
    + apply Hsub.
  - econstructor; eauto.
    apply (cbn_multi_subst _ _ _ H).
  - econstructor.
    + eapply (cbn_multi_subst _ _ _ H).
    + apply IHst.
      intros [| ?]; simpl.
      * apply st_refl.
      * apply st_rename.
        eauto.
Qed.

Lemma st_red_comp t2 t3 : red t2 t3 -> forall t1, st t1 t2 -> st t1 t3.
Proof.
  induction 1; intros ? Hst; inversion Hst; subst; eauto.
  - inversion H3; subst.
    eapply cbn_multi_st_comp.
    eapply rt_trans.
    + eassumption.
    + eapply rt_trans.
      * apply cbn_app_multi.
        eassumption.
      * apply rt_step.
        eauto.
    + apply st_subst.
      * eauto.
      * intros [| ?]; [ apply H4 | apply st_refl ].
Qed.
Hint Resolve st_red_comp.

Lemma beta_multi_st t t' :
  clos_refl_trans _ red t t' ->
  st t t'.
Proof.
  intros H.
  apply clos_rt_rtn1 in H.
  induction H; eauto.
  - apply st_refl.
Qed.


Theorem call_by_name_property t t1 :
  clos_refl_trans _ red t (tabs t1) ->
  exists t1', clos_refl_trans _ cbn t (tabs t1') /\ clos_refl_trans _ red t1' t1.
Proof.
  intros Hred.
  apply beta_multi_st in Hred.
  inversion Hred; subst.
  eauto.
Qed.
