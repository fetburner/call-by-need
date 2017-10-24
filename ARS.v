Require Import Relations.

Section ARS.
  Variable A : Type.
  Variable R : relation A.

  Definition in_normal_form x := forall y, ~R x y.
  Arguments in_normal_form x /.
  Definition normal_form_of x y :=
    clos_refl_trans _ R x y /\ in_normal_form y.
  Arguments normal_form_of x y /.
  Definition joinable x y :=
    exists z, clos_refl_trans _ R x z /\ clos_refl_trans _ R y z.
  Arguments joinable x y /.

  Definition Church_Rosser :=
    forall x y,
    clos_refl_sym_trans _ R x y ->
    joinable x y.
  Definition confluent :=
    forall x y1 y2,
    clos_refl_trans _ R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2.
  Definition semi_confluent :=
    forall x y1 y2,
    R x y1 ->
    clos_refl_trans _ R x y2 ->
    joinable y1 y2.
  Definition diamond_property :=
    forall x y y',
    R x y ->
    R x y' ->
    exists z,
    R y z /\ R y' z.
  Definition deterministic :=
    forall x y z,
    R x y ->
    R x z ->
    y = z.

  Local Hint Constructors clos_refl_trans.

  Theorem Church_Rosser_impl_confluent :
    Church_Rosser ->
    confluent.
  Proof.
    intros HCR ? y1 y2 Hrtc1 Hrtc2.
    assert (Hrstc : clos_refl_sym_trans _ R y1 y2).
    { apply clos_rt_clos_rst in Hrtc1.
      apply clos_rt_clos_rst in Hrtc2.
      apply rst_sym in Hrtc1.
      eapply rst_trans; eauto. }
    eauto.
  Qed.

  Corollary confluent_impl_semi_confluent :
    confluent ->
    semi_confluent.
  Proof.
    Hint Resolve rt_step.
    intros ? ? ? ? ? ?.
    eauto.
  Qed.

  Theorem semi_confluent_impl_Church_Rosser :
    semi_confluent ->
    Church_Rosser.
  Proof.
    intros Hsc ? ? Hrstc.
    apply clos_rst_rst1n_iff in Hrstc.
    induction Hrstc as [| ? ? ? [ | ] ? [? []]]; simpl; eauto.
    - edestruct Hsc as [? []]; eauto.
  Qed.

  Definition semi_confluent_impl_confluent H :=
    Church_Rosser_impl_confluent (semi_confluent_impl_Church_Rosser H).
  
  Definition confluent_impl_Church_Rosser H :=
    semi_confluent_impl_Church_Rosser (confluent_impl_semi_confluent H).

  Lemma diamond_property_impl_semi_confluent :
    diamond_property ->
    semi_confluent.
  Proof.
    intros Hdiamond ? y ? ? Hrtc.
    generalize dependent y.
    apply clos_rt_rt1n in Hrtc.
    induction Hrtc; simpl in *; eauto.
    - intros ? H'.
      destruct (Hdiamond _ _ _ H H') as [? [H'']].
      destruct (IHHrtc _ H'') as [? []]; eauto.
  Qed.

  Definition diamond_property_impl_confluent H :=
    semi_confluent_impl_confluent (diamond_property_impl_semi_confluent H).

  Lemma strip_lemma x z :
    clos_refl_trans _ R x z ->
    x = z \/ exists y, R x y /\ clos_refl_trans _ R y z.
  Proof.
    Local Hint Resolve clos_rt1n_rt.
    intros Hrt.
    apply clos_rt_rt1n in Hrt.
    inversion Hrt; subst; eauto.
  Qed.

  Corollary confluent_both_normal_form :
    confluent ->
    forall x y,
    clos_refl_sym_trans _ R x y ->
    in_normal_form x ->
    in_normal_form y ->
    x = y.
  Proof.
    intros Hc ? ? Hrstc Hnfx Hnfy.
    destruct (confluent_impl_Church_Rosser Hc _ _ Hrstc) as [? [Hrtx Hrty]].
    destruct (strip_lemma _ _ Hrtx) as [ | [? [Hrx]]].
    - subst.
      destruct (strip_lemma _ _ Hrty) as [ | [? [Hry]]].
      + subst.
        reflexivity.
      + destruct (Hnfy _ Hry).
    - destruct (Hnfx _ Hrx).
  Qed.

  Lemma deterministic_impl_semi_confluent :
    deterministic ->
    semi_confluent.
  Proof.
    intros Hdet ? ? ? HR Hrt.
    simpl.
    destruct (strip_lemma _ _ Hrt) as [|[? [HR']]].
    - subst. eauto.
    - rewrite (Hdet _ _ _ HR HR'). eauto.
  Qed.

  Definition deterministic_impl_confluent H :=
    semi_confluent_impl_confluent (deterministic_impl_semi_confluent H).

  Lemma normalizing_and_deterministic_impl_terminating x y :
    deterministic ->
    clos_refl_trans _ R x y ->
    in_normal_form y ->
    Acc (fun y x => R x y) x.
  Proof.
    intros Hdet Hrt Hnf.
    apply clos_rt_rt1n in Hrt.
    induction Hrt; constructor; intros ? HR.
    - destruct (Hnf _ HR).
    - rewrite (Hdet _ _ _ H HR) in *.
      eauto.
  Qed.
End ARS.

Lemma clos_rt_impl A (R R' : relation A) x y:
  (forall x y, R x y -> R' x y) ->
  clos_refl_trans _ R x y ->
  clos_refl_trans _ R' x y.
Proof.
  Local Hint Constructors clos_refl_trans.
  induction 2; eauto.
Qed.

Lemma confluent_same_relation A R R' :
  confluent A R ->
  (forall x y, clos_refl_trans _ R x y <-> clos_refl_trans _ R' x y) ->
  confluent A R'.
Proof.
  intros Hconfluent Hsame x y y' Hrtc1 Hrtc2.
  apply Hsame in Hrtc1.
  apply Hsame in Hrtc2.
  destruct (Hconfluent _ _ _ Hrtc1 Hrtc2) as [z []].
  exists z.
  split; apply Hsame; eauto.
Qed.

