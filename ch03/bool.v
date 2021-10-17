Inductive term : Type :=
| ttrue : term
| tfalse : term
| tif : term -> term -> term -> term.

Inductive eval : term -> term -> Prop :=
| E_IfTrue : forall (t2 t3: term), eval (tif ttrue t2 t3) t2
| E_IfFalse : forall (t2 t3: term), eval (tif tfalse t2 t3) t3
| E_If : forall (t1 t1' t2 t3: term), eval t1 t1' -> eval (tif t1 t2 t3) (tif t1' t2 t3).

Notation "t1 --> t2" := (eval t1 t2) (at level 60).

Example s := tif ttrue tfalse tfalse.

Lemma one_step_s : eval s tfalse.
Proof.
  apply E_IfTrue.
Qed.

Theorem determinancy_of_one_step : forall t t' t'', (t --> t') -> (t --> t'') -> t' = t''.
Proof.
  intros.
  generalize dependent t''.
  induction H; intros; inversion H0; subst.
  - reflexivity.
  - inversion H4.
  - reflexivity.
  - inversion H4.
  - inversion H.
  - inversion H.
  - apply IHeval in H5.
    rewrite H5.
    reflexivity.
Qed.

Inductive value : term -> Prop :=
| vtrue : value ttrue
| vfalse : value tfalse.

Definition normal_form (t: term): Prop :=
  ~ exists t', t --> t'.

Theorem value_is_normal_form : forall t, value t -> normal_form t.
Proof.
  intros.
  unfold normal_form.
  unfold not.
  induction H; intros; inversion H; inversion H0.
Qed.

Proposition PNNP: forall p: Prop, p -> ~ ~p.
Proof.
  unfold not.
  now intros p H notH.
Qed.

Theorem tif_is_not_normal : forall t0 t1 t2, ~ (normal_form (tif t0 t1 t2)).
Proof.
  unfold normal_form.
  intros.
  apply PNNP.
  generalize dependent t2.
  generalize dependent t1.
  induction t0.
  - intros.
    exists t1.
    constructor.
  - intros.
    exists t2.
    constructor.
  - intros.
    specialize IHt0_1 with t0_2 t0_3.
    destruct IHt0_1.
    exists (tif x t1 t2).
    constructor.
    assumption.
Qed.

Theorem normal_form_is_value : forall t, normal_form t -> value t.
Proof.
  intros.
  destruct t; try constructor.
  absurd (normal_form (tif t1 t2 t3)).
  - apply tif_is_not_normal.
  - assumption.
Qed.

Inductive multi_eval : term -> term -> Prop :=
| M_Eval : forall t1 t2, eval t1 t2 -> multi_eval t1 t2
| M_Refl : forall t1, multi_eval t1 t1
| M_Trans : forall t1 t2 t3, multi_eval t1 t2 -> multi_eval t2 t3 -> multi_eval t1 t3.

Notation "t1 -->* t2" := (multi_eval t1 t2) (at level 60).

Lemma one_step_is_multistep : forall t0 t1, t0 --> t1 -> t0 -->* t1.
Proof.
  intros.
  now constructor.
Qed.

Inductive multi_eval' : term -> term -> Prop :=
| M_Eval' : forall t1 t2, eval t1 t2 -> multi_eval' t1 t2
| M_Refl' : forall t1, multi_eval' t1 t1
| M_Trans' : forall t1 t2 t3, eval t1 t2 -> multi_eval' t2 t3 -> multi_eval' t1 t3.

Notation "t1 ->->* t2" := (multi_eval' t1 t2) (at level 60).

Lemma multi_eval'_transitive : forall t1 t2 t3, multi_eval' t1 t2 -> multi_eval' t2 t3 -> multi_eval' t1 t3.
Proof.
  intros.
  induction H.
  - apply M_Trans' with (t1 := t1) in H0. assumption. assumption.
  - assumption.
  - apply IHmulti_eval' in H0.
    apply M_Trans' with (t1 := t1) in H0.
    + assumption.
    + assumption.
Qed.

Lemma multi_eval_iff_multi_eval' : forall t1 t2, t1 ->->* t2 <-> t1 -->* t2.
Proof.
  intros.
  split.
  - intros.
    induction H.
    + now apply M_Eval in H.
    + constructor; constructor.
    + apply M_Eval in H.
      apply M_Trans with (t1 := t1) in IHmulti_eval'.
      * assumption.
      * assumption.
  - intros.
    induction H; subst.
    + now apply M_Eval' in H.
    + constructor; constructor.
    + apply multi_eval'_transitive with (t2 := t2).
      * assumption.
      * assumption.
Qed.


Theorem muti_eval_uniqueness_of_normal_form : forall t u u', t -->* u -> t -->* u' -> normal_form u -> normal_form u' -> u = u'.
Proof.
  intros.
  apply multi_eval_iff_multi_eval' in H.
  apply multi_eval_iff_multi_eval' in H0.
  induction H.
  - induction H0.
    + now apply determinancy_of_one_step with (t := t1) (t' := t2) (t'' := t0).
    + destruct H2. now exists t2.
    + induction H3.
      * apply IHmulti_eval'.
        apply determinancy_of_one_step with (t' := t2) in H0.
        rewrite <- H0 in H3.
        destruct H1.
        exists t3.
        assumption.
        assumption.
        assumption.
      * apply determinancy_of_one_step with (t' := t0) in H.
        symmetry. assumption. assumption.
      * apply determinancy_of_one_step with (t' := t0) in H.
        rewrite <- H in H1.
        destruct H1.
        exists t3.
        assumption.
        assumption.
  - induction H0.
    + destruct H1.
      now exists t2.
    + reflexivity.
    + destruct H1.
      now exists t2.
  - induction H0.
    + apply determinancy_of_one_step with (t' := t2) in H0.
      * rewrite H0 in IHmulti_eval'. destruct IHmulti_eval'.
        apply M_Refl'. assumption. reflexivity.
      * assumption.
    + destruct H2.
      now exists t2.
    + apply determinancy_of_one_step with (t' := t2) in H0.
      * rewrite H0 in IHmulti_eval'. destruct IHmulti_eval'. assumption. assumption. reflexivity.
      * assumption.
Qed.

Lemma meval_if : forall t1 t1' t2 t3, t1 -->* t1' -> tif t1 t2 t3 -->* tif t1' t2 t3.
Proof.
intros.
induction H.
- constructor.
  constructor.
  assumption.
- apply M_Refl.
- apply M_Trans with (t2 := tif t0 t2 t3).
  * assumption.
  * assumption.
Qed.

Theorem termination_of_evaluation : forall t, exists t', (normal_form t' /\ t -->* t').
Proof.
  intros.
  induction t.
  - exists ttrue. split.
    * apply value_is_normal_form. constructor.
    * apply M_Refl.
  - exists tfalse. split.
    * apply value_is_normal_form. constructor.
    * apply M_Refl.
  - destruct IHt1 as [v1 [IH1n IH1e]].
    apply normal_form_is_value in IH1n.
    inversion IH1n; subst.
    * destruct IHt2 as [v2 [IH2n IH2e]].
      exists v2. constructor. assumption.
      assert (tif t1 t2 t3 -->* tif ttrue t2 t3). {
        apply meval_if. assumption.
      }
      assert (tif ttrue t2 t3 -->* t2). {
        constructor.
        constructor.
      }
      assert (tif t1 t2 t3 -->* t2). {
        apply M_Trans with (t2 := tif ttrue t2 t3).
        - assumption.
        - assumption.
      }
      apply M_Trans with (t2 := t2).
      + assumption.
      + assumption.
    * destruct IHt3 as [v3 [IH3n IH3e]].
      exists v3; constructor.
      assumption.
      assert (tif t1 t2 t3 -->* tif tfalse t2 t3). {
        apply meval_if. assumption.
      }
      assert (tif tfalse t2 t3 -->* t3). {
        constructor.
        constructor.
      }
      assert (tif t1 t2 t3 -->* t3). {
        apply M_Trans with (t2 := tif tfalse t2 t3).
        - assumption.
        - assumption.
      }
      apply M_Trans with (t2 := t3).
      assumption.
      assumption.
Qed.
