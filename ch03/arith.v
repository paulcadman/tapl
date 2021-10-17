Require Import Wf_nat.
Require Import List.
Import ListNotations.

Inductive term : Type :=
| tzero : term
| ttrue : term
| tfalse : term
| tsucc : term -> term
| tpred : term -> term
| tiszero : term -> term
| tif : term -> term -> term -> term.

Inductive boolean_value : term -> Prop :=
| vtrue : boolean_value ttrue
| vfalse : boolean_value tfalse.

Inductive numeric_value : term -> Prop :=
| vzero : numeric_value tzero
| vsucc : forall (t : term), numeric_value t -> numeric_value (tsucc t).

Definition value t := boolean_value t \/ numeric_value t.

Lemma numeric_value_is_value : forall t, numeric_value t -> value t.
Proof.
  intros.
  now right.
Qed.

Inductive eval : term -> term -> Prop :=
| E_IfTrue : forall (t2 t3: term), eval (tif ttrue t2 t3) t2
| E_IfFalse : forall (t2 t3: term), eval (tif tfalse t2 t3) t3
| E_If : forall (t1 t1' t2 t3: term), eval t1 t1' -> eval (tif t1 t2 t3) (tif t1' t2 t3)
| E_Succ : forall (t1 t1': term), eval t1 t1' -> eval (tsucc t1) (tsucc t1')
| E_PredZero : eval (tpred tzero) tzero
| E_PredSucc : forall (t: term), numeric_value t -> eval (tpred (tsucc t)) t
| E_Pred : forall (t1 t1': term), eval t1 t1' -> eval (tpred t1) (tpred t1')
| E_IsZeroZero : forall (t: term), eval (tiszero tzero) ttrue
| E_IsZeroSucc : forall (t: term), numeric_value t -> eval (tiszero (tsucc t)) tfalse
| E_IsZero : forall (t1 t1': term), eval t1 t1' -> eval (tiszero t1) (tiszero t1') .

Notation "t1 --> t2" := (eval t1 t2) (at level 60).

Example s := tif ttrue tfalse tfalse.

Lemma one_step_s : eval s tfalse.
Proof.
  apply E_IfTrue.
Qed.

Definition normal_form (t: term): Prop := ~ exists t', t --> t'.

Theorem boolean_value_is_normal_form : forall t, boolean_value t -> normal_form t.
Proof.
  intros.
  unfold normal_form.
  unfold not.
  induction H; intros; inversion H; inversion H0.
Qed.

Theorem numeric_value_is_normal_form : forall t, numeric_value t -> normal_form t.
Proof.
  intros.
  unfold normal_form.
  unfold not.
  induction H; intros.
  - inversion H. inversion H0.
  - destruct H0.
    destruct IHnumeric_value.
    inversion H0.
    subst.
    now exists t1'.
Qed.

Theorem value_is_normal_form : forall t, value t -> normal_form t.
Proof.
  intros.
  destruct H.
  - now apply boolean_value_is_normal_form.
  - now apply numeric_value_is_normal_form.
Qed.


Theorem determinancy_of_one_step : forall t t' t'', (t --> t') -> (t --> t'') -> t' = t''.
Proof.
  intros.
  generalize dependent t''.
  induction H; intros; inversion H0; subst; try (now reflexivity || now inversion H).

  - inversion H4.

  - inversion H4.

  - apply IHeval in H5.
    now rewrite H5.

  - apply IHeval in H2.
    now rewrite H2.

  - inversion H1.

  - apply vsucc in H.
    apply numeric_value_is_normal_form in H.
    destruct H.
    now exists t1'.

  - apply vsucc in H2.
    apply numeric_value_is_normal_form in H2.
    destruct H2.
    now exists t1'.

  - apply IHeval in H2.
    now rewrite H2.

  - inversion H1.

  - apply vsucc in H.
    apply numeric_value_is_normal_form in H.
    destruct H.
    now exists t1'.

  - apply vsucc in H2.
    apply numeric_value_is_normal_form in H2.
    destruct H2.
    now exists t1'.

  - apply IHeval in H2.
    now rewrite H2.
Qed.

Fixpoint size (t : term): nat :=
  match t with
    ttrue => 1
  | tfalse => 1
  | tzero => 1
  | tsucc t1 => (size t1) + 1
  | tpred t1 => (size t1) + 1
  | tiszero t1 => (size t1) + 1
  | (tif t1 t2 t3) => (size t1) + (size t2) + (size t3) + 1
  end.

Fixpoint depth (t : term): nat :=
  match t with
    ttrue => 1
  | tfalse => 1
  | tzero => 1
  | tsucc t1 => (depth t1) + 1
  | tpred t1 => (depth t1) + 1
  | tiszero t1 => (depth t1) + 1
  | (tif t1 t2 t3) =>  (list_max [(depth t1); (depth t2); (depth t3)]) + 1
  end.

Theorem induction_on_depth (P : term -> Prop) :
  (forall s, (forall r, depth r < depth s -> P r) -> P s) -> forall s, P s.
Proof.
  (* Definition ltof (a b:A) := f a < f b.
      https://coq.inria.fr/library/Coq.Arith.Wf_nat.html#b:4
      https://github.com/coq/coq/blob/eb745e1d2bd511e7f7e5db54468e9a3c7ecc2247/theories/Arith/Wf_nat.v#L66
   *)
  Check ltof.
  Check induction_ltof1.
  exact (induction_ltof1 term depth P).
Qed.

Theorem induction_on_size (P : term -> Prop) :
  (forall s, (forall r, size r < size s -> P r) -> P s) -> forall s, P s.
Proof.
  exact (induction_ltof1 term size P).
Qed.

Definition structural_induction := term_ind.

Inductive big_eval : term -> term -> Prop :=
| B_Value : forall t, value t -> big_eval t t
| B_IfTrue : forall t1 t2 t3 v2,
value v2 -> big_eval t1 ttrue -> big_eval t2 v2 -> big_eval (tif t1 t2 t3) v2
| B_IfFalse : forall t1 t2 t3 v3,
value v3 -> big_eval t1 tfalse -> big_eval t3 v3 -> big_eval (tif t1 t2 t3) v3
| B_Succ : forall t1 nv1,
numeric_value nv1 -> big_eval t1 nv1 -> big_eval (tsucc t1) (tsucc nv1)
| B_PredZero : forall t1,
big_eval t1 tzero -> big_eval (tpred t1) tzero
| B_PredSucc : forall t1 nv1,
numeric_value nv1 -> big_eval t1 (tsucc nv1) -> big_eval (tpred t1) nv1
| B_IsZeroZero : forall t1,
big_eval t1 tzero -> big_eval (tiszero t1) ttrue
| B_IsZeroSucc : forall t1 nv1,
numeric_value nv1 -> big_eval t1 (tsucc nv1) -> big_eval (tiszero t1) (tfalse).

Notation "t ==> v" := (big_eval t v) (at level 60).

Theorem eval_value_is_big_eval : forall t v, value v -> t --> v -> t ==> v.
Proof.
intros.
induction H0.
- apply B_IfTrue.
  * assumption.
  * apply B_Value.
    constructor.
    constructor.
  * now apply B_Value.
- apply B_IfFalse.
  * assumption.
  * apply B_Value.
    constructor.
    constructor.
  * now apply B_Value.
- inversion H; inversion H1.
- apply B_Succ. inversion H. inversion H1; subst. now inversion H1.
  destruct H. inversion H. inversion H. apply IHeval. now apply numeric_value_is_value in H2.
- apply B_PredZero. apply B_Value. right. apply vzero.
- apply B_PredSucc.
  * assumption.
  * apply B_Succ.
    + assumption.
    + now apply B_Value.
- destruct H; inversion H.
- apply B_IsZeroZero. apply B_Value. right. apply vzero.
- apply B_IsZeroSucc with (nv1 := t).
  * assumption.
  * apply B_Succ.
    + assumption.
    + apply B_Value.
      now right.
- destruct H; inversion H.
Qed.
