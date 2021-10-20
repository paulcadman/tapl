Set Implicit Arguments.
Require Import Arith.
Require Import Wf_nat.
Require Import List.
Import ListNotations.

Section var.
  Variable var : Set.

  Inductive term : Set :=
  | tvar : var -> term
  | tapp : term -> term -> term
  | tabs : (var -> term) -> term.

  (* Inductive value : term -> Prop := *)
  (* | vabs : forall (x: var -> term), value (tabs x). *)

  (* Inductive eval : term -> term -> Prop := *)
  (* | E_App1 : forall (t1 t1' t2: term), eval t1 t1' -> eval (tapp t1 t2) (tapp t1' t2) *)
  (* | E_App2 : forall (v1 t2 t2': term), value v1 -> eval t2 t2' -> eval (tapp v1 t2) (tapp v1 t2'). *)
End var.

Definition Exp := forall var, term var.

Example identity : Exp := fun _ => tabs (fun x => tvar x).
Example self_app : Exp := fun _ => tabs (fun x => tapp (tvar x) (tvar x)).

Fixpoint size (t: term unit): nat :=
  match t with
  | tvar _ => 1
  | tapp t1 t2 => 1 + (size t1) + (size t2)
  | tabs t' => 1 + size (t' tt)
  end.

Definition Size (t: Exp) := size (t unit).

Eval compute in Size identity.
Eval compute in Size self_app.

Fixpoint depth (t: term unit): nat :=
  match t with
  | tvar _ => 1
  | tapp t1 t2 => 1 + (list_max [(depth t1); (depth t2)])
  | tabs t' => 1 + depth (t' tt)
  end.

Definition Depth (t: Exp) := depth (t unit).

Eval compute in Depth identity.
Eval compute in Depth self_app.

Section flatten.
  Variable var: Set.

  Fixpoint flatten (t : term (term var)) : term var :=
    match t with
    | tvar t' => t'
    | tapp t1 t2 => tapp (flatten t1) (flatten t2)
    | tabs t1 => tabs (fun x => flatten (t1 (tvar x)))
  end.

End flatten.

Definition Exp1 := forall var : Set, var -> term var.
Definition Subst (E: Exp1) (E' : Exp): Exp := fun var => flatten (E (term var) (E' var)).

Example ident1 : Exp1 := fun _ X => tvar X.

Example free_var : Exp1 := fun _ x => tabs (fun y => tvar x).
Example expr : Exp := fun _ => tabs (fun x => tvar x).

Eval compute in Subst free_var expr.
