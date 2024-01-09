Inductive bool3 : Type :=
  | TRUE
  | FALSE
  | IDK.

Definition and3 (v1 v2 : bool3) :=
  match v1, v2 with
  | FALSE, _ => FALSE
  | _, FALSE => FALSE
  | TRUE, TRUE => TRUE
  | _, _ => IDK
  end.

Definition or3 (v1 v2 : bool3) :=
  match v1, v2 with
  | TRUE, _ => TRUE
  | _, TRUE => TRUE
  | FALSE, FALSE => FALSE
  | _, _ => IDK
  end.

Definition not3 (v : bool3) :=
  match v with
  | TRUE => FALSE
  | FALSE => TRUE
  | IDK => IDK
  end.

Inductive bexpr : Type :=
  | Cst (v : bool3)
  | Var (n : nat)
  | And (b1 b2 : bexpr)
  | Or (b1 b2 : bexpr)
  | Not (b : bexpr).

Definition of_bool (b : bool) :=
  if b then TRUE else FALSE.

Fixpoint eval (env : nat -> bool) (b : bexpr) :=
  match b with
  | Cst v => v
  | Var n => of_bool (env n)
  | And b1 b2 => and3 (eval env b1) (eval env b2)
  | Or b1 b2 => or3 (eval env b1) (eval env b2)
  | Not b => not3 (eval env b)
  end.

Lemma and3_IDK:
  forall v1 v2,
    and3 v1 v2 = IDK ->
    (v1 = IDK /\ v2 = TRUE) \/
    (v1 = TRUE /\ v2 = IDK) \/
    (v1 = IDK /\ v2 = IDK).
Proof.
  intros [] []; simpl; intuition.
Qed.

Lemma or3_IDK:
  forall v1 v2,
    or3 v1 v2 = IDK ->
    (v1 = IDK /\ v2 = FALSE) \/
    (v1 = FALSE /\ v2 = IDK) \/
    (v1 = IDK /\ v2 = IDK).
Proof.
  intros [] []; simpl; intuition.
Qed.