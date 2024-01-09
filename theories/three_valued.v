From Coq Require Import Bool.


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

Inductive mode :=
  | BAD
  | GOOD.

(** "good/bad" semantics *)
Fixpoint good_bad (m : mode) (env : nat -> bool) (b : bexpr) :=
  match b with
  | Cst IDK => false
  | Cst TRUE =>
    match m with
    | BAD => false
    | GOOD => true
    end
  | Cst FALSE =>
    match m with
    | BAD => true
    | GOOD => false
    end
  | Var n =>
    match m with
    | BAD => negb (env n)
    | GOOD => env n
    end
  | And b1 b2 =>
    match m with
    | BAD => orb (good_bad BAD env b1) (good_bad BAD env b2)
    | GOOD => andb (good_bad GOOD env b1) (good_bad GOOD env b2)
    end
  | Or b1 b2 =>
    match m with
    | BAD => andb (good_bad BAD env b1) (good_bad BAD env b2)
    | GOOD => orb (good_bad GOOD env b1) (good_bad GOOD env b2)
    end
  | Not b =>
    match m with
    | BAD => good_bad GOOD env b
    | GOOD => good_bad BAD env b
    end
  end.

Lemma good_bad_sound:
  forall env b,
    (good_bad BAD env b = true -> eval env b = FALSE) /\
    (good_bad GOOD env b = true -> eval env b = TRUE).
Proof.
  intros env.
  induction b; simpl.
  - now destruct v.
  - now destruct (env n).
  - split.
  + intros [->%(proj1 IHb1) | ->%(proj1 IHb2)]%orb_true_iff; try easy.
    now destruct (eval env b1).
  + now intros [->%(proj2 IHb1) ->%(proj2 IHb2)]%andb_true_iff.
  - split.
  + now intros [->%(proj1 IHb1) ->%(proj1 IHb2)]%andb_true_iff.
  + intros [->%(proj2 IHb1) | ->%(proj2 IHb2)]%orb_true_iff; try easy.
    now destruct (eval env b1).
  - split.
  + now intros ->%IHb.
  + now intros ->%IHb.
Qed.

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

Lemma IDK_good_bad_false:
  forall env b,
    eval env b = IDK -> forall m, good_bad m env b = false.
Proof.
  intros env b Hb.
  induction b; intros m; simpl in *.
  - now destruct v.
  - now destruct (env n), m.
  - apply and3_IDK in Hb as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  + destruct m.
  * rewrite IHb1; auto.
    destruct (good_bad BAD env b2) eqn:Heq; try easy.
    apply good_bad_sound in Heq.
    now rewrite Heq in H2.
  * rewrite IHb1; auto.
  + destruct m.
  * rewrite IHb2; auto.
    destruct (good_bad BAD env b1) eqn:Heq; try easy.
    apply good_bad_sound in Heq.
    now rewrite Heq in H1.
  * rewrite IHb2; auto.
    now destruct (good_bad GOOD env b1).
  + destruct m.
  * now rewrite IHb1, IHb2.
  * now rewrite IHb1, IHb2.
  - apply or3_IDK in Hb as [[H1 H2] | [[H1 H2] | [H1 H2]]].
  + destruct m.
  * now rewrite IHb1.
  * rewrite IHb1; auto.
    destruct (good_bad GOOD env b2) eqn:Heq; try easy.
    apply good_bad_sound in Heq.
    now rewrite Heq in H2.
  + destruct m.
  * rewrite IHb2; auto.
    now destruct (good_bad BAD env b1) eqn:Heq.
  * rewrite IHb2; auto.
    destruct (good_bad GOOD env b1) eqn:Heq; try easy.
    apply good_bad_sound in Heq.
    now rewrite Heq in H1.
  + destruct m.
  * rewrite IHb1, IHb2; auto.
  * rewrite IHb1, IHb2; auto.
  - destruct m.
  + destruct (eval env b); try easy.
    now apply IHb.
  + destruct (eval env b); try easy.
    now apply IHb.
Qed.

Lemma good_bad_complete:
  forall env b,
    (eval env b = TRUE -> good_bad GOOD env b = true) /\
    (eval env b = FALSE -> good_bad BAD env b = true).
Proof.
  intros env b.
  induction b; simpl; split.
  - now intros ->.
  - now intros ->.
  - now destruct (env n).
  - now destruct (env n).
  - intros H.
    destruct (eval env b1), (eval env b2); try easy.
    now rewrite (proj1 IHb1), (proj1 IHb2).
  - intros H.
    destruct (eval env b1), (eval env b2); intuition.
  - intros H.
    destruct (eval env b1), (eval env b2); intuition.
  - intros H.
    destruct (eval env b1), (eval env b2); try easy; intuition.
  - intros H.
    destruct (eval env b); try easy; intuition.
  - intros H.
    destruct (eval env b); try easy; intuition.
Qed.

Definition good_bad_eval (env : nat -> bool) (b : bexpr) :=
  if good_bad BAD env b then FALSE
  else if good_bad GOOD env b then TRUE
  else IDK.

Lemma good_bad_encoding :
  forall env b, good_bad_eval env b = eval env b.
Proof.
  intros. unfold good_bad_eval.
  pose proof (good_bad_sound env b) as [H1 H2].
  destruct (good_bad BAD env b) eqn:Hb1; intuition.
  destruct (good_bad GOOD env b) eqn:Hb2; intuition.
  clear H1 H2.
  pose proof (good_bad_complete env b) as [H1 H2].
  destruct (eval env b) eqn:Hb3; auto.
  now rewrite H1 in Hb2.
  now rewrite H2 in Hb1.
Qed.
