From Coq Require Import Bool.
From ThreeValued Require Import bool3.

(** GOOD/BAD encoding of 3 valued logic in boolean logic *)

Inductive mode :=
  | BAD
  | GOOD.

(** "good/bad" semantics.
    The intuition is that "good" means "must be true" and "bad" means "must be false"
*)
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

(**
  If the "good" semantics returns true, then the 3 value semantis returns false
  If the "bad" semantics returns true, then the 3 value semantis returns true
*)
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

Lemma IDK_good_bad_false:
  forall env b,
    eval env b = IDK -> forall m, good_bad m env b = false.
Proof.
  intros env b Hb.
  pose proof (H := good_bad_encoding env b).
  unfold good_bad_eval in H.
  rewrite Hb in H. clear Hb.
  destruct (good_bad BAD env b) eqn:Heq1; try easy.
  destruct (good_bad GOOD env b) eqn:Heq2; try easy.
  now intros [].
Qed.
