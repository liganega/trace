(** * Fresh Constants *)

Set Implicit Arguments.

Require Import Coq.Arith.Max.

Require Import decidable_In.
Require Import sublist.
Require Import language_syntax.

(** Remember that [constants] play the role of [parameters].
   In particular, we will show that fresh constants are as good as
   fresh parameters. *)

(** [new] chooses a fresh one which does not belong to lists. *)

Definition new (l:list name) : name := S (fold_right max 0 l).

Lemma new_no_zero : forall (l:list name), new l <> 0.
Proof.
  unfold new; intros; auto with arith.
Qed.

Lemma In_less : forall (n:name)(l:list name),
  n @ l ->
  n < new l.
Proof.
  unfold new; induction l; simpl; intro H; [elim H | ]; destruct H; subst; auto with arith.
  apply lt_le_trans with (m:= S (fold_right max 0 l)); eauto 2 with arith.
Qed.

Lemma new_fresh : forall l : list name, (new l) # l.
Proof.
  intros l H.
  elim (lt_irrefl (new l)).
  apply In_less; exact H.  
Qed.

(** Freshness for a term *)

Lemma fresh_out_t : forall m (t: term m),
  (new (oc_t t)) # (oc_t t).
Proof.
  intros m t. 
  exact (new_fresh (oc_t t)).
Qed.

(** Freshness for a formula *)

Lemma fresh_out_f : forall m (A:formula m),
  (new (oc_f A)) # (oc_f A).
Proof.
  intros m A. 
  exact (new_fresh (oc_f A)).
Qed.

(** Choosing a fresh variable for a context *)

Definition fresh_out (Ga:context) : name := new (oc_c Ga).

(** Freshness for a context *)

Definition fresh (x:name)(Ga:context) : Prop :=
  x # (oc_c Ga).

Lemma fresh_out_spec : forall (Ga:context),
  fresh (fresh_out Ga) Ga.
Proof.
  unfold fresh; unfold fresh_out; intros Ga.
  exact (new_fresh (oc_c Ga)).
Qed.

Lemma fresh_fml_peel : forall a A Ga, 
  fresh a (A::Ga) ->
  a # (oc_f A).
Proof.
  unfold fresh; simpl; intros; auto with datatypes.
Qed.

Lemma fresh_peel : forall a A Ga,
  fresh a (A::Ga) ->
  fresh a Ga.
Proof.
  unfold fresh; simpl; intros; auto with datatypes.
Qed.
