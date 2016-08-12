Set Implicit Arguments.

Require Export Arith.
Require Export List.

(** * Decidable [In] Predicate *)

Class EqDec (A : Type) :=
  { 
    dec : forall (a b : A), {a = b} + {a <> b}
  }.

Global Generalizable Variables A.

Delimit Scope Dec_scope with Dec.

Infix "==" := dec (at level 70, no associativity) : Dec_scope.

Open Scope Dec_scope.

Ltac case_var :=
  let ldestr a b := destruct (a == b); [try subst a | idtac] in
  match goal with
  | |- context [?a == ?b]      => ldestr a b
  | H: context [?a == ?b] |- _ => ldestr a b
  end.

Ltac case_dec decA :=
  match goal with
    | |- context [decA ?a ?b]       => destruct (decA a b)
    | _ : context [decA ?a ?b] |- _ => destruct (decA a b)
  end.

Notation " a @ l " := (In a l) (at level 70).
Notation " a # l " := (~ In a l) (at level 70).

(** Tactics for destructing the decidable equality between naturals numbers. *)

(** A specified tactic for uninteresting cases *)

Ltac neq_case :=
  match goal with
    | H : ?x <> ?y |- _ =>
      right; red; intro Heq; inversion Heq; congruence
  end.

(** Decidability of being-in-a-list *)

Lemma dec_In `{D : EqDec A} (a : A) (l : list A) : 
  {a @ l} + {a # l}.
Proof.
  auto using in_dec, dec.
Defined.

Notation "a <-? l" := (dec_In a l) (at level 70).

Ltac case_In :=
  match goal with
    | |- context [?a <-? ?l]       => destruct (a <-? l)
    | H : context [?a <-? ?l] |- _ => destruct (a <-? l)
  end.

(** Uniqueness of proofs of being-in-a-list

 This does not hold with the original definition of [In].
 Hence we borrow the power of ProofIrrelevance Axiom. *)

Require Import ProofIrrelevance.

Lemma In_proof_uniq `{a : A} {l : list A} (p q : In a l) :
  p = q.
Proof.
  apply proof_irrelevance.
Defined.

Hint Resolve In_dec In_proof_uniq : datatypes.

(** Extra properties of [In] including the following

List.in_eq
List.in_cons
 *)

Lemma neq_In_cons `{l : list A} {a b : A} :
  a <> b ->
  b @ (a::l) -> b @ l.
Proof.
  simpl; intros; intuition congruence.
Qed.

Hint Resolve neq_In_cons : datatypes.

Lemma In_rm_1 `{D : EqDec A} {a b : A} {l : list A} :
  a @ (remove dec b l) ->
  a @ l.
Proof.
  induction l; simpl; intros; auto.
  repeat case_var; firstorder.
Qed.

Lemma In_rm_2 `{D : EqDec A} {a b : A} {l : list A} :
  a <> b ->
  a @ l ->
  a @ (remove dec b l).
Proof.
  induction l; simpl; intros; auto.
  case_var; solve [intuition congruence | firstorder].
Qed.

Lemma In_rm_neq `{D : EqDec A} {a b : A} {l : list A} :
  a @ (remove dec b l) ->
  a <> b.
Proof.
  induction l; simpl; intros; auto.
  case_var; simpl in *; intuition congruence.
Qed.

Hint Resolve In_rm_1 In_rm_2 In_rm_neq : datatypes.

Lemma In_appL `(a : A) (l m: list A) :
  a @ l ->
  a @ (l ++ m).
Proof.
  intros; apply in_or_app; left; assumption.
Qed.

Lemma In_appR `(a : A) (l m: list A) :
  a @ m ->
  a @ (l ++ m).
Proof.
  intros; apply in_or_app; right; assumption.
Qed.

Hint Resolve In_appL In_appR : datatypes.

Lemma notIn_rm_1 `{D : EqDec A} (a : A) (l: list A) :
  a # (remove dec a l).
Proof.
  induction l; simpl; intros; intuition.
  case_var; intuition firstorder.
Qed.

Lemma notIn_rm_2 `{D : EqDec A} (a b : A) (l: list A) :
  a <> b ->
  a # (remove dec b l) ->
  a # l.
Proof.
  firstorder using notIn_rm_1.
Qed.

Hint Resolve notIn_rm_1 notIn_rm_2 : datatypes.

Lemma notIn_app_1 `(a : A) (l m: list A) :
  a # (l ++ m) ->
  a # l /\ a # m.
Proof.
  firstorder with datatypes.
Qed.

Lemma notIn_app_2 `(a : A) (l m: list A) :
  a # l ->
  a # m ->
  a # (l ++ m).
Proof.
  intros ? ? Hnot; elim (in_app_or _ _ _ Hnot); auto. 
Qed.

Lemma notIn_app_3 `(a : A) (l m: list A) :
  a # (l ++ m) -> a # l.
Proof.
  intros H. elim (notIn_app_1  _ _ _ H); tauto.
Qed.

Lemma notIn_app_4 `(a : A) (l m: list A) :
  a # (l ++ m) -> a # m.
Proof.
  intros H. elim (notIn_app_1  _ _ _ H); tauto.
Qed.

Lemma notIn_cons_1 `(a : A) (b : A) (l : list A) :
  a # (b :: l) -> a <> b.
Proof.
  intuition; subst; auto with datatypes.
Qed.

Lemma notIn_cons_2 `(a : A) (b : A) (l : list A) :
  a # (b :: l) ->
  a # l.
Proof.
  intuition; subst; auto with datatypes. 
Qed.

Hint Resolve notIn_app_1 notIn_app_2 notIn_app_3 notIn_app_4 : datatypes.
Hint Resolve in_cons notIn_cons_1 notIn_cons_2 : datatypes.

Lemma notIn_cons_3 `(a : A) (b : A) (l : list A) :
  a <> b ->
  b # l ->
  b # (a :: l).
Proof.
  firstorder.
Qed.

Lemma notIn_singleton_1 `(a : A) (b : A) : 
  a <> b ->
  b # (a :: nil).
Proof.
  firstorder. 
Qed.

Lemma notIn_empty_1 `(a : A) : 
  a # nil.
Proof.
  firstorder.
Qed.

Lemma rm_cons `{D : EqDec A} (a b : A) (l: list A) :
  a <> b ->
  b :: remove dec a l = remove dec a (b :: l).
Proof.
  intros; simpl; destruct (dec a b); congruence.
Qed.

Hint Resolve notIn_cons_3 notIn_singleton_1 notIn_empty_1 rm_cons: datatypes.

Lemma rm_app `{D : EqDec A} (a : A) (l m : list A) :
  (remove dec a l) ++ (remove dec a m) = (remove dec a (l ++ m)).
Proof.
  induction l; auto; simpl; intros.
  case_var; simpl; congruence.
Qed. 

Lemma rm_rm_eq_rm `{D : EqDec A} (a : A) (l : list A) :
  remove dec a (remove dec a l) = (remove dec a l).
Proof.
  induction l; auto; simpl; intros. 
  case_var; subst; auto. 
  rewrite <- rm_cons; congruence.
Qed.

Hint Resolve rm_app rm_rm_eq_rm : datatypes.

Lemma rm_neq_eq `{D : EqDec A} (a b : A) (l : list A) :
  remove dec a (remove dec b l) =  remove dec b (remove dec a l).
Proof. 
  induction l; auto; simpl; intros.
  repeat (case_var; subst; simpl); intuition congruence.
Qed.

Hint Resolve rm_neq_eq : datatypes.

