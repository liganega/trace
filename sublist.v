(** * Sublist Relation  *)

Set Implicit Arguments.

Require Export List.
Require Export decidable_In.

(** Lists are considered as sets.

   - [List.incl] relation behaves like subset relation.

   - A list [l] is a sublist of another list [k]
     if [l] is a subset of [k] when they are regarded as sets. *)

Hint Unfold incl.

(** [incl] and empty list *)

Lemma nil_incl {A} (l: list A) :
  incl nil l. 
Proof.
  red; simpl; intuition.
Qed.

Lemma incl_nil {A} {l:list A} : 
  incl l nil -> l = nil.
Proof.
  unfold incl; intros H.
  induction l as [ | a]; simpl in *; auto. 
  elim (H a); auto. 
Qed.

Hint Resolve nil_incl incl_nil : datatypes.

(** [incl] and [cons] *)

Lemma incl_cons_0 {A} {l m: list A} {a : A} :
    incl (a :: l) m ->
    a @ m.
Proof.
  intro H; unfold incl in *. 
  auto with datatypes. 
Qed.

Lemma incl_cons_1 {A} {l m: list A}{a : A} :
  incl (a :: l) m ->
  incl l m.
Proof.
  intros; auto with datatypes.
Qed.

Lemma incl_cons_2 {A} (a:A) (l:list A) :
  incl l (a::l).
Proof.
  unfold incl; simpl; auto. 
Qed. 

Lemma incl_cons_3 {A} {l m: list A} (a:A) : 
  incl l m ->
  incl (a::l) (a::m).
Proof.
  unfold incl; simpl; firstorder.
Qed.

Hint Resolve incl_cons_1 incl_cons_2 incl_cons_3 : datatypes.

(** [incl] and [app] *)

Lemma incl_appL {A} {l m n: list A} :
  incl (l ++ m) n ->
  incl l n.
Proof.
  unfold incl; intros; eauto with datatypes.
Qed.

Lemma incl_appR {A} {l m n: list A} :
  incl (l ++ m) n ->
  incl m n.
Proof.
  unfold incl; intros; eauto with datatypes.
Qed.

Hint Resolve incl_appL incl_appR : datatypes.

(** [incl] and [remove] *)

Lemma rm_incl_1 `{D :EqDec A} (a : A) (l : list A) :
  incl (remove dec a l) l.
Proof.
  unfold incl; induction l as [| ]; simpl; intros; auto.
  repeat case_var; simpl in *; intuition. 
Qed.

Lemma rm_incl_2 `{D :EqDec A} (a : A) (l : list A) :
  incl (remove dec a (a::l)) l.
Proof.
  simpl; intros; case_var; 
  [ auto using rm_incl_1 | intuition ].
Qed.

Hint Resolve rm_incl_1 rm_incl_2 : datatypes.

Lemma incl_rm_1 `{D :EqDec A} (l m : list A) (a : A) :
  incl l m ->
  incl (remove dec a l) (remove dec a m).
Proof.
  intro; unfold incl.
  induction l as [| v l']; simpl in *; intros; intuition.
  case_var; subst; intuition.
  simpl in *; firstorder.
  subst. apply In_rm_2; firstorder.
Qed.

Lemma incl_rm_2 `{D :EqDec A} (l m : list A) (a : A) :
  incl (remove dec a m) l ->
  incl m (a :: l).
Proof.
  unfold incl; simpl; intros.
  case (a == a0); auto with datatypes.
Qed.

Lemma incl_rm_3 `{D :EqDec A} (l m : list A) (a : A) :
  incl l (a :: m) ->
  incl (remove dec a l) m.
Proof.
  intros; apply @incl_tran with (m:= remove dec a (a::m)).
  - apply incl_rm_1; assumption.
  - auto with datatypes. 
Qed.

Lemma incl_rm_4 `{D :EqDec A} (l m : list A) (a b : A) :
  incl l m ->
  a = b ->
  incl (b :: l) (b :: remove dec a m).
Proof.
  unfold incl; simpl; intros.
  case (a0 == a); intros; subst; firstorder. 
Qed.

Hint Resolve incl_rm_1 incl_rm_2 incl_rm_3 incl_rm_4 : datatypes.

Lemma In_singleton {A} (n m : A) :
  n @ (m :: nil) -> n = m.
Proof.
  simpl; intuition congruence.
Qed.

Lemma In_incl {A} (l : list A) (n : A) :
  incl (n :: nil) l <-> n @ l.
Proof.
  split. 
  - apply @incl_cons_0 with (l:=nil); auto. 
  - intro. unfold incl; simpl; intros. 
    intuition congruence.
Qed.


