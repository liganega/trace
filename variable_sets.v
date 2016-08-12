(** * Variable Sets *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.

(** Subcontext relation *)

Notation sub_ctx := incl.

(** Being-in-a-context relation *)

(** Relation between context and contants *)

Lemma In_oc_sub (A:formula nil) (Ga:context) :
  A @ Ga ->
  sub_name (oc_f A) (oc_c Ga).
Proof.
  unfold sublist; induction Ga as [ | B]; simpl; intros; auto.
  destruct H; subst; auto with datatypes. 
Qed.

Implicit Arguments In_oc_sub [A Ga].

Lemma sub_ctx_oc : forall (Ga De:context),
  sub_ctx Ga De -> sub_name (oc_c Ga) (oc_c De).
Proof.
  unfold sublist; intros; induction Ga as [ | A]; simpl in * ; intros; intuition.
  apply in_app_or in H0; destruct H0; auto with datatypes.
  generalize (H A); intros.
  apply In_oc_sub in H1; auto. 
Qed.

Hint Resolve In_oc_sub sub_ctx_oc.

(** Relation between variables and traces

 - Traces contain free occurrences of variables in pseudo-terms and -formulae.

 - Well-defined terms or formulas have no local variables. *)

Lemma sub_ov_term : forall m (t:term m),
  sub_name (ov_t t) m.
Proof.
  unfold sublist; induction t; simpl; intros; try case_var; intuition; subst; auto. 
  apply in_app_or in H; destruct H; auto with datatypes.
Qed.

Lemma sub_ov_fml : forall m (A:formula m),
  sub_name (ov_f A) m.
Proof.
  unfold sublist; induction A as [ m [p t] | |]; simpl; intros.

  apply sub_ov_term with t; assumption.

  apply in_app_or in H; destruct H; auto.

  apply (@neq_In_cons _ m x a); auto with datatypes.
  - apply (@In_rm_neq name (name_Dec)) in H; auto.  
  - apply IHA; auto with datatypes; apply (@In_rm_1 name (name_Dec)) in H; auto.
Qed.

Hint Resolve sub_ov_term sub_ov_fml.

Lemma term_ov_nil_1 : forall (t: term nil),
  ov_t t = nil.
Proof.
  intro t; apply incl_nil; auto.  
Qed.

Hint Rewrite -> term_ov_nil_1 : bv.

Lemma term_ov_nil_2 : forall (t:term nil)(x:name),
  x # (ov_t t).
Proof.
intros; rewrite term_ov_nil_1; firstorder. 
Qed.

Lemma term_sub : forall (t:term nil) m,
  sub_name (ov_t t) m.
Proof.
intros.
exact (eq_rect_r (fun l => incl l m) (nil_incl m) (term_ov_nil_1 t)).
Qed.

Hint Resolve term_ov_nil_1 term_ov_nil_2 term_sub.

Lemma fml_ov_nil_1 : forall (A:formula nil),
  ov_f A = nil.
Proof.
intro A; eapply incl_nil; eauto.
Qed.

Hint Rewrite -> fml_ov_nil_1 : bv.

Lemma fml_ov_nil_2 : forall (A:formula nil) m,
  sub_name (ov_f A) m.
Proof.
intros; rewrite fml_ov_nil_1; apply nil_incl.
Qed.

Lemma fml_ov_nil_3 : forall (A:formula nil)(x:name),
  x # (ov_f A).
Proof.
intros; rewrite fml_ov_nil_1; firstorder. 
Qed.

Hint Resolve fml_ov_nil_1 fml_ov_nil_2 fml_ov_nil_3.

(** inversion properties for variable sets:

   - These properties are used in the definition of substitution. *)

Lemma sub_ov_funL : forall (f:function) m (t0 t1: term m) l,
  sub_name (ov_t (App f t0 t1)) l ->
  sub_name (ov_t t0) l.
Proof.
simpl; intros; eauto 2 with datatypes.
Qed.

Lemma sub_ov_funR : forall (f:function) m (t0 t1: term m) l,
  sub_name (ov_t (App f t0 t1)) l ->
  sub_name (ov_t t1) l.
Proof.
simpl; intros; eauto 2 with datatypes.
Qed.

Hint Resolve sub_ov_funL sub_ov_funR.

Lemma In_inv_atom : forall (p:predicate) m l (t: term m),
  sub_name (ov_f (Atom (p,t))) l ->
  sub_name (ov_t t) l.
Proof.
intros; auto. 
Qed.

Lemma In_inv_impL : forall m l (B C: formula m),
  sub_name (ov_f (B --> C)) l ->
  sub_name (ov_f B) l.
Proof.
  simpl; intros; eauto 2 with datatypes.
Qed.

Lemma In_inv_impR : forall m l (B C: formula m),
  sub_name (ov_f (B --> C)) l ->
  sub_name (ov_f C) l.
Proof.
  simpl; intros; eauto 2 with datatypes.
Qed.

Lemma In_inv_all : forall m l x (B:formula (x::m)),
  sub_name (ov_f (@Forall m x B)) l ->
  sub_name (@ov_f (x::m) B) (x::l).
Proof.
  simpl; intros. apply (@incl_rm_2 name (name_Dec)); auto.
Qed.

Hint Resolve In_inv_atom In_inv_impL In_inv_impR In_inv_all.

