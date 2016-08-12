(** * Completeness of [LJT] w.r.t. Kripke Semantics *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import environments.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution.
Require Import fresh_csts.
Require Import relocation.  
Require Import LJT_and_weakening.
Require Import kripke_semantics.
Require Import soundness.

(** The completeness of [LJT] w.r.t. Kripke semantics follows
   from the Universal Completeness.

   The universal Kripke model consists of contexts as worlds,
   the sub-context relation, and the provability for atomic
   sentences, and term as the constant domain. *)

(** ** The Universal Model *)

(** Monotonicity of forcing relation *)

Lemma weakening_atom : forall Ga Ga',
  sub_ctx Ga Ga' ->
  forall (P : predicate * (term nil)),
    Ga |- Atom P ->
    Ga' |- Atom P.
Proof.
  intros Ga Ga' h1 P h2; exact (weakening h1 h2).
Qed.

(** Reflexivity of sub-context relation. *)

Lemma sub_ctx_refl : forall (Ga : context), sub_ctx Ga Ga.
Proof.
  apply incl_refl.
Qed.

(** Transitivity of sub-context relation. *)

Lemma sub_ctx_trans : forall (Ga Ga0 Ga1 : context), 
  sub_ctx Ga Ga0 -> sub_ctx Ga0 Ga1 -> sub_ctx Ga Ga1.
Proof.
  unfold sublist; intros Ga Ga0 Ga1 H H0 a H1.
  apply H0; apply H; exact H1.
Qed.

(** Universal model's domain is the set of well-formed terms. *)

Canonical Structure Universal := @Build_Kripke
  context
  (@sub_ctx (formula nil))
  sub_ctx_refl
  sub_ctx_trans
  (term nil)
  (@Cst nil)
  (@App nil)
  (fun Ga P => Ga |- Atom P)
  weakening_atom.

(** In the universal model, substitution plays the role of
   semantic interpretation. *)

Lemma psem_tsubst : forall m (t:term m) (eta:assoc (term nil)),
  psem Universal t eta = [[nil ! eta]] t.
Proof.
  induction t; simpl; intros; auto;
  [ case_Env
  | f_equal ]
  ; auto.
Qed.

(** ** Universal Completeness *)

Theorem univ_cpltness : forall m (A:formula m) (Ga:context) (eta:assoc (term nil)),
  Ga ||- A [eta] ->
  Ga |- [nil ! eta] A

with univ_cpltness_stoup : forall m (A:formula m) (Ga:context) (eta:assoc (term nil)),
    (forall C Ga', sub_ctx Ga Ga' -> Ga' ;; [nil ! eta] A |- C -> Ga' |- C) ->
    Ga ||- A [eta].
Proof.
  destruct A as [ [p t] | | ]; simpl; intros.

  rewrite <- psem_tsubst; assumption.

  apply ProofImplyR.
  apply univ_cpltness; auto.
  apply X; auto using incl_cons_2.
  apply univ_cpltness_stoup; intros; auto.
  apply ProofCont with (A:= [nil ! eta] A1); auto using in_eq.

  set (a:= new (oc_c (Forall x ([x :: nil ! eta]A) :: Ga))).
  apply ProofForallR with (a:=a); intros.
  apply new_fresh.
  rewrite substitution; apply univ_cpltness; auto using sub_ctx_refl.

  destruct A as [ [p t] | |]; simpl; intros.
  
  apply H; auto using sub_ctx_refl.
  rewrite psem_tsubst; auto using ProofAxiom.

  apply univ_cpltness_stoup; intros; auto.
  apply H; eauto using sub_ctx_trans.
  apply ProofImplyL; eauto using univ_cpltness, mono_force.
  
  apply univ_cpltness_stoup; intros; auto.
  apply H; eauto using sub_ctx_trans.
  apply ProofForallL with (u:=d).
  rewrite substitution; auto.
Qed.

(** ** Completeness for _closed_ formulae *)

(** Remark:

   - Because we don't consider parameters, every term/formula are closed. *)

Theorem univ_cpltness' : forall (A: formula nil)(Ga:context),
  Ga ||- A [nil] ->
  Ga |- A.
Proof.
  intros.
  rewrite freloc_id with (h:=sub_ov_fml A).
  rewrite <- formula_subst with (eta:=nil).
  apply univ_cpltness; auto.
Qed.

Theorem univ_cpltness_stoup' : forall (A:formula nil)(Ga:context),
  (forall C Ga', sub_ctx Ga Ga' -> Ga' ;; A |- C -> Ga' |- C) ->
  Ga ||- A [nil].
Proof. 
  intros.
  rewrite freloc_id with (h:=sub_ov_fml A) in H.
  rewrite <- formula_subst with (eta:=nil) in H.
  apply univ_cpltness_stoup; auto.
Qed.

Lemma univ_cpltness_axiom : forall (Ga:context)(A:formula nil),
  A @ Ga ->
  Ga ||- A [nil].
Proof.
  induction Ga as [| B]; simpl; intros A H;
    [ elim H
      |  destruct (fml_dec A B); subst;
        [ apply univ_cpltness_stoup'; intros;
          eauto using ProofCont, in_eq
          | apply mono_force with Ga; 
            [ change (sub_ctx Ga (B::Ga)); apply incl_cons_2
              | apply IHGa; auto; intuition; contradict n; auto
            ]
        ]
    ].
Qed.  

Lemma universal_force_context : forall (Ga: worlds Universal) De,
  sub_ctx De Ga -> 
  list_forall (fun B => Ga ||- B [nil]) De.
Proof.
  induction De as [|A]; intros; constructor;
    [ apply univ_cpltness_axiom; auto using in_eq
      | apply IHDe; eauto using incl_cons_1;
        intros; auto using in_cons
    ].
Qed.

Theorem completeness : forall Ga A,
  (forall K (w: worlds K),
    (list_forall (fun B => w ||- B [nil]) Ga) -> w ||- A [nil]) ->
  Ga |- A.
Proof.
  intros; apply univ_cpltness';
  apply X; apply universal_force_context with (Ga:=Ga)(De:=Ga); auto.
Qed.

(** ** Cut-admissibility *)

Definition cut_ad Ga A B :
  Ga ;; A |- B -> Ga |- A -> Ga |- B :=
  fun p1 p2 =>
    completeness B 
    (fun K w H1 =>
      soundness_stoup p1 K w H1 (soundness p2 K w H1)).
