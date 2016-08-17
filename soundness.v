(** * Soundness of LJT w.r.t. Kripke Semantics *)

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

(** The soundness of [LJT] with respect to Kripke semantics
   is relatively simple.

   If we had included parameters (free variables), the soundness
   proof of [LJT] would be a simple simultaneous induction
   on the derivation, cf. with_FreeVar_soundness.v.

   However, because we use constants instead, the case
   [ProofForallR] requires more attention. *) 

(** ** Some auxiliary predicates and operations *)

(** A predicate checking that a property holds for all elements
   of a list. *)

Inductive list_forall (A:Type)(P:A -> Type) : list A -> Type :=
| ForallNil  : list_forall P nil
| ForallCons : forall a l, 
               P a -> list_forall P l -> list_forall P (cons a l).

Definition force_ctx K (w:worlds K) eta Ga :=
  list_forall (fun B : (formula nil) => w ||- B [eta]) Ga.

Lemma force_In_ctx : forall K (w:worlds K) eta Ga,
  force_ctx K w eta Ga ->
  forall A,
    A @ Ga ->
    w ||- A [eta].
Proof.
  induction 1 as [ | B]; simpl; intros A; [ intro Hnil; elim Hnil | intro Hcons ].
  destruct (fml_dec A B); subst; auto. 
  apply IHX; auto with datatypes. intuition; contradict n; auto.
 Qed.

Lemma list_force_assoc_equiv : forall Ga K (w:worlds K) eta eta0,
  list_forall (fun B : (formula nil) => w ||- B [eta]) Ga ->
  list_forall (fun B : (formula nil) => w ||- B [eta0]) Ga.
Proof.
  induction 1;
    [ constructor
      | apply ForallCons;
        [apply force_assoc_equiv with eta; auto; solve_assoc
          | assumption
        ]
    ].
Qed.

(** Forcing is monotone wrt. the world relation. *)

Lemma mono_force_ctx : forall K (w w':worlds K),
  w <= w' -> 
  forall eta (Ga:context), 
    force_ctx K w eta Ga ->
    force_ctx K w' eta Ga.
Proof.
  induction 2 as [| B]; constructor; eauto using mono_force.
Qed.

(** ** Creation of a new Kripke model *)

Section Creation_new_Kripke.

(** This section reflects the fact that fresh constants are
   as good as fresh parameters.

   - Syntactically, this fact is represented by the renaming lemma.

   - At the semantic level, this corresponds to creating a new Kripke
     model from a given one such that the semantics remains
     nearly identical.

   - The following section is not necessary when we had introduced
     parameters. *)

  Variable K : Kripke.

(** Given an arbitrary association for constants, we construct
   a new Kripke model which differs only for a specific constant. *)

  Definition Kripke_new_csts (f : name -> domain K) : Kripke
    := @Build_Kripke (worlds K) (wle K) (wle_refl K) (wle_trans K)
    (domain K) f (funs K) (atoms K) (atoms_mon K).

(** [csts_up] creates a new association for constants using a specific
   value for a specific contant. *)

  Definition csts_up (f:name -> domain K) (n:name) (d:domain K) :
    name -> domain K
    := (fun m => if (eq_name m n) then d else f m).

(** If [c] is a fresh constant for a class of formulae, then
   the new Kripke model has the same interpretation as before
   w.r.t. the class.

   For technical reason, we need to exclude the case [c=0],
   Note its special role in the definition of forcing. *)

  Lemma fresh_csts_psem : forall m (t:term m) (c:name) (eta:assoc (domain K)),
    c # (oc_t t) ->
    sub_name (ov_t t) (dom eta) ->
    forall (d:domain K),
      psem K t eta = psem (Kripke_new_csts (csts_up (csts K) c d)) t eta.
  Proof.
    unfold csts_up; induction t; simpl; intros.
    - apply incl_cons_0 in H0.
      apply lookup_exists in H0; inversion H0 as [d' Hd'].
      rewrite Hd' in *; auto.
    - repeat case_name; intuition.
    - f_equal; [rewrite <-  IHt1 | rewrite <- IHt2]; auto with datatypes.
  Qed.

  Lemma fresh_csts_forceL : forall m (A:formula m) (c:name) (eta:assoc (domain K)),
    c # oc_f A ->
    sub_name (ov_f A) (dom eta) ->
    forall (w:worlds K) (d:domain K),
      force K w A eta ->
      force (Kripke_new_csts (csts_up (csts K) c d)) w A eta

    with fresh_csts_forceR : forall m (A:formula m) (c:name) (eta:assoc (domain K)),
      c # oc_f A ->
      sub_name (ov_f A) (dom eta) ->
      forall (w:worlds K) (d:domain K),
        force (Kripke_new_csts (csts_up (csts K) c d)) w A eta ->
        force K w A eta.
  Proof.
    - destruct A as [ [p t] | | ]; simpl; intros.
      + rewrite <- fresh_csts_psem; assumption. 
      + apply fresh_csts_forceL; auto with datatypes. 
        apply X; auto.
        apply fresh_csts_forceR with (c:=c) (d:=d); auto with datatypes.
      + assert (sub_name (ov_f A) (dom ((x,d0)::eta))).
        * apply incl_rm_2; auto.
        * apply fresh_csts_forceL; auto. 
    - destruct A as [ [p t] | | ]; simpl; intros.
      + rewrite <- fresh_csts_psem in X; assumption.
      + generalize (incl_appL H0); intro.
        generalize (incl_appR H0); intro.
        apply fresh_csts_forceR with (c:=c) (d:=d); auto with datatypes.
        apply X; auto. 
        apply fresh_csts_forceL; auto with datatypes.
      + assert (sub_name (ov_f A) (dom ((x, d0)::eta))).
        * apply incl_rm_2; auto.
        * apply fresh_csts_forceR with (c:=c) (d:=d0); eauto.
  Qed.

  Lemma fresh_csts_force_ctx : forall (Ga:context) (c:name),
    c # oc_c Ga ->
    forall (w:worlds K) (eta:assoc (domain K)) (d:domain K),
      force_ctx K w eta Ga ->
      force_ctx (Kripke_new_csts (csts_up (csts K) c d)) w eta Ga.
  Proof.
    induction Ga as [ | A]; simpl; intros;
      [ apply ForallNil
        | destruct_notIn; inversion X; apply ForallCons;
          [ apply fresh_csts_forceL
            | apply IHGa ]; auto ].
  Qed.

End Creation_new_Kripke.

(** ** Soundness *)

Theorem soundness : forall Ga A,
  Ga |- A ->
    forall K (w:worlds K),
      list_forall (fun B => w ||- B [nil]) Ga ->
      w ||- A [nil]

with soundness_stoup : forall Ga A C,
  Ga ;; A |- C ->
    forall K (w:worlds K),
      list_forall (fun B => w ||- B [nil]) Ga ->
      w ||- A [nil]
      -> w ||- C [nil].
Proof.
  (* soundness*)
  destruct 1; simpl; intros;
    [ apply soundness_stoup with (Ga:=Ga)(A:=A);
      eauto using force_In_ctx
      | apply soundness with (Ga:= B::Ga); auto;
        apply ForallCons; auto;
          apply mono_force_ctx with (w:=w); assumption
      | apply force_assoc_equiv with ((y,d)::nil);
        [ solve_assoc
          | simpl in n; destruct_notIn;
            apply fresh_csts_forceR with (c:=a)(d:=d); auto;
              set (K' := Kripke_new_csts K (csts_up K (csts K) a d));
                assert (d = psem K' (@Cst nil a) nil);
                  [ simpl; unfold csts_up; simpl; case_name; intuition congruence
                    | rewrite H2;
                      apply subst_force with (K:=K')(l:=nil); simpl; auto;
                        apply soundness with (K:=K')(Ga:=Ga); auto;
                          apply fresh_csts_force_ctx; auto;
                            apply mono_force_ctx with (w:=w); auto;
                              apply list_force_assoc_equiv with (eta:=eta); auto
                  ]
        ]
    ].

  (* soundness_stoup *)
  destruct 1; simpl; intros;
    [ assumption
      | apply soundness_stoup with (Ga:=Ga)(A:=C); auto;
        apply X0;
          [ apply wle_refl
            | apply soundness with Ga; auto
          ]
      | 
    ].

  apply soundness_stoup with
    (Ga := Ga) (A := [nil ! (y,u) :: nil] B); auto.
      change (w ||- [ (nil \ y) ! (y, u) :: nil] B [nil]).
        apply force_assoc_equiv with nil.
        + solve_assoc.
        + apply force_subst; auto;
              apply force_assoc_equiv with (eta:= (y, psem K u nil) :: nil).
          * unfold assoc_equiv; intros; simpl in *; case_name; auto.
          * apply force_assoc_equiv with ((y, psem K u nil) :: nil);
            [ solve_assoc
            | apply X0; apply wle_refl
            ].
Qed.

