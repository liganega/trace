(** Renaming of Constants *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import environments.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import fresh_csts.
Require Import variable_sets.
Require Import substitution.
Require Import relocation.

(** [McKinna & Pollak] and [Leroy] used [simultaneous] parameter swapping
   in order to show the equivalence between different styles of quantification.

   We will use simultaneous [renaming] of constants.
   Note that [renaming] is easier to deal with. *)

(** [renaming] is an arbitrary funtion from [Cst] to [Cst]. *)

Notation renaming := (assoc name).

Fixpoint rename_t (eta : renaming) m (t : term m) : term m := 
  match t with
    | Var y h    => Var y h
    | Cst c       => match eta ^^ c with
                       | Some d => Cst d
                       | None   => Cst c
                     end
    | App f t1 t2 => App f (rename_t eta t1)  (rename_t eta t2)
  end.

Fixpoint rename_f (eta : renaming) m (A : formula m) : formula m := 
  match A with
    | Atom (p,t) => Atom (p, rename_t eta t )
    | B --> C    => (rename_f eta B) --> (rename_f eta C)
    | Forall y B => Forall y (rename_f eta B)
  end.

Fixpoint rename_c (eta : renaming) (Ga : context) : context := 
  match Ga with
    | nil => nil
    | A :: Ga0 => rename_f eta A :: rename_c eta Ga0
  end.

(** Renaming associations *)

Fixpoint rename_a (eta : renaming) (rho : assoc (term nil)) :=
  match rho with
    | nil           => nil
    | (x,t) :: rho0 => (x, rename_t eta t) :: rename_a eta rho0
  end.

(** No renaming means no change  *)

Lemma rename_t_nil : forall m (t:term m),
  rename_t nil t = t.
Proof.
  induction t; simpl; f_equal; auto.
Qed.

Lemma rename_f_nil : forall m (A:formula m),
  rename_f nil A = A.
Proof.
  induction A as [m [p t]| |]; simpl; f_equal; auto.
  f_equal; auto using rename_t_nil.
Qed.

Lemma rename_c_nil : forall (Ga:context),
  rename_c nil Ga = Ga.
Proof.
  induction Ga; simpl; f_equal; auto using rename_f_nil.
Qed.

(** Compatibility of renaming with predicates and operators. *)

Lemma rename_In_ctx : forall A Ga eta,
  A @ Ga ->
  (rename_f eta A) @ (rename_c eta Ga).
Proof.
  induction Ga; simpl; intros; auto.
  destruct H; subst; auto.
Qed.

Lemma In_dom_sig_rename : forall (x: name) (rho: assoc (term nil))(eta:renaming) t,
  rho ^^ x = Some t ->
  (rename_a eta rho) ^^ x = Some (rename_t eta t).
Proof.
  induction rho as [ | [y b] ]; simpl; intros;
    [ discriminate
      | case_name; inversion H; subst; auto
    ].
Qed.

Lemma treloc_rename_t : forall m l (t:term m) eta
  (H: sub_name (ov_t t) l) (H0 : sub_name (ov_t (rename_t eta t)) l),
  rename_t eta (treloc t H) = treloc (rename_t eta t) H0.
Proof.
  induction t; simpl; intros;
  [ f_equal; apply In_proof_uniq
  | case_env; auto
  | f_equal; auto].
Qed.

(** Renaming and substitution *)

Lemma rename_tsubst : forall m (t:term m) (rho:assoc (term nil))(eta:renaming) l,
  sub_name m (l ++ dom rho) ->
  rename_t eta ([[l ! rho]] t) =
  [[l ! rename_a eta rho]] (rename_t eta t).
Proof.
  induction t; simpl; intros.
  - unfold incl in *; apply (@in_app_or name _ _ x) in H; auto. destruct H as [HL | HR]. 
    + case_In; simpl; intuition. 
    + case_In; auto. apply lookup_exists in HR; inversion HR. rewrite H.
      rewrite (In_dom_sig_rename x rho eta H); apply treloc_rename_t. 
  - case_Env; auto.
  - f_equal; auto.
Qed.

Lemma rename_subst : forall m (A:formula m) (rho:assoc (term nil))(eta:renaming) l,
  sub_name m (l ++ dom rho) ->
  rename_f eta ([l ! rho] A) =
  [l ! rename_a eta rho] (rename_f eta A).
Proof.
  induction A as [m [p t] | |]; simpl; intros;
    [ do 2 f_equal; apply rename_tsubst; auto
      | f_equal; auto
      | f_equal; apply IHA; unfold sublist; intros; simpl in *; destruct H0; auto
    ].
Qed.

(** ** Renaming and freshness *)

Lemma rename_t_fresh : forall m (t:term m) eta a a0,
  a # oc_t t ->
  rename_t ((a,a0) :: eta) t = rename_t eta t.
Proof.
  induction t; simpl; intros;
    [ reflexivity
      | repeat case_name; try congruence; elim H; auto
      | destruct_notIn; f_equal; auto
    ].
Qed.

Lemma rename_f_fresh : forall m (A:formula m) eta a a0,
  a # oc_f A ->
  rename_f ((a, a0) :: eta) A = rename_f eta A.
Proof.
  induction A as [m [p t] | | ]; simpl; intros;
    [ do 2 f_equal; apply rename_t_fresh
      | destruct_notIn; f_equal
      | f_equal
    ]; auto.
Qed.

Lemma rename_c_fresh : forall Ga eta a a0,
  a # oc_c Ga ->
  rename_c ((a, a0) :: eta) Ga = rename_c eta Ga.
Proof.
  induction Ga as [ | A Ga0]; simpl; intros; auto.
  destruct_notIn; f_equal; auto using rename_f_fresh.
Qed.

(** Function values and (co-)domain *)

Fixpoint image (eta : renaming) : list name :=
  match eta with
    | nil => nil
    | (_, a0) :: eta0 => a0 :: image eta0
  end.

Definition fun_value (eta : renaming) (a:name) : name :=
  match eta ^^ a with
    | Some a0 => a0
    | None   => a
  end.

Notation " eta ** a " := (fun_value eta a) (at level 60).

Lemma notIn_image : forall (eta:renaming) a a0 a1,
  a # image eta ->
  eta ^^ a0 = Some a1 ->
  a <> a1.
Proof.
  induction eta as [ |[x] ]; simpl; intros;
  repeat case_name; intuition try congruence; eauto.
Qed.

Lemma term_rename_fresh : forall m (t:term m) eta a a0,
  a0 # oc_t t ->
  a0 # dom eta ->
  a0 # image eta ->
  rename_t ((a0, eta ** a) :: eta) (rename_t ((a, a0) :: nil) t) = 
  rename_t eta t.
Proof.
  induction t; simpl; intros; destruct_notIn;
    [ reflexivity
      | repeat case_name; simpl; firstorder;
        [ rewrite (notIn_dom_None _ _ H0); simpl; 
          case_name; intuition; unfold fun_value;
            destruct (eta ^^ a); auto
          | case_eq (eta ^^ a); intros;
            [ assert (n <> a0);
              [ apply sym_not_eq; eauto using notIn_image
                | simpl; case_name; congruence
              ]
              | simpl; case_name; congruence
            ]
        ]
      | f_equal; auto].
Qed.

Lemma formula_rename_fresh : forall m (A:formula m) eta a a0,
  a0 # oc_f A ->
  a0 # dom eta ->
  a0 # image eta ->
  rename_f ((a0, eta ** a) :: eta) (rename_f ((a, a0) :: nil) A) = 
  rename_f eta A.
Proof.
  induction A as [m [p t]| |]; simpl; intros;
    [ do 2 f_equal; auto using term_rename_fresh
      | destruct_notIn; f_equal; auto
      | f_equal; auto
    ].
Qed.

Lemma context_rename_fresh : forall De eta a a0,
  a0 # oc_c De ->
  a0 # dom eta ->
  a0 # image eta ->
  rename_c ((a0, eta ** a) :: eta) (rename_c ((a, a0) :: nil) De) =
  rename_c eta De.
Proof.
  induction De as [ | A]; simpl; intros;
    [ reflexivity
      | destruct_notIn; f_equal; auto using formula_rename_fresh
    ].
Qed.

Lemma notIn_oc_rename_t : forall m (t : term m) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # oc_t (rename_t ((a0, eta ** a) :: eta) t).
Proof.
  induction t; simpl; intros; auto. 
  - case_name; auto; unfold fun_value; case_Env; intro F; simpl in F; destruct F; auto. 
    + rewrite H2 in *; apply H; elim (notIn_image eta a H H1); auto.
    + rewrite H2 in *; apply H; elim (notIn_image eta n H H1); auto.
  - solve_notIn.
Qed.

Lemma notIn_oc_rename_f : forall m (A : formula m) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # oc_f (rename_f ((a0, eta ** a) :: eta) A).
Proof.
  induction A as [m [p t] | |]; simpl; intros;
    [ auto using notIn_oc_rename_t
      | solve_notIn
      | auto
    ].
Qed.

Lemma notIn_oc_rename_c : forall (Ga : context) eta a a0,
  a0 # image eta ->
  a <> a0 ->
  a0 # oc_c (rename_c ((a0, eta ** a) :: eta) Ga).
Proof.
  induction Ga as [ | A Ga0]; simpl; intros;
    auto using notIn_app_2, notIn_oc_rename_f.
Qed.

Lemma sub_ctx_fresh_cst : forall Ga Ga0 a a0,
  sub_ctx Ga Ga0 ->
  a # oc_c Ga ->
  sub_ctx Ga (rename_c ((a, a0) :: nil) Ga0).
Proof.
  unfold sublist; intros.
  assert (a1 = rename_f ((a, a0):: nil) a1);
    [ rewrite rename_f_fresh;
      [ symmetry; apply rename_f_nil
        | contradict H0; exact (In_oc_sub H1 a H0)
      ]
      | rewrite H2; apply rename_In_ctx; auto
    ].  
Qed.

