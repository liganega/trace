(** * Substitution *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import environments.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import relocation.

(** Defining substitution requires special consideration for two reasons.

   - First, the relationship between syntax and semantics such as soundness
     and completeness should be realized in a natural way.

     For this purpose, we find that simultaneous substitution provides
     a convenient way in establishing the relationship.

   - Second, because of the trace part, it is not clear to which class
     the resulting expression of a substitution should belong.

     Thus we decided to state clearly the type of the resulting expression
     in the definition of substitution.


   - Notice the special role of the [Var] case because it needs relocation.

   - No alpha-conversion is used.

   - Since there are no parameters, substitution only for variables are necessary. *)

Notation assoc := (env name).

Fixpoint tsubst (eta:assoc (term nil)) l m (t: term m) {struct t} : term l :=
  match t with
    | Var y h    => match y <-? l with
                       | left p  => @Var l y p
                       | right _ => match eta ^^ y with
                                      | Some u => (treloc u (term_sub u l))
                                      | None   => @Cst l 0
                                    end
                     end
    | Cst c       => @Cst l c
    | App f t1 t2 => App f (tsubst eta l t1)  (tsubst eta l t2)
  end.

Notation "[[ l ! eta ]] t" := (tsubst eta l t) (at level 55, eta at next level).

Fixpoint subst (eta: assoc (term nil)) l m (A:formula m) {struct A} : formula l :=
  match A with
    | Atom (p,t) => Atom (p, [[l ! eta ]] t )
    | B --> C    => (subst eta l B) --> (subst eta l C)
    | Forall y B => Forall y (subst eta (y::l) B)
  end.

Notation "[ l ! eta ] A" := (subst eta l A) (at level 55).

Lemma trm_tsubst : forall m (t:term m) eta l (H: sub_name (ov_t t) l),
  [[l ! eta]] t = treloc t H.  
Proof.
  induction t; simpl; intros;
    [ destruct (x <-? l) as [|Hnotin]; [ f_equal | elim Hnotin];
      auto with datatypes
      | reflexivity
      | f_equal; auto ].
Qed.

(** For well-defined terms, local variable substitution has no effect. *)

Lemma term_tsubst : forall (t:term nil) (eta:assoc (term nil)),
  [[nil ! eta]] t = t.
Proof.
  intros;
  assert (sub_name (ov_t t) nil) as Hsub ;
    [ rewrite term_ov_nil_1; apply incl_refl
      | transitivity (treloc t Hsub); auto using trm_tsubst
    ].        
Qed.

Lemma formula_subst : forall m (A:formula m) eta l (H: sub_name (ov_f A) l),
  [l ! eta] A = freloc A H.  
Proof.
  induction A as [m [p t] | |]; simpl; intros; f_equal; auto.
  f_equal; auto using trm_tsubst.
Qed.

(** For well-defined formulae, local variable substitution has no effect. *)

Lemma fml_subst : forall (A:formula nil) (eta:assoc (term nil)),
  [nil ! eta] A = A.
Proof.
  intros; assert (sub_name (ov_f A) nil) as Hsub ;
    [ rewrite fml_ov_nil_1; apply incl_refl
      | transitivity (freloc A Hsub); auto using formula_subst
    ].
Qed.

(** Relocation has no effect on substitution. *)

Lemma tsubst_treloc_1 : forall m (t:term m) l l' eta (h: sub_name (ov_t t) l),
  [[l' ! eta]] (treloc t h) = [[l' ! eta]] t.
Proof.
  induction t; simpl; intros; f_equal; auto. 
Qed.

Lemma tsubst_reloc_2 : forall m (t:term m) l l' eta
  (h1: sub_name (ov_t t) l) (h2: sub_name (ov_t t) l'),
  [[l' ! eta]] (treloc t h1) = treloc t h2.
Proof.
  intros; transitivity ([[l'! eta]] t);
    auto using tsubst_treloc_1, trm_tsubst.
Qed.

(** Extending substitution with forbidden variables has no impact. *)

Lemma tsubst_In : forall m (t:term m) x l v eta,
  x @ l ->
  [[l ! eta]] t = [[l ! (x,v)::eta]] t.
Proof.
  induction t; simpl; intros; auto.
  - case_In; auto; case_name; case_Env; auto; elim n; intuition. 
  - f_equal; auto.
Qed.

Lemma subst_In : forall m (A:formula m) x l u eta,
  x @ l ->
  [l ! eta] A = [l ! (x,u)::eta] A.
Proof.
  induction A as [m [p t] | | ]; simpl; intros;
    [ rewrite <- tsubst_In; [reflexivity | exact H]
      | f_equal; auto
      | f_equal; auto using in_cons
    ].
Qed.

(** Substitution and [LEq] *)

Lemma tsubst_LEq_1 : forall m (t:term m) l l' eta eta',
  LEq l l' ->
  [[l' ! eta']] ([[l ! eta]] t) = [[l' ! eta]] t.
Proof.
  induction t; simpl; intros;
    [ destruct (x <-? l); simpl; destruct (x <-? l'); try reflexivity;
      [ elim n; elim H; intros; apply H0; exact i0
        | elim n; elim H; intros; apply H1; exact i0
        | case_Env; auto;
          apply tsubst_reloc_2; apply term_ov_nil_1
      ]
      | reflexivity
      | f_equal; auto
    ].
Qed.
  
Lemma subst_LEq_1 : forall m (A:formula m) l l' eta eta',
  LEq l l' ->
  [l' ! eta'] ([l ! eta] A) = [l' ! eta] A.
Proof.
  induction A as [m [p t] | | ]; simpl; intros l l' eta eta' H; inversion H;
    [ do 2 f_equal; apply tsubst_LEq_1; auto
      | f_equal; auto
      | f_equal; auto using LEq_cons
    ].
Qed.

Lemma tsubst_LEq_2 : forall m (t:term m) l l' k eta eta',
  LEq l l' ->
  [[k ! eta']] ([[l ! eta]] t) = [[k ! eta']] ([[l' ! eta]] t).
Proof.
  induction t; simpl; intros; auto.
  - inversion H; repeat (case_In); auto;
    [ elim n 
    | elim n
    | case_Env]; auto.
    transitivity (treloc t (term_sub t k)); auto using tsubst_reloc_2.
  - f_equal; auto.
Qed.

Lemma subst_LEq_2 : forall m (A:formula m) l l' k eta eta',
  LEq l l' ->
  [k ! eta'] ([l ! eta] A) = [k ! eta' ] ([l' ! eta] A).
Proof.
  induction A as [m [p t] | | ]; simpl; intros;
    [ do 2 f_equal; auto using tsubst_LEq_2
      | f_equal
      | f_equal
    ]; auto using LEq_cons.
Qed.

(** ** Substitutions Lemma *)

Lemma t_substitution : forall m (t:term m) y l (eta:assoc (term nil)) (u:term nil),
  [[l ! (y,u)::nil]] ([[(y :: l) ! eta]] t) =
  [[l ! (y, u) :: eta]] t.
Proof.
  induction t; intros; auto; [| simpl; f_equal; auto].
  unfold tsubst at 2; destruct ( x == y); subst; auto.
  - case_In; [simpl; case_name; congruence | elim n; auto with datatypes].
  - case_In; simpl. apply neq_In_cons in i0; auto.
    + case_In; auto; intuition. 
    + generalize (notIn_cons_2 n0); intros; case_Env; simpl. 
      * case_In; auto; [elim H; auto |].
        case_name; auto;
        [elim n0; auto with datatypes 
        | rewrite trm_tsubst with (t:= treloc t (term_sub t (y ::l))) (H:= treloc_ov_2 t _ _)]; auto.
      * case_In; auto; 
        [ elim H
        | case_name; auto; elim n0] ; auto with datatypes. 
Qed.

Lemma substitution : forall m (A : formula m) y l (eta:assoc (term nil)) (u:term nil),
  [l ! (y,u) :: nil] ([y :: l ! eta] A) = [l ! (y, u) :: eta] A.
Proof.
  induction A as [m [p t] | | ]; simpl; intros;
    [ do 2 f_equal; apply t_substitution
      | f_equal; auto
      | f_equal; destruct (x == y) as [xy | nxy];
        [ subst y; rewrite subst_LEq_1; auto using LEq_xx, subst_In, in_eq
          | rewrite subst_LEq_2 with (l':= y::x::l); auto using LEq_xy
        ]
    ].
Qed.

