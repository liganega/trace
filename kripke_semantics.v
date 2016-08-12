(** * Kripke Semantics *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import environments.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import substitution.
Require Import variable_sets.
Require Import fresh_csts.
Require Import relocation.  

(** ** Kripke Model *)

(** We use the conventional Kripke model adopted by Troelstra and van Dalen
   for the semantics of LJT.

   - A Kripke model is a tuple of a partially-ordered set of _worlds_, a domain,
     interpretations of constants and function symbols into the domain,
     and a binary relation between worlds and atomic sentences. *)

Record Kripke : Type := {
  worlds: Type;
  wle : worlds -> worlds -> Type;
  wle_refl : forall w, wle w w;
  wle_trans : forall w w' w'', wle w w' -> wle w' w'' -> wle w w'';
  domain : Type;
  csts : name -> domain;
  funs : function -> domain -> domain -> domain;
  atoms : worlds -> predicate * domain -> Type;
  atoms_mon : forall w w', wle w w' -> forall P, atoms w P -> atoms w' P
  }.

Notation "w <= w'" := (wle _ w w') (at level 70).

(** ** Semantics *)

(** Interpretation of a pseudo-term in a Kripke model using associations for variables.

   - The interpretation of pseudo-terms is made total by ignoring insignificant variables.

   - The being-in-a-list part of a term is simply ignored during the interpretation.

   - The trace relocation has no impact on the Kripke semantics. *)

Fixpoint psem K m (t:term m) (eta:assoc (domain K)){struct t} :
  domain K :=
  match t with
    | Var x _ => match eta ^^ x with
                    | Some u => u
                    | None => csts _ 0 (* fixed value *)
                  end
    | Cst c => csts _ c
    | App f t1 t2 => funs _ f (psem K t1 eta) (psem K t2 eta)
  end.

(** Forcing: The Kripke semantics is extended to all formulae *)

Reserved Notation "w ||- A [ eta ]" (at level 80).

Fixpoint force K (w: worlds K) m (A : formula m) eta {struct A} : Type :=
  match A with
    | Atom (p,t) => atoms K w (p, psem K t eta)
    | B --> C    => forall w', w <= w' -> 
                    w' ||- B [eta] -> w' ||- C [eta]
    | Forall y B => forall w', w <= w' ->
                    forall (d :domain K), w' ||- B [(y, d) :: eta]
  end
  
  where " w ||- A [ eta ] " := (force _ w A  eta).

Notation "w ||- A [ eta ]" := (force _ w A eta) (at level 80).

(** Forcing is monotone w.r.t. the world relation. *)

Lemma mono_force : forall K (w w':worlds K) eta,
  w <= w' -> 
  forall m (A:formula m),
    w ||- A [eta] -> w' ||- A [eta].
Proof.
  induction A as [m [p t]| |]; simpl; intros.  
  apply atoms_mon with (w:=w); auto. 

  apply X0; eauto using wle_trans. 

  apply X0; eauto using wle_trans. 
Qed.

(** Kripke semantics is independent of relocation. *)

Lemma reloc_psem : forall m (t: term m) K eta 
  k l (h: sub_name (ov_t t) k) (h0: sub_name (ov_t t) l),
  psem K (treloc t h) eta = psem K (treloc t h0) eta.
Proof. 
  induction t; simpl; intros; f_equal; auto. 
Qed.

Fixpoint reloc_force m (A: formula m) {struct A} :
  forall K (w: worlds K) eta
    k l (h: sub_name (ov_f A) k) (h0: sub_name (ov_f A) l),
    w ||- (freloc A h) [eta] ->
    w ||- (freloc A h0) [eta] :=
      match A in formula _ return 
        forall K (w: worlds K) eta
          k l (h: sub_name (ov_f A) k) (h0: sub_name (ov_f A) l),
          w ||- (freloc A h) [eta] ->
          w ||- (freloc A h0) [eta]
        with
        | Atom (p, t) => fun K w eta k l h h0 Hatom => 
          let P := fun (d:domain K) => atoms K w (p, d) in
            eq_rect_r P Hatom (
              reloc_psem t K eta (In_inv_atom _ _ h0)(In_inv_atom _ _ h))
        | B --> C => fun K w eta k l h h0 Himply =>
          let h' := In_inv_impL B C h in
          let h'' := In_inv_impR B C h in
          let h0' := In_inv_impL B C h0 in
          let h0'' := In_inv_impR B C h0 in
            fun w' (h1:w <= w') (h2: w' ||- (freloc B h0') [eta]) =>
              let p1 := reloc_force B K w' eta h0' h' h2 in
              let p2 := Himply w' h1 p1 in
                reloc_force C K w' eta h'' h0'' p2
        | Forall y B => fun K w eta k l h h0 Hall => 
          fun w' (h1:w <= w')(d:domain K) =>
            reloc_force B K w' ((y,d) :: eta)
            (In_inv_all B h) (In_inv_all B h0) (Hall w' h1 d)
      end.

(** ** Equivalence of associations *)

Definition assoc_equiv (A:Type) (m:trace) (eta eta0:assoc A) :=
  forall x, x @ m -> eta ^^ x = eta0 ^^ x.

Hint Unfold assoc_equiv.

Lemma assoc_equiv_comm : forall (A:Type) (m:trace) (eta eta0:assoc A),
  assoc_equiv m eta eta0 ->
  assoc_equiv m eta0 eta.
Proof.
  firstorder using assoc_equiv.
Qed.

Lemma assoc_equiv_cons : forall A m (eta eta0 : assoc A),
  assoc_equiv m eta eta0 ->
  forall x d,
    assoc_equiv (x :: m) ((x, d) :: eta) ((x, d) :: eta0).
Proof.
  unfold assoc_equiv; intros; simpl; case_name; auto.
  eauto using neq_In_cons.
Qed.

Hint Resolve assoc_equiv_comm assoc_equiv_cons.

(** A specified tactic for handling [assoc_equiv]. *)

Ltac solve_assoc :=
  let z := fresh "z" in
    let Hz := fresh "Hz" in
      intros z Hz; simpl in *; repeat case_name; intuition.

(** Semantics for well-defined terms/formulas is fixed. *)

Lemma psem_assoc_equiv : forall K m eta eta0 (t:term m),
  assoc_equiv m eta eta0 -> 
  psem K t eta = psem K t eta0.
Proof.
  induction t; simpl; intros;
    [ rewrite H; auto
      | reflexivity
      | f_equal; auto
    ].
Qed.

Lemma psem_term_assoc_indep : forall K eta eta' (t:(term nil)),
  psem K t eta = psem K t eta'.
Proof.
  intros; apply psem_assoc_equiv; firstorder.
Qed.  

Lemma force_assoc_equiv : forall m (A:formula m) K (w:worlds K) eta eta0,
  assoc_equiv m eta eta0 -> 
  w ||- A [eta] ->
  w ||- A [eta0].
Proof.
  induction A as [m [p t] | |]; simpl; intros;
    [ rewrite psem_assoc_equiv with (eta0:=eta0) in X; auto
      | eauto
      | apply IHA with (eta := (x,d)::eta); auto
    ].
Qed.

Lemma force_formula_assoc_indep : forall K (w:worlds K) eta eta' (A: formula nil),
  w ||- A [eta] ->
  w ||- A [eta'].
Proof.
  intros; apply force_assoc_equiv with eta; firstorder.
Qed.

(** ** Forcing and substitution *)

Theorem psem_tsubst_In : forall m (t:term m) l x u K eta,
  sub_name (dom eta) l ->
  x @ l ->
  psem K ([[l ! (x,u)::nil]] t) eta = psem K t eta.
Proof.
  induction t; simpl; intros;
    [ destruct (x <-? l); try case_name; auto; simpl; intuition (rewrite notIn_dom_None); auto
      | reflexivity
      | f_equal; auto ].
Qed.

Theorem force_subst_In : forall m (A:formula m) l x u K (w:worlds K) eta,
  sub_name (dom eta) l ->
  x @ l ->
  w ||- ([l ! (x,u)::nil] A) [eta] ->
  w ||- A [eta]

  with subst_In_force : forall m (A:formula m) l x u K (w:worlds K) eta,
    sub_name (dom eta) l ->
    x @ l ->
    w ||- A [eta] ->
    w ||- ([l ! (x,u)::nil] A) [eta].
Proof.
  induction A as [m [p t] | m A1 IHA1 A2 IHA2 | m y A]; simpl; intros.
  rewrite <- psem_tsubst_In with (l:=l) (x:=x) (u:=u); assumption.

  clear IHA1 IHA2.
  apply force_subst_In with (l:=l)(x:=x)(u:=u);[ assumption | assumption | ].
  apply X; try assumption. 
  apply subst_In_force; assumption.

  clear IHA.
  apply force_subst_In with (l:=y::l)(x:=x)(u:=u);
    [ simpl; apply incl_cons_3; exact H
      | apply in_cons; exact H0
      | apply X; assumption ].

  induction A as [m [p t] | m A1 IHA1 A2 IHA2 | m y A]; simpl; intros.
  rewrite psem_tsubst_In with (x:=x)(u:=u); assumption.

  clear IHA1 IHA2.
  apply subst_In_force; try assumption.
  apply X; try assumption. 
  apply force_subst_In with (l:=l)(x:=x)(u:=u); assumption.

  clear IHA.
  apply subst_In_force;
    [ simpl; apply incl_cons_3; exact H
      | apply in_cons; exact H0
      | apply X; assumption ].
Qed.

Lemma psem_tsubst : forall m (t:term m) x l (u:(term nil)) K eta,
  sub_name (dom eta) l ->
  psem K t ((x, psem K u eta) :: eta) =
  psem K ([[(l \ x) ! (x,u):: nil]] t) eta.
Proof.
  induction t; simpl; intros;
    [ case_name; case_In;
      [ destruct (notIn_rm_1 x0 l); auto
        | pattern u at 1; rewrite (treloc_id u (sub_ov_term u)); apply reloc_psem
        | auto
        | rewrite notIn_dom_None; auto;
          contradict n0; unfold sublist in *; apply (@In_rm_2 name (name_Dec)); auto
      ]          
      | reflexivity
      | f_equal; auto ].
Qed.

Theorem force_subst : forall m (A:formula m) x l (u:(term nil)) K (w:worlds K) eta,
  sub_name (dom eta) l ->
  w ||- A [(x, psem K u eta) :: eta] ->
  w ||- ([(l \ x) ! (x,u)::nil] A) [eta]

with subst_force : forall m (A:formula m) x l (u:term nil) K (w:worlds K) eta, 
  sub_name (dom eta) l ->
  w ||- ([(l \ x) ! (x,u)::nil] A) [eta] ->
  w ||- A [(x, psem K u eta) :: eta].
Proof.
  { destruct A as [ [p t] | A1 A2 | y A ]; simpl; intros.
  - rewrite <- psem_tsubst; auto.
  - apply force_subst; auto; apply X; auto; apply subst_force with (l:=l); auto.
  - destruct (x == y) as [xyeq | xyneq].
    + apply subst_In_force.
      * simpl; apply (@incl_rm_4 name (name_Dec)); assumption.
      * rewrite xyeq; apply in_eq.
      * apply force_assoc_equiv with
              ((y, d) :: (x, psem K u eta) :: eta); auto; solve_assoc.
    + rewrite (@rm_cons name (name_Dec)); auto.
      apply force_subst;
        [ simpl; apply incl_cons_3; exact H
        |  rewrite psem_assoc_equiv with (eta0:= eta);
          [ apply force_assoc_equiv with
            ((y, d) :: (x, psem K u eta) :: eta); auto; solve_assoc
          | solve_assoc]
        ].
  }

  { destruct A as [ [p t] | A1 A2 | y A ]; simpl; intros.
    - rewrite <- psem_tsubst in X; auto.
    - apply subst_force with (l:=l); auto; apply X; auto; apply force_subst; auto.
    - destruct (x == y) as [xyeq | xyneq].
      + apply force_assoc_equiv with ((y,d) :: eta).
        * solve_assoc.
        * apply force_subst_In with (l:= y:: (l \ x))(x:=x)(u:=u).
          simpl; apply (@incl_rm_4 name name_Dec); auto. 
          rewrite xyeq; auto with datatypes. 
          apply X; auto. 
      + rewrite (@rm_cons name name_Dec) in X; auto.
        apply force_assoc_equiv with ((x, psem K u eta) :: (y,d) :: eta).
        * solve_assoc.
        * rewrite psem_assoc_equiv with (eta0:= (y,d)::eta);
         [ apply subst_force with (l:= y::l);
            [ simpl; apply incl_cons_3; exact H
            | apply X; exact X0
            ]
          | solve_assoc
          ].
  }
Qed.