(** * Intuitionistic sequent calculus LJT *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import environments.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution.
Require Import fresh_csts.
Require Import renaming.

(** For the presentation of predicate logic, we adopt sequent calculus
   to represent proofs. The advantage of such an approach is that
   it has an easy-to-define notion of normal form (it is merely
   the absence of the cut rule). A disadvantage is that it is less
   natural than the so-called natural deduction.

   The Gentzen-style sequent calculus [LJT] is obtained from the
   intuitionistic sequent calculus [LJ] by restricting the use of
   the left introduction rules of the implication and the universal
   quantification.

   Herbelin and Mints showed that there is a one-to-one correspondence
   between cut-free proofs in [LJT] and normal lambda-terms.
   This implies that LJT is a Curry-Howard-de Bruijn-style proof system. *)

Reserved Notation "Ga |- A" (at level 70).
Reserved Notation "Ga ;; A |- C" (at level 70, A at next level).

Inductive prove : context -> (formula nil) -> Type :=
  | ProofCont : forall (A C: (formula nil)) (Ga:context), 
    A @ Ga -> Ga ;; A |- C -> Ga |- C

  | ProofImplyR : forall B C Ga, 
    (cons B Ga) |- C -> Ga |- B --> C

  | ProofForallR : forall y (B : formula (y::nil)) Ga (a:name),
    a # oc_c (Forall y B :: Ga) ->
    Ga |- [ nil ! (y, @Cst nil a)::nil ] B -> 
    Ga |- (@Forall nil y B)

  where "Ga |- A" := (prove Ga A)

with prove_stoup : list (formula nil) -> (formula nil) -> (formula nil) -> Type :=
  | ProofAxiom Ga C: Ga ;; C |- C

  | ProofImplyL Ga D : forall B C, 
    Ga |- B -> Ga ;; C |- D -> Ga ;; (B --> C) |- D

  | ProofForallL Ga C : forall y (u:(term nil)) (B: formula (y :: nil)), 
    Ga ;; [nil ! (y,u)::nil] B |- C ->
    Ga ;; (@Forall nil y B) |- C

  where " Ga ;; B |- A " := (prove_stoup Ga B A).

Notation "Ga |- A" := (prove Ga A) (at level 70).
Notation "Ga ;; A |- C" := (prove_stoup Ga A C) (at level 70, A at next level).

(** REMARKS:

   - All the formulae occurring in derivations are well-formed.
     This is possible because we can primarily focus on [well-formed formula := formula nil].

   - The so-called [Exists-Fresh] style of quantification is used for the right
     universal quantification. *)


(** ** Weakening *)

(** Simple structural induction on derication does not work.

   - This is a well-known issue about the [Exists-Fresh] style of quantification.

   - The [Exists-Fresh] style of quantification provides too _weak_ an induction principle.

   - We suggest a solution to that issue using simultaneous [renaming].

   - No alpha-conversion is necessary. *)

(** Generalized Weakening Lemma  *)

Lemma weakening_gen : forall Ga De A eta,
  sub_ctx Ga De -> 
  Ga |- A ->
  rename_c eta De |- rename_f eta A

with weakening_stoup_gen : forall Ga De A C eta,
  sub_ctx Ga De ->
  Ga ;; A |- C ->
  rename_c eta De ;; rename_f eta A |- rename_f eta C.
Proof.
  { destruct 2; simpl.
    
    - apply ProofCont with (rename_f eta A);
      [ apply rename_In_ctx; apply H; auto
      | apply weakening_stoup_gen with Ga; auto
      ].
      
    - apply ProofImplyR; 
      change (rename_c eta (B :: De) |- rename_f eta C);
      apply weakening_gen with (B :: Ga); auto using incl_cons_3.
   
    - set (l:= 
               ((a::nil) ++ oc_c De ++ oc_f B ++
                 oc_c (rename_c eta De) ++ oc_f (Forall y (rename_f eta B)) ++
                 dom eta ++ image eta ++
                 oc_f (Forall y B) ++ oc_c Ga));
      set (a0:= new l); 
      generalize (new_fresh l); intro Hnew.
      simpl in n; destruct_notIn. 
      rewrite H4, <- H3 in *; repeat (apply notIn_app_1 in Hnew; destruct Hnew as [? Hnew]). 
      clear H3 H4; apply notIn_cons_1 in H5.
      rewrite <- context_rename_fresh with (a := a) (a0:= a0); auto.
      + set (De0 := rename_c ((a,a0) :: nil) De);
        rewrite <- rename_f_fresh with (a:=a0)(a0:= eta ** a); auto with datatypes.
        apply ProofForallR with a0.
        * simpl; auto using notIn_app_2, notIn_oc_rename_f, notIn_oc_rename_c.
        *{ rewrite <- rename_c_fresh with (a:=a)(a0:=a0).
           - rewrite <- rename_f_fresh with (a:=a)(a0:=a0); auto;
            set (eta0 := (a,a0) :: (a0, eta ** a) :: eta);
            replace ((y, @Cst nil a0) :: nil) with (rename_a eta0 ((y, @Cst nil a) :: nil)).
             +  rewrite <- rename_subst;
              [ apply weakening_gen with Ga; auto; apply sub_ctx_fresh_cst; auto
              | simpl; intros; auto].
             + unfold eta0; simpl; case_name; congruence.
           - unfold De0; replace a0 with (nil ** a0); auto using notIn_oc_rename_c. 
         }
  }
    - destruct 2; simpl; intros;
      [ apply ProofAxiom
      | apply ProofImplyL; eauto
      | apply ProofForallL with (u:= rename_t eta u);
        replace ((y,rename_t eta u) :: nil) with (rename_a eta ((y,u):: nil)); auto;
        rewrite <- rename_subst; eauto
      ].
Qed.

Lemma weakening : forall Ga De A,
  sub_ctx Ga De -> 
  Ga |- A ->
  De |- A.
Proof.
  intros.
  rewrite <- (rename_c_nil De).
  rewrite <- (rename_f_nil A).
  eauto using weakening_gen. 
Qed.

Lemma weakening_stoup : forall Ga De A C,
    sub_ctx Ga De ->
    Ga ;; A |- C ->
    De ;; A |- C.
Proof.
  intros.
  rewrite <- (rename_c_nil De).
  rewrite <- (rename_f_nil A).
  rewrite <- (rename_f_nil C).
  eauto using weakening_stoup_gen.
Qed.

(** Renaming Lemma *)

Lemma renaming : forall Ga A eta,
  Ga |- A ->
  rename_c eta Ga |- rename_f eta A.
Proof.
  firstorder using weakening_gen.
Qed.

Lemma renaming_stoup : forall Ga A C eta,
  Ga ;; A |- C ->
  rename_c eta Ga ;; rename_f eta A |- rename_f eta C.
Proof.
  firstorder using weakening_stoup_gen.
Qed.
