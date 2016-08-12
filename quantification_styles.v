(** * Equivalence of 3 quantification styles *)

Set Implicit Arguments.

Require Import decidable_In. 
Require Import environments.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.
Require Import substitution.
Require Import fresh_csts.
Require Import LJT_and_weakening.
Require Import renaming.

(** ** Deduction with Cofinite-quantification  *)

Reserved Notation "Ga |~ A" (at level 70).
Reserved Notation "Ga ;; A |~ C" (at level 70, A at next level).

Inductive co_prove : context -> (formula nil) -> Type :=
| co_ProofCont : forall (A C: (formula nil)) (Ga:context), 
  A @ Ga -> Ga ;; A |~ C -> Ga |~ C

| co_ProofImplyR : forall B C Ga, 
  (cons B Ga) |~ C -> Ga |~ B --> C

| co_ProofForallR : forall y (B : formula (y::nil)) Ga L,
  (forall (c: name), c # L -> Ga |~ [nil ! (y,Cst nil c)::nil] B) -> 
  Ga |~ (Forall y B)

  where "Ga |~ A" := (co_prove Ga A)

with co_prove_stoup : list (formula nil) -> (formula nil) -> (formula nil) -> Type :=

| co_ProofAxiom Ga C: Ga ;; C |~ C

| co_ProofImplyL Ga D : forall B C, 
  Ga |~ B -> Ga ;; C |~ D -> Ga ;; (B --> C) |~ D

| co_ProofForallL Ga C : forall y (u:(term nil)) (B: formula (y :: nil)), 
  Ga ;; [nil ! (y,u)::nil] B |~ C ->
    Ga ;; (Forall y B) |~ C

  where " Ga ;; B |~ A " := (co_prove_stoup Ga B A).

Notation "Ga |~ A" := (co_prove Ga A) (at level 70).
Notation "Ga ;; A |~ C" := (co_prove_stoup Ga A C) (at level 70, A at next level).

(** ** Deduction with AllFresh-quantification  *)

Reserved Notation "Ga |+ A" (at level 70).
Reserved Notation "Ga ;; A |+ C" (at level 70, A at next level).

Inductive all_prove : context -> (formula nil) -> Type :=
| all_ProofCont : forall (A C: (formula nil)) (Ga:context), 
  A @ Ga -> Ga ;; A |+ C -> Ga |+ C

| all_ProofImplyR : forall B C Ga, 
  (cons B Ga) |+ C -> Ga |+ B --> C

| all_ProofForallR : forall y (B : formula (y::nil)) Ga,
  (forall (c: name), c # (oc_c Ga ++ oc_f B) -> Ga |+ [nil ! (y,Cst nil c)::nil] B) -> 
  Ga |+ (Forall y B)

  where "Ga |+ A" := (all_prove Ga A)

with all_prove_stoup : list (formula nil) -> (formula nil) -> (formula nil) -> Type :=

| all_ProofAxiom Ga C: Ga ;; C |+ C

| all_ProofImplyL Ga D : forall B C, 
  Ga |+ B -> Ga ;; C |+ D -> Ga ;; (B --> C) |+ D

| all_ProofForallL Ga C : forall y (u:(term nil)) (B: formula (y :: nil)), 
  Ga ;; [nil ! (y,u)::nil] B |+ C ->
    Ga ;; (Forall y B) |+ C

  where " Ga ;; B |+ A " := (all_prove_stoup Ga B A).

Notation "Ga |+ A" := (all_prove Ga A) (at level 70).
Notation "Ga ;; A |+ C" := (all_prove_stoup Ga A C) (at level 70, A at next level).

(** ** Equivalence of 3 quantification styles *)

(** We prove the equivalence of the 3 quantification styles:

   - Ga |- A ==>  Ga |+ A

   - Ga |+ A ==>  Ga |~ A

   - Ga |~ A ==>  Ga |- A *)

Lemma all_prove_from_prove : forall Ga A, 
  Ga |- A ->
    forall eta, rename_c eta Ga |+ rename_f eta A

with all_prove_stoup_from_prove_stoup : forall Ga A C,
  Ga ;; A |- C ->
    forall eta, rename_c eta Ga ;; rename_f eta A |+ rename_f eta C.
Proof.
  destruct 1; simpl; intros;
    [ apply all_ProofCont with (rename_f eta A);
      [ apply rename_In_ctx; auto
        | apply all_prove_stoup_from_prove_stoup; assumption
      ]
      | apply all_ProofImplyR;
        change (rename_f eta B :: rename_c eta Ga) with (rename_c eta (B :: Ga));
          apply all_prove_from_prove; assumption
      | apply all_ProofForallR; intros;
        simpl in *; destruct_notIn; 
          set (eta' := (a,c) :: eta);
            rewrite <- (rename_c_fresh _ _ a c H3);
              rewrite <- (rename_f_fresh _ _ a c H0);
                replace ((y, Cst nil c)::nil) with
                  (rename_a ((a,c) :: eta) ((y, Cst nil a) :: nil));
                  [ rewrite <- rename_subst;
                    [ apply all_prove_from_prove; auto
                      | simpl; auto
                    ]
                    | simpl; case_name; intuition try congruence
                  ]
    ].        

  destruct 1; simpl; intros;
    [ apply all_ProofAxiom
      | apply all_ProofImplyL; auto
      | apply all_ProofForallL with (rename_t eta u);
        replace ([nil ! (y, rename_t eta u) :: nil] rename_f eta B)
      with (rename_f eta ([nil ! (y, u) :: nil] B));
        [ apply all_prove_stoup_from_prove_stoup; assumption
          | apply rename_subst; simpl; intros; auto
        ]
    ].
Qed.

Lemma co_prove_from_all_prove : forall Ga A, 
  Ga |+ A ->
  Ga |~ A

  with co_prove_stoup_from_all_prove_stoup : forall Ga A C,
    Ga ;; A |+ C ->
    Ga ;; A |~ C.
Proof.
  destruct 1;
    [ apply co_ProofCont with A; auto
      | apply co_ProofImplyR; auto
      | apply co_ProofForallR with (L:= oc_c Ga ++ oc_f B); auto
    ].

  destruct 1;
    [ apply co_ProofAxiom
      | apply co_ProofImplyL; auto
      | eapply co_ProofForallL; eauto
    ].
Qed.

Lemma prove_from_co_prove : forall Ga A, 
  Ga |~ A ->
  Ga |- A

  with prove_stoup_from_co_prove_stoup : forall Ga A C,
    Ga ;; A |~ C ->
    Ga ;; A |- C.
Proof.
  { destruct 1.
    + apply ProofCont with A; auto.
    + apply ProofImplyR; auto.
    + set (c':= new (L ++ oc_c (Forall y B :: Ga)));
      assert (c' = new (L ++ oc_f B ++ oc_c Ga)) as H; auto.
      generalize (new_fresh (L ++ oc_f B ++ oc_c Ga)); intro.
      apply ProofForallR with c'; destruct_notIn; simpl. 
      rewrite H; destruct_notIn; auto with datatypes.
  }
  { destruct 1;
    [ apply ProofAxiom
      | apply ProofImplyL; auto
      | apply ProofForallL with u; auto
    ].
  }
Qed.
