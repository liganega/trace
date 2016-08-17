(** * Language Syntax *)

Set Implicit Arguments.

Require Import decidable_In.

(** The language syntax for the first-order logic is represented.

   - Implication and universal quantification are the only logical symbols.

   - We assume there are two decidable sets of infinitely many "unary" predicates
     and "binary" functions.

   - This is general enough because predicate and function symbols of different
     arities can be encoded. *)


Notation name := nat.
Notation eq_name :=eq_nat_dec.

Instance name_Dec : EqDec name :=
  {
    dec := eq_name
  }.

Ltac case_name :=(case_dec eq_name; subst).

Parameter predicate : Set.      (* unary predicates *)
Parameter function : Set.       (* binary functions *)

(** We assume decidability of function and predicate symbols *)

Axiom eq_pred : EqDec predicate.
Axiom eq_fun : EqDec function.


(* ####################################################### *)
(** *** Representation with locally traced names *)

(** We suggest a style called "representation with locally traced names".

   - Our style is closely related to the McKinna-Pollack's _locally-named_ style.

   - That is, two sorts of named variables are used:
     -- (locally bound) _variables_
     -- _parameters_ (also called _free_ variables)

   - A new feature of is that the sets of terms and formulae depend on
     a list of variables, called a _trace_, that might be used
     during the term or formula construction.

   - That is, variables occurring in an expression are controlled by
     the type of that expression.

   - An important consequence is that we can talk about _well-formed_ terms
     and formulae without defining an extra syntax.
     (Well-formed expressions are those with an empty trace.) *)

(* ####################################################### *)
(** *** Constants as parameters *)

(** Syntactically, We don't use parameters (free variables).

   - We let constants play the role of constants.

   - An important consequence at the syntactic level is that substitution
     is needed only for variables.

   - The language itself needs to contain infinitely many constants.

   - Note that every language can be conservatively extended to a language
     with infinitely many constants.

   - Even if we formally introduce parameters, the substitution for parameters
     do not play any role

   - For the formalization with parameters, see the Coq files, called [with_FreeVar_*.v]. *)

(* ####################################################### *)
(** ** Pseudo-terms *)

(** Any decidable, denumerable set can be used for the representation of variables
   and constants.
   Here we use [name = nat], the set of natural numbers, to make the formlization
   as simple as possible. 

   Given a _trace_ [m], [pterm m] is the set of pseudo-terms with free occurrence
   of variables from the trace [m]. *)


Notation trace := (list name).

Inductive term (m : trace) : Set := 
| Var : forall (x: name), x @ m -> term m
| Cst  : name -> term m
| App  : function -> term m -> term m -> term m.

Implicit Arguments Var [m].
Implicit Arguments Cst [m].

(** ** Pseudo-formulas *)

(** Given a trace [m], [formula m] is the set of pseudo-formulae with free occurrence of
   variables from the trace [m].

   - Atomic pseudo-formulas are defined first. *)

Definition atom m := (predicate * term m)%type.

Inductive formula (m:trace) : Set :=
| Atom   : atom m -> formula m
| Imply  : formula m -> formula m -> formula m
| Forall : forall (x:name), formula (x::m) -> formula m.

Implicit Arguments Forall [m].

Notation "A --> B" := (@Imply _ A B) (at level 69, right associativity).

(** ** Well-formed terms and formulas *)

(** Well-formed expressions are expressions without any free occurrence of variables. *)

(** ** Contexts *)

Notation context := (list (formula nil)).

(** ** Occurrence of constances ([oc]): *)

(** This is a necessary step to talk about fresh constants for a context. *)

Fixpoint oc_t m (t:term m){struct t} : list name :=
  match t with
  | Var _ _    => nil
  | Cst c       => c :: nil
  | App _ t0 t1 => (oc_t t0) ++ (oc_t t1)
  end.

Fixpoint oc_f m (A:formula m){struct A} : list name :=
  match A with
  | Atom (p, t) => oc_t t
  | Imply B C   => oc_f B ++ oc_f C
  | Forall x A  => @oc_f (x::m) A
  end.

Fixpoint oc_c (Ga:context){struct Ga} : list name :=
  match Ga with
  | nil      => nil
  | A :: Ga' => oc_f A ++ oc_c Ga'
  end.

(** ** Free occurrence of variables ([ov]): *)

Notation "l \ x" := (remove eq_name x l)  (at level 69).

Fixpoint ov_t m (t:term m){struct t} : trace :=
  match t with
  | Var x _    => x :: nil
  | Cst _       => nil
  | App _ t0 t1 => (ov_t t0) ++ (ov_t t1)
  end.

Fixpoint ov_f m (A:formula m){struct A} : trace :=
  match A with
  | Atom (p, t) => ov_t t
  | Imply B C   => ov_f B ++ ov_f C
  | Forall x B  => (@ov_f (x::m) B) \ x
  end.

(** [fml] is decidable. *)

Require Import ProofIrrelevance.

Lemma In_proof_uniq `{a : A} {l : list A} (p q : In a l) :
  p = q.
Proof.
  apply proof_irrelevance.
Defined.

Lemma trm_dec : forall m (t t0 : term m), {t = t0} + {t <> t0}.
Proof.
  induction t; induction t0; try (right; discriminate).
  - destruct (eq_name x x0); subst.
    + left. rewrite (In_proof_uniq i i0); auto.
    + neq_case.
  - destruct (eq_name n n0); subst; auto.
    neq_case.
  - destruct (f == f0); subst; auto.
    + destruct (IHt1 t0_1); subst; auto;
      destruct (IHt2 t0_2); subst; auto; neq_case.
    + neq_case.
Qed.

Lemma atom_dec : forall m (P Q:atom m), {P = Q} + {P <> Q}.
Proof.
  destruct P as [p t]; destruct Q as [q u].
  decide equality; [ apply trm_dec | apply eq_pred ].
Qed.

Lemma fml_dec : forall m (A B: formula m), {A = B} + {A <> B}.
Proof.
  induction A as [? P | |]; destruct B as [Q | |]; try (right; discriminate);
    [ destruct (atom_dec P Q); 
      [ subst; left; reflexivity
        | neq_case
      ]
      | destruct (IHA1 B1); destruct (IHA2 B2);
        [ subst; left; reflexivity
          | neq_case
          | neq_case
          | neq_case
        ]
      | destruct (x == x0);
        [ subst x;
          destruct (IHA B) as [ | neq];
            [ left; subst; reflexivity
              | right; intro Heq; elim neq;
                inversion Heq as [HdepEq];
                  apply inj_pairT2 in HdepEq; assumption
            ]
          | neq_case
        ]
    ].
Qed.

(** A tactic for destructing the decidable equality between pseudo-expressions. *)

Ltac case_lang :=
  let destr t u := destruct (trm_dec t u); [try subst t | idtac] in
    let destr A B := destruct (fml_dec A B); [try subst A | idtac] in
  match goal with
    | |- context [trm_dec ?t ?u]       => destr t u
    | _ : context [trm_dec ?t ?u] |- _ => destr t u
    | |- context [fml_dec ?A ?B]       => destr A B
    | _ : context [fml_dec ?A ?B] |- _ => destr A B
  end.


Notation sublist :=incl.
Notation sub_name := incl.

(** ** Set-theoretic equivalence of lists *)

(** [LEq] indicates the set-theoretical equality of lists. *)

Notation LEq := (fun (l m: list name) => sub_name l m /\ sub_name m l).

Lemma LEq_cons : forall l l' x,
  LEq l l' -> LEq (x::l) (x::l').
Proof.
  intros l l' x H; inversion H. unfold sub_name; split; simpl; intros; 
  destruct H2; auto with datatypes. 
Qed.

Lemma LEq_xx : forall x l, LEq (x::x::l) (x::l).
Proof.
  split; unfold sub_name;
    intros; simpl; destruct (a == x); try exact I;
      eauto using neq_In_cons. 
Qed.

Lemma LEq_xy : forall x y l, LEq (x::y::l) (y::x::l).
Proof.
  split; unfold sub_name; simpl; intros; destruct H; intuition. 
Qed.
