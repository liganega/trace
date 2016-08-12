(** * Module [extralibrary]: library functions, theorems, and tactics *)

Require Import Arith.
Require Import ZArith.
Require Import List.
Require Export decidable_In.

(** ** Tactics *)

Ltac decEq :=
  match goal with
  | [ |- (_, _) = (_, _) ] =>
      apply injective_projections; unfold fst,snd; try reflexivity
  | [ |- (@Some ?T _ = @Some ?T _) ] =>
      apply (f_equal (@Some T)); try reflexivity
  | [ |- (@cons ?T _ _ = @cons ?T _ _) ] =>
      apply (f_equal2 (@cons T)); try reflexivity
  | [ |- (?X _ _ _ _ _ = ?X _ _ _ _ _) ] =>
      apply (f_equal5 X); try reflexivity
  | [ |- (?X _ _ _ _ = ?X _ _ _ _) ] =>
      apply (f_equal4 X); try reflexivity
  | [ |- (?X _ _ _ = ?X _ _ _) ] =>
      apply (f_equal3 X); try reflexivity
  | [ |- (?X _ _ = ?X _ _) ] =>
      apply (f_equal2 X); try reflexivity
  | [ |- (?X _ = ?X _) ] =>
      apply (f_equal X); try reflexivity
  | [ |- (?X ?A <> ?X ?B) ] =>
      cut (A <> B); [intro; congruence | try discriminate]
  end.

Ltac omegaContradiction :=
  cut False; [contradiction|omega].

Ltac caseEq name :=
  generalize (refl_equal name); pattern name at -1 in |- *; case name.

(** ** Arithmetic *)

Inductive comparison_nat (x y: nat) : Set :=
  | Nat_less:    x < y -> comparison_nat x y
  | Nat_equal:   x = y -> comparison_nat x y
  | Nat_greater: x > y -> comparison_nat x y.

Lemma compare_nat: forall x y, comparison_nat x y.
Proof.
  intros. case (lt_eq_lt_dec x y); intro.
  destruct s. apply Nat_less; auto. apply Nat_equal; auto.
  apply Nat_greater; auto.
Defined.


Lemma map_append {A} {B} (f: A -> B) (l1 l2: list A) :
  map f (l1 ++ l2) = (map f l1) ++ (map f l2).
Proof.
  induction l1; simpl; intros. auto. decEq; auto. 
Qed.


(** ** Peano induction. *)

(** This is a variant of the induction principle over natural
  numbers.  It will be used later to do induction over
  the size of a type. *)

Lemma Peano_induction:
  forall (P: nat -> Prop),
  (forall x, (forall y, y < x -> P y) -> P x) ->
  forall x, P x.
Proof.
  intros P H.
  assert (forall x, forall y, y < x -> P y).
  induction x; intros.
  omegaContradiction.
  apply H. intros. apply IHx. omega.
  intro. apply H0 with (S x). omega.
Qed.


Ltac destruct_notIn :=
  match goal with
    | H : (?x # (?l ++ ?m)) |- _  =>
      destruct (notIn_app_1 x l m H); clear H; destruct_notIn
    | x := ?l |- _ =>
      assert (x = l); auto; clearbody x; destruct_notIn
    | _ => idtac
  end.


Ltac solve_notIn :=
  intros;
  destruct_notIn;
  repeat first [ apply notIn_app_2
               | apply notIn_cons_3
               | apply notIn_singleton_1
               | apply notIn_empty_1

               ];
  auto;
  try tauto;
  fail "Not solvable by [solve_notIn]; try [destruct_notIn]".

