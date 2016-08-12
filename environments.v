(** * Environmentts *)

Set Implicit Arguments.

Require Import Arith.
Require Import List.
Require Import extralibrary.


(** Given a set [A], asociaions are list of elements of [name * A]. 
   Environments are used for

   - simultaneous substitution

   - simultaneous renaming

   - Kripke semantics *)

Definition env (A X : Type) := list (A * X).

(** Domain of an environment *)

Definition dom {A X : Type} (rho: env A X) : list A :=
  map (@fst A X) rho.

Definition img {A X : Type} (rho: env A X) : list X :=
  map (@snd A X) rho.

Fixpoint lookup `{D : EqDec A} {X : Type} (a : A) (rho:env A X) :
  option X := 
  match rho with
    | nil => None
    | (b, x) :: rho0
      => if dec a b then Some x else lookup a rho0 
  end.

Notation " rho ^^ a " := (lookup a rho) (at level 60).

(** A tactic distinguishing values of function environment. *)

Ltac case_env :=
  match goal with
    | |- context [ ?e ^^ ?a ]       => destruct (e ^^ a)
    | H : context [ ?e ^^ ?a ] |- _ => destruct (e ^^ a)
  end.


Ltac case_Env :=
  match goal with
    | |- context [ ?e ^^ ?a ]       => case_eq (e ^^ a); intros
    | H : context [ ?e ^^ ?a ] |- _ => case_eq (e ^^ a); intros
  end.

Lemma dom_append {A X : Type} (e1 e2 : env A X) :
  dom (e1 ++ e2) = dom e1 ++ dom e2.
Proof.
  unfold dom; apply map_append. 
Qed.

Lemma dom_env_extends {A X : Type} (e1 e2 : env A X) a x y :
  dom (e1 ++ (a, x) :: e2) = dom (e1 ++ (a, y) :: e2).
Proof.
  repeat rewrite dom_append; reflexivity.
Qed.

Lemma env_dom_notIn_img  `{D : EqDec A} {X} {e : env A X} {x} :
  x # img e ->
  forall a, a @ dom e -> e ^^ a <> Some x.
Proof.
  induction e as [| []]; simpl; intros.
  - intuition.
  - case_var.
    + intro Hneq; inversion Hneq; intuition.
    + firstorder.
Qed.

(** If [a] is not in [dom (rho)], then [rho (a)] is undefined. *)

Lemma notIn_dom_None `{D : EqDec A}{X : Type} (a : A) (rho: env A X) :
  a # (dom rho) -> rho ^^ a = None.
Proof.
  induction rho as [| [ ]]; auto; simpl; intros. 
  case_var; intuition. 
Qed.

Hint Resolve notIn_dom_None.

Lemma lookup_inv `{D : EqDec A} {X : Type} (a : A) (x : X) (e : env A X) :
  e ^^ a = Some x -> a @ (dom e).
Proof.
  induction e as [| []]; simpl; 
  [ congruence
  | case_var; intuition]. 
Qed.

Lemma lookup_In `{D : EqDec A} {X : Type} (a : A) (x : X) (e : env A X) :
  e ^^ a = Some x -> (a, x) @ e.
Proof.
  induction e as [| []]; simpl; 
  [ | case_var]; intuition congruence. 
Qed.

(** If [a] is in [dom (rho)], there is some [x] s.t. [rho(a) = Some x]. *)

Lemma lookup_exists `{D : EqDec A} {X : Type} (a : A) (e : env A X) :
  a @ (dom e) -> exists x, e ^^ a = Some x.
Proof.
  induction e as [| []]; simpl; intros.
  - intuition.
  - case_var.
    + exists x; auto.
    + intuition congruence.
Qed.

Hint Resolve lookup_inv lookup_exists : datatypes.

Lemma env_lookup_In `{D : EqDec A} {X : Type} {a : A} {x : X} {e : env A X} :
  (a, x) @ e -> exists y, e ^^ a = Some y.
Proof.
  induction e as [| []]; simpl; intros. 
  - intuition.
  - case_var. 
    + eexists; auto.
    + elim H; intro; [intuition congruence | eauto].
Qed.


Lemma env_lookup_notIn `{D : EqDec A} {X : Type} {a : A} {e : env A X} :
  e ^^ a = None -> a # dom e.
Proof.
  induction e as [| []]; simpl; intros. 
  - intuition.
  - case_var; intuition congruence. 
Qed.


Lemma env_dom_In `{D : EqDec A} {X : Type} {a : A} {x : X} {e : env A X} :
  (a, x) @ e -> a @ dom e.
Proof.
  intros.
  elim (env_lookup_In H).
  intros x0 ?.
  apply lookup_inv with x0; auto.
Qed.

Lemma lookup_eq `{D : EqDec A} {X : Type} (a b : A) (x : X) (e : env A X) :
  a = b -> ((b, x) :: e) ^^ a = Some x.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma lookup_neq `{D : EqDec A} {X : Type} (a b : A) (x : X) (e : env A X) :
  a <> b -> e ^^ a  = ((b, x) :: e) ^^ a.
Proof.
  simpl; intros; case_var; intuition.
Qed.

Lemma lookup_ext_1 `{D : EqDec A} {X : Type} (a b : A) (e e0 : env A X) c x x0 :
  a = b ->
  (e ++ (a, x) :: e0) ^^ c = (e ++ (a, x) :: (b, x0) :: e0) ^^ c.
Proof.
  induction e as [ | []]; simpl; intros; 
    repeat case_var; intuition try congruence; auto.
Qed.

Lemma lookup_ext_2 `{D : EqDec A} {X : Type} (a b : A) (e e0 : env A X) c x x0 :
  a <> b ->
  (e ++ (a, x) :: (b, x0) :: e0) ^^ c =
  (e ++ (b, x0) :: (a, x) :: e0) ^^ c.
Proof.
  induction e as [ | [ ]]; simpl; intros; 
    repeat case_var; intuition try congruence; auto.
Qed.

Lemma lookup_ext_3 `{D : EqDec A} {X : Type} (a b : A) (e e0 : env A X) x :
  a = b ->
  a @ (dom e) -> 
  (e ++ e0) ^^ a = (e ++ (b, x) :: e0) ^^ a.
Proof.
  induction e as [ | [ ] ]; simpl; intros;  
  repeat case_var; intuition try congruence. 
Qed.

(** ** Removing elements from environments *)

(** env_rm A x rho = rho \ {(x,_)} *)

Fixpoint env_rm `{D : EqDec A} {X : Type} (rho : env A X) (a : A) : env A X :=
  match rho with
  | nil            => nil
  | (b, x) :: rho' => if a == b then env_rm rho' a
                                else (b, x) :: env_rm rho' a
  end.

Notation " rho ^- a " := (env_rm rho a) (at level 60).

Lemma env_rm_incl `{D : EqDec A} {X : Type} (rho : env A X) (a : A) :
  incl (rho ^- a) rho.
Proof.
  unfold incl; induction rho as [ | []]; simpl; auto; intros [a1 y] Ha1.
  case_var; [| simpl in *; elim Ha1]; intuition.
Qed.

Lemma env_rm_self `{D : EqDec A} {X : Type} (rho : env A X) (a : A) : 
  (rho ^- a) ^^ a = None.
Proof. 
  induction rho as [| [? ?]]; auto; simpl; intros.
  case_var; auto; simpl; case_var; intuition.
Defined.

Lemma env_neq `{D : EqDec A} {X : Type} (rho rho' : env A X) (a b : A) (u : X) :
  a <> b ->
  (rho ++ (b, u) :: rho') ^^ a = (rho ++ rho') ^^ a.
Proof.
  induction rho as [ | [ ]]; intros.
  - rewrite! app_nil_l. rewrite <-lookup_neq; auto.
  - simpl; case_var; auto.
Defined.

Lemma empty_dom `(a : A) (X : Type) :
  a # (dom (@nil (A * X))). 
Proof.
  intuition.
Defined.

Lemma In_dom_neq `(a : A) (b : A) {X : Type} (rho : env A X) (x : X) :
  a <> b ->
  a @ (dom ((b, x)::rho)) -> a @ (dom rho).
Proof.
  simpl; intros; intuition congruence.
Defined.

Lemma rm_dom `{D : EqDec A} {X : Type} (rho : env A X) (a : A) :
  dom (rho ^- a) = remove dec a (dom rho). 
Proof.
  induction rho as [| [ ] rho]; auto; simpl; intros. 
  case_var; simpl; congruence.
Defined. 

Lemma In_dom_neq_rm `{D : EqDec A} {X : Type} (rho : env A X) (a b : A) :
  a <> b ->
  a @ (dom rho) -> a @ (dom (rho ^- b)).
Proof.
  intros. rewrite rm_dom; auto using In_rm_2.
Defined.

Lemma not_In_dom `{D : EqDec A} {X : Type} (a : A) (rho : env A X) :
  a # dom (rho ^- a).
Proof.
  intros. rewrite rm_dom; apply notIn_rm_1.
Defined.

Lemma rm_rm `{D : EqDec A} {X : Type} (a : A) (rho : env A X) :
  rho ^- a = (rho ^-a) ^- a.
Proof.
  induction rho as [| [b ?] rho]; simpl; auto. 
  repeat (case_var; simpl; auto); intuition congruence.
Defined.

Lemma rm_neq_rm `{D : EqDec A} {X : Type} (a b : A) (rho : env A X) :
  a <> b ->
  (rho ^- b) ^- a = (rho ^- a) ^- b.
Proof.
  induction rho as [| [ ]]; auto; simpl; intros. 
  repeat (case_var; simpl; auto); intuition; congruence.
Defined.

Lemma rm_neq_rm_r `{D : EqDec A} {X : Type} (a b : A) (rho rho': env A X)(x : X) :
  a <> b ->
  (rho ++ (b, x) :: rho') ^- a = rho ^- a ++ (b, x) :: rho' ^- a.
Proof.
  induction rho as [ | [ ]]; auto; simpl; intros. 
  repeat (case_var; simpl; intuition).
  case_var; simpl; intuition congruence.
Defined.

Lemma rm_change `{D : EqDec A} {X : Type} (a b : A) (rho: env A X)(x : X) :
  a <> b ->
  ((b, x)::rho) ^- a = (b, x) :: rho ^- a.
Proof.
  intro H. apply (rm_neq_rm_r nil rho _ H). 
Defined.

Lemma rm_eq `{D : EqDec A} {X : Type} (a b : A) (rho: env A X) (x : X) :
  a = b ->
  ((b, x)::rho) ^- a = rho ^- a.
Proof.
  intros; simpl; case_var; intuition.
Defined.

Lemma rm_r `{D : EqDec A} {X : Type} (a : A) (rho rho' : env A X) :
  (rho ++ rho') ^- a = rho ^- a ++ rho' ^- a.
Proof.
  induction rho as [| [ ] ]; auto.
  simpl; case_var; auto. 
  rewrite <- app_comm_cons; congruence.
Defined.

Lemma env_rm_neq `{D : EqDec A} {X : Type} (a b : A) (rho : env A X) :
  a <> b -> 
  rho ^^ a = (rho ^- b) ^^ a.
Proof.
  induction rho as [| []]; auto; intros. 
  repeat (simpl; case_var; intuition).
Defined.


Lemma env_rm_notIn_dom `{D : EqDec A} {X : Type} (a : A) (rho : env A X) :
  a # dom rho -> 
  rho = (rho ^- a).
Proof.
  induction rho as [| []]; auto; simpl; intros; case_var; intuition congruence. 
Qed.
    

Lemma rm_eq_r `{D : EqDec A} {X : Type} (a b : A) (rho rho' : env A X) (x : X) :
  a = b ->
  (rho ++ (b, x) :: rho') ^- a = rho ^- a ++ rho' ^- a.
Proof.
  intros; subst; rewrite rm_r.
  simpl; case_var; intuition.
Defined.

(** For the following, one needs instances. *)


Instance nat_EqDec : EqDec nat := 
  {
    dec := eq_nat_dec
  }.

Hint Rewrite <- (@env_rm_neq _ nat_EqDec) : env_rmi.

(** We now define a notion of inclusion between environments that we
  call ``weakening''. [e2] weakens [e1] if all the bindings in [e1]
  are preserved in [e2]; however, [e2] may contain additional,
  non-interfering bindings. *) 

Definition env_weaken `{D : EqDec A} {X : Type} (e1 e2 : env A X) : Prop :=
  forall a x, e1 ^^ a = Some x -> e2 ^^ a = Some x.

Hint Unfold env_weaken.

Lemma env_weaken_incl_dom `{D : EqDec A} {X : Type} (e1 e2 : env A X) : 
  env_weaken e1 e2 -> incl (dom e1) (dom e2).
Proof.
  unfold incl; intros. 
  elim (lookup_exists _ _ H0). intros t LOOKUP. 
  apply lookup_inv with t. apply H. auto.
Qed.

Lemma env_weaken_add `{D : EqDec A} {X : Type} (e1 e2 : env A X) x t :
  env_weaken e1 e2 ->
  env_weaken ((x, t) :: e1) ((x, t) :: e2).
Proof.
  intros; red; intros x' t'. simpl; case_var; auto. 
Qed.

Hint Resolve env_weaken_add.

