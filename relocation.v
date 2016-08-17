(** * Trace Relocation *)

Set Implicit Arguments.

Require Import decidable_In.
Require Import extralibrary.
Require Import sublist.
Require Import language_syntax.
Require Import variable_sets.

(** A pseudo-term or a -formula syntactically belongs to infinitely
   many classes. For example, a term [t] from [pterm m] belongs also
   to [pterm k] for all traces [k] including [ov_t (t)] as a sublist.

   - The relocation function is based on the fact that
     the being-in-a-list part is inessential so long as
     the trace contains all the variables needed for
     the construction of an expression e, i.e., [bv (e)]. *)

Fixpoint treloc  m (t: term m) l {struct t} : sub_name (ov_t t) l -> term l :=
  match t return sub_name (ov_t t) l -> term l with
    | Var x _    => fun H => @Var l x (H x (in_eq x nil))
    | Cst c       => fun _ => @Cst l c
    | App f t0 t1 => fun H =>
                     App f (treloc t0 (sub_ov_funL f t0 t1 H)) 
                           (treloc t1 (sub_ov_funR f t0 t1 H))
  end.

Fixpoint freloc m (A: formula m) l {struct A} : sub_name (ov_f A) l -> formula l :=
  match A return sub_name (ov_f A) l -> formula l with
    | Atom (p,t) => fun H =>
                    Atom (p, treloc t (In_inv_atom _ _ H))
    | B --> C    => fun H =>
                    freloc B (In_inv_impL _ _ H) --> freloc C (In_inv_impR _ _ H)
    | Forall x B => fun H =>
                    Forall x (freloc B (In_inv_all _ H))
  end.

(** Relocation is reflexive. *)

Lemma treloc_id : forall m (t: term m) (h:sub_name (ov_t t) m),
  t = treloc t h.
Proof.
  induction t; simpl; intros; f_equal; auto with datatypes. 
Qed.

Lemma freloc_id : forall m (A: formula m) (h:sub_name (ov_f A) m),
  A = freloc A h.
Proof.
  induction A as [m [p t] | |]; simpl; intros; repeat f_equal; auto using treloc_id.
Qed.

Hint Resolve treloc_id freloc_id.
Hint Rewrite <- treloc_id freloc_id : relocation.

(** Repeated application of relocation is equivalent to a single application. *)

Lemma treloc_idempotent : forall m (t:term m) l k
  (h1: sub_name (ov_t t) l)
  (h2: sub_name (ov_t (treloc t h1)) k)
  (h3: sub_name (ov_t t) k),
  treloc t h3 = treloc (treloc t h1) h2.
Proof.
  induction t; simpl; intros; f_equal; auto with datatypes.
Qed.

Lemma freloc_idempotent : forall m (A:formula m) l k
  (h1: sub_name (ov_f A) l)
  (h2: sub_name (ov_f (freloc  A h1)) k)
  (h3: sub_name (ov_f A) k),
  freloc A h3 = freloc (freloc A h1) h2.
Proof.
  induction A as [m [p t]| |]; simpl; intros; f_equal; auto.
  f_equal; auto using treloc_idempotent.
Qed.

Hint Resolve treloc_idempotent freloc_idempotent.
Hint Rewrite <- treloc_idempotent freloc_idempotent : relocation.

(** Equality is preserved by relocation *)

Lemma treloc_eq : forall m (t s :term m) l
  (h1: sub_name (ov_t t) l)
  (h2: sub_name (ov_t s) l),
  t = s ->
  treloc t h1 = treloc s h2.
Proof.
  intros; subst.
  induction s; simpl; f_equal; auto with datatypes.
Qed.

Lemma freloc_eq : forall m (A B :formula m) l
  (h1: sub_name (ov_f A) l)
  (h2: sub_name (ov_f B) l),
  A = B ->
  freloc A h1 = freloc B h2.
Proof.
  intros; subst.
  generalize dependent l.
  induction B as [? [p t] | | ]; simpl; intros; f_equal; auto.
  f_equal; auto using treloc_eq.
Qed.

Hint Resolve treloc_eq freloc_eq.

(** Relocation has no effect upon constants. *)

Lemma treloc_oc : forall m (t:term m) k (h:sub_name (ov_t t) k),
  oc_t t = oc_t (treloc t h).
Proof.
  induction t; simpl; intros; f_equal; auto. 
Qed.

Lemma freloc_oc : forall m (A:formula m) k (h:sub_name (ov_f A) k),
  oc_f A = oc_f (freloc A h).
Proof. 
  induction A as [m [p t] | |]; simpl; intros; f_equal; auto using treloc_oc.
Qed.

Hint Resolve treloc_oc freloc_oc.
Hint Rewrite <- treloc_oc freloc_oc : relocation.

(** Relocation has no effect upon variables. *)

Lemma treloc_bv : forall m (t:term m) k (h:sub_name (ov_t t) k),
  ov_t t = ov_t (treloc t h).
Proof.
  induction t; simpl; intros; f_equal; auto.
Qed.

Lemma freloc_bv : forall m (A:formula m) k (h:sub_name (ov_f A) k),
  ov_f A = ov_f (freloc A h).
Proof.
  induction A as [m [p t] | |]; simpl; intros; f_equal; auto using treloc_bv.
Qed.

Hint Resolve treloc_bv freloc_bv.
Hint Rewrite <- treloc_bv freloc_bv : relocation.

Lemma treloc_ov_1 : forall (t:term nil) m (h: sub_name (ov_t t) m),
  ov_t (treloc t h) = nil.
Proof.
intros; rewrite <- treloc_bv; auto. 
Qed.

Lemma treloc_ov_2 : forall (t:term nil) m (h: sub_name (ov_t t) m),
  forall l, sub_name (ov_t (treloc t h)) l.
Proof.
  intros; rewrite treloc_ov_1; auto with datatypes.
Qed.

Hint Resolve treloc_ov_1 treloc_ov_2.
Hint Rewrite -> treloc_ov_1 : relocation.

Lemma freloc_ov_1 : forall (A:formula nil) m (h: sub_name (ov_f A) m),
  ov_f (freloc A h) = nil.
Proof.
intros; rewrite <- freloc_bv; auto. 
Qed.

Lemma freloc_ov_2 : forall (A:formula nil) m (h: sub_name (ov_f A) m),
  forall l, sub_name (ov_f (freloc A h)) l.
Proof.
  intros; rewrite freloc_ov_1; auto with datatypes. 
Qed.

Hint Resolve freloc_ov_1 freloc_ov_2.
Hint Rewrite -> freloc_ov_1 : relocation.

