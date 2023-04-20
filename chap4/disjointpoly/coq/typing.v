
(*

This file contains the coq formalization
of section 4.2 of thesis.

-> Revised Dsijointness Algorithm

September 21, 2022:
---------------
-> Union + intersection + unit
-> Extended from section 4 of OOPSLA'22 draft 
-> Polymorphism
-> Nominal Types
-> No Disjoint Specs
-> Splitable types and direct disjointness
-> without following rule:
    A * B
  -----------
    A&B * C

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.
(* Require Import Coq.Strings.String. *)

Require Import syntax.

(** definitions *)

(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_int : forall i5,
     value (e_lit i5)
 | val_abs : forall e,
     lc_exp (e_abs e) ->
     value (e_abs e)
 | val_null :
     value e_null
 | val_tabs : forall T e,
     lc_exp (e_tabs T e) ->
     value (e_tabs T e)
 | val_new : forall P,
     value (e_new P).

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit
 | findtype_tabs : forall T e,
     findtype (e_tabs T e) (t_all t_bot t_bot)
 | find_type_new : forall P,
     findtype (e_new P) (t_prim P).

#[export]
Hint Constructors value findtype : core.

(****** Counting Free Variables ******)

(** Computing free type variables in a type *)

Fixpoint fv_tt (T : typ) {struct T} : vars :=
  match T with
  | t_top         => \{}
  | t_int         => \{}
  | t_bot         => \{}
  | t_arrow T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | t_union T1 T2 => (fv_tt T1) \u (fv_tt T2)
  | t_and T1 T2   => (fv_tt T1) \u (fv_tt T2)
  | t_unit        => \{}
  | t_bvar J      => \{}
  | t_fvar X      => \{X}
  | t_all T1 T2   => (fv_tt T1) \u (fv_tt T2)
  | t_prim i      => \{}
  end.

(** Computing free type variables in a term *)

Fixpoint fv_te (e : exp) {struct e} : vars :=
  match e with
  | e_bvar i    => \{}
  | e_fvar x    => \{}
  | e_lit i     => \{} 
  | e_abs e    => fv_te e
  | e_app e1 e2 => (fv_te e1) \u (fv_te e2)
  | e_typeof e A e1 B e2 => (fv_te e) \u (fv_tt A) \u (fv_te e1) \u (fv_tt B) \u (fv_te e2)
  | e_null      => \{}
  | e_tabs V e1 => (fv_tt V) \u (fv_te e1)
  | e_tapp e1 V => (fv_te e1) \u (fv_tt V)
  | e_new i     => \{}
  end.

(** Computing free term variables in a type *)

Fixpoint fv_ee (e : exp) {struct e} : vars :=
  match e with
  | e_bvar i    => \{}
  | e_fvar x    => \{x}
  | e_lit i     => \{}
  | e_abs e    => (fv_ee e)
  | e_app e1 e2 => (fv_ee e1) \u (fv_ee e2)
  | e_typeof e A e1 B e2 => (fv_ee e) \u (fv_ee e1) \u (fv_ee e2)
  | e_null      => \{}
  | e_tabs V e1 => (fv_ee e1)
  | e_tapp e1 V => (fv_ee e1)
  | e_new i     => \{}
  end.


(***** Substitution Functions ******)

(** Substitution for free type variables in types. *)

Fixpoint subst_tt (Z : var) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_top         => t_top
  | t_int         => t_int
  | t_bot         => t_bot
  | t_arrow T1 T2 => t_arrow (subst_tt Z U T1) (subst_tt Z U T2)
  | t_union T1 T2 => t_union (subst_tt Z U T1) (subst_tt Z U T2)
  | t_and T1 T2   => t_and (subst_tt Z U T1) (subst_tt Z U T2)
  | t_unit        => t_unit
  | t_bvar J      => t_bvar J
  | t_fvar X      => If (X = Z) then U else (t_fvar X)
  | t_all T1 T2   => t_all (subst_tt Z U T1) (subst_tt Z U T2)
  | t_prim i      => t_prim i
  end.

(** Substitution for free type variables in terms. *)

Fixpoint subst_te (Z : var) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i    => e_bvar i
  | e_fvar x    => e_fvar x
  | e_lit i     => e_lit i 
  | e_abs e    => e_abs (subst_te Z U e)
  | e_app e1 e2 => e_app (subst_te Z U e1) (subst_te Z U e2)
  | e_typeof e A e1 B e2 => e_typeof (subst_te Z U e) (subst_tt Z U A) (subst_te Z U e1) (subst_tt Z U B) (subst_te Z U e2)
  | e_null      => e_null
  | e_tabs V e1 => e_tabs (subst_tt Z U V)  (subst_te Z U e1)
  | e_tapp e1 V => e_tapp (subst_te Z U e1) (subst_tt Z U V)
  | e_new i     => e_new i
  end.

(** Substitution for free term variables in terms. *)

Fixpoint subst_ee (z : var) (u : exp) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i    => e_bvar i
  | e_fvar x    => If (x = z) then u else e_fvar x
  | e_lit i     => e_lit i 
  | e_abs e    => e_abs (subst_ee z u e)
  | e_app e1 e2 => e_app (subst_ee z u e1) (subst_ee z u e2)
  | e_typeof e A e1 B e2 => e_typeof (subst_ee z u e) A (subst_ee z u e1) B (subst_ee z u e2)
  | e_null      => e_null
  | e_tabs V e1 => e_tabs V  (subst_ee z u e1)
  | e_tapp e1 V => e_tapp (subst_ee z u e1) V
  | e_new i     => e_new i
  end.


(* defns Typing *)
Reserved Notation "PG ; G |= e : A" (at level 80, e at next level, A at next level).
Inductive typing (PG:envp) : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt PG G  ->
      okenvp PG ->
     typing PG G (e_lit i5) t_int
 | typ_null : forall G,
      okt PG G ->
      okenvp PG ->
      typing PG G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt PG G ->
      okenvp PG ->
      binds x (bind_typ A) G  ->
      typing PG G (e_fvar x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     typing PG G e1 (t_arrow A B) ->
     typing PG G e2 A ->
     typing PG G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing PG G e B ->
     sub PG G B A ->
     typing PG G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okt PG G ->
      okenvp PG ->
      ( forall x , x \notin  L  -> typing PG (G & x ~: A) (open_ee e (e_fvar x)) B)  ->
     typing PG G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing PG G e (t_union A B) ->
     ( forall x ,x \notin  L -> typing PG (G & x ~: A ) (open_ee e1 (e_fvar x) ) C) ->
     ( forall x ,x \notin  L -> typing PG (G & x ~: B ) (open_ee e2 (e_fvar x) ) C) ->
     (PG ; G |= A *a B) ->
     typing PG G (e_typeof e A e1 B e2) C
 | typ_inter : forall G e A B,
     typing PG G e A ->
     typing PG G e B ->
     typing PG G e (t_and A B)
 | typ_tabs : forall L G e A B,
     okt PG G ->
     okenvp PG ->
     (forall X, X \notin L ->
      typing PG (G & X ~*: A) (e open_te_var X) (B open_tt_var X)) ->
      typing PG G (e_tabs A e) (t_all A B)
 | typ_tapp : forall G e A B C,
     typing PG G e (t_all B C) ->
     PG ; G |= A *a B ->
     typing PG G (e_tapp e A) (open_tt C A)
 | typ_prim : forall G i,
     okt PG G ->
     okenvp PG ->
     wft PG G (t_prim i) ->
     typing PG G (e_new i) (t_prim i)
where "PG ; G |= e : A" := (typing PG G e A).


(* defns Reduction *)
Reserved Notation "PG ; G |= e --> e'" (at level 80, e at next level, e' at next level).
Inductive step (PG:envp) (G:env) : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step PG G e1 e1' ->
     step PG G (e_app e1 e2) (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     step PG G e e' ->
     step PG G (e_app v e) (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     step PG G (e_app (e_abs e) v) (open_ee e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     step PG G e e' ->
     step PG G (e_typeof e A e1 B e2) (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub PG G C A ->
     step PG G (e_typeof v A e1 B e2) (open_ee e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub PG G C B ->
     step PG G (e_typeof v A e1 B e2) (open_ee  e2 v )
 | step_tapp : forall e e' A,
      type A ->
      step PG G e e' ->
      step PG G (e_tapp e A) (e_tapp e' A)
 | step_tabs : forall A e B,
      lc_exp (e_tabs A e) ->
      type B ->
      step PG G (e_tapp (e_tabs A e) B) (open_te e B)
where "PG ; G |= e --> e'" := (step PG G e e') : env_scope.

#[export]
Hint Constructors typing step : core.

(** Gathering free names already used in the proofs **)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : exp => fv_ee x) in
  let D := gather_vars_with (fun x : exp => fv_te x) in
  let E := gather_vars_with (fun x : typ => fv_tt x) in
  let F := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D \u E \u F).

(** "pick_fresh x" tactic create a fresh variable with name x *)

Ltac pick_fresh x :=
  let L := gather_vars in (pick_fresh_gen L x).

(** "apply_fresh T as x" is used to apply inductive rule which
   use an universal quantification over a cofinite set *)

Tactic Notation "apply_fresh" constr(T) "as" ident(x) :=
  apply_fresh_base T gather_vars x.

Tactic Notation "apply_fresh" "*" constr(T) "as" ident(x) :=
  apply_fresh T as x; autos*.

(** These tactics help applying a lemma which conclusion mentions
  an environment (E & F) in the particular case when F is empty *)

Ltac get_env :=
  match goal with
  | |- sub _ ?E _ _  => E
  | |- typing _ ?E _ _ => E
  end.

Tactic Notation "apply_empty_bis" tactic(get_env) constr(lemma) :=
  let E := get_env in rewrite <- (concat_empty_r E);
  eapply lemma; try rewrite concat_empty_r.

Tactic Notation "apply_empty" constr(F) :=
  apply_empty_bis (get_env) F.

Tactic Notation "apply_empty" "*" constr(F) :=
  apply_empty F; autos*.

(** Tactic to undo when Coq does too much simplification *)

Definition subst_tb (Z : var) (P : typ) (b : bind) : bind :=
  match b with
  | bind_disj T => bind_disj (subst_tt Z P T)
  | bind_typ T => bind_typ (subst_tt Z P T)
  end.

Ltac unsimpl_map_bind :=
  match goal with |- context [ ?B (subst_tt ?Z ?P ?U) ] =>
    unsimpl ((subst_tb Z P) (B U)) end.

Tactic Notation "unsimpl_map_bind" "*" :=
  unsimpl_map_bind; autos*.

(* ********************************************************************** *)
(** * Properties of Substitutions *)

(* ********************************************************************** *)
(** ** Properties of type substitution in types *)

(** The next lemma is the strengthened induction hypothesis for the
    lemma that follows, which states that opening a locally closed
    term is the identity.  This lemma is not otherwise independently
    useful. *)

Lemma open_tt_rec_type_aux : forall T j V i U,
  i <> j ->
  open_tt_rec j V T = open_tt_rec i U (open_tt_rec j V T) ->
  T = open_tt_rec i U T.
Proof with congruence || eauto.
  induction T; intros j V i U Neq H; simpl in *; inversion H; f_equal...
  case_nat...  case_nat...
Qed.

(** Opening a locally closed term is the identity.  This lemma depends
    on the immediately preceding lemma. *)

Lemma open_tt_rec_type : forall T U k,
  type T ->
  T = open_tt_rec k U T.
Proof with auto.
  intros T U k Htyp. revert k.
  induction Htyp; intros k; simpl; f_equal...
    unfold open_tt in *.
    pick_fresh X.
    apply (open_tt_rec_type_aux T2 0 (t_fvar X))...
Qed.


(** Substitution for a fresh name is identity. *)

Lemma subst_tt_fresh : forall Z U T,
  Z \notin fv_tt T -> subst_tt Z U T = T.
Proof.
  induction T; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution commutes with opening under certain conditions.  This
    lemma depends on the fact that opening a locally closed term is
    the identity. *)

Lemma subst_tt_open_tt_rec : forall T1 T2 X P k,
  type P ->
  subst_tt X P (open_tt_rec k T2 T1) =
    open_tt_rec k (subst_tt X P T2) (subst_tt X P T1).
Proof with auto.
  intros T1 T2 X P k WP. revert k.
  induction T1; intros k; simpl; f_equal...
  case_nat; subst...
  case_var; subst... apply open_tt_rec_type...
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_tt_open_tt : forall T1 T2 X P, type P ->
  subst_tt X P (open_tt T1 T2) =
  open_tt (subst_tt X P T1) (subst_tt X P T2).
Proof.
  unfold open_tt. intros. apply subst_tt_open_tt_rec; auto.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_tt_open_tt_var : forall X Y U T, Y <> X -> type U ->
  (subst_tt X U T) open_tt_var Y = subst_tt X U (T open_tt_var Y).
Proof.
  introv Neq Wu. rewrite* subst_tt_open_tt.
  simpl. case_var*.
Qed.

Lemma subst_tt_intro_rec : forall X T2 U k,
  X \notin fv_tt T2 ->
  open_tt_rec k U T2 = subst_tt X U (open_tt_rec k (t_fvar X) T2).
Proof with congruence || auto.
  induction T2; intros U k Fr; simpl in *; f_equal...
  case_nat... simpl. case_var...
  case_var...
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_tt_intro : forall X T2 U, 
  X \notin fv_tt T2 -> type U ->
  open_tt T2 U = subst_tt X U (T2 open_tt_var X).
Proof.
  introv Fr Wu. rewrite* subst_tt_open_tt.
  rewrite* subst_tt_fresh. simpl. case_var*.
Qed.

(* ********************************************************************** *)
(** ** Properties of type substitution in terms *)

Lemma open_te_rec_expr_aux : forall e j u i P ,
  open_ee_rec j u e = open_te_rec i P (open_ee_rec j u e) ->
  e = open_te_rec i P e.
Proof with congruence || eauto.
  induction e; intros j u i P H; simpl in *; inversion H; f_equal...
Qed.

Lemma open_te_rec_type_aux : forall e j Q i P,
  i <> j ->
  open_te_rec j Q e = open_te_rec i P (open_te_rec j Q e) ->
  e = open_te_rec i P e.
Proof.
  induction e; intros j Q i P Neq Heq; simpl in *; inversion Heq;
    f_equal; eauto using open_tt_rec_type_aux.
Qed.

Lemma open_te_rec_expr : forall e U k,
  lc_exp e ->
  e = open_te_rec k U e.
Proof.
  intros e U k WF. revert k.
  induction WF; intros k; simpl; f_equal; auto using open_tt_rec_type;
  try solve [
    unfold open_ee in *;
    pick_fresh x;
    eapply open_te_rec_expr_aux with (j := 0) (u := e_fvar x);
    auto
  | unfold open_te in *;
    pick_fresh X;
    eapply open_te_rec_type_aux with (j := 0) (Q := t_fvar X);
    auto
  ].
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_te_fresh : forall X U e,
  X \notin fv_te e -> subst_te X U e = e.
Proof.
  induction e; simpl; intros; f_equal*; apply* subst_tt_fresh.
Qed.

Lemma subst_te_open_te_rec : forall e T X U k,
  type U ->
  subst_te X U (open_te_rec k T e) =
    open_te_rec k (subst_tt X U T) (subst_te X U e).
Proof.
  intros e T X U k WU. revert k.
  induction e; intros k; simpl; f_equal; auto using subst_tt_open_tt_rec.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_te_open_te : forall e T X U, type U ->
  subst_te X U (open_te e T) =
  open_te (subst_te X U e) (subst_tt X U T).
Proof.
  intros. unfold open_te. generalize 0.
  induction e; intros; simpls; f_equal*;
  apply* subst_tt_open_tt_rec.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_te_open_te_var : forall X Y U e, Y <> X -> type U ->
  (subst_te X U e) open_te_var Y = subst_te X U (e open_te_var Y).
Proof.
  introv Neq Wu. rewrite* subst_te_open_te.
  simpl. case_var*.
Qed.

Lemma subst_te_intro_rec : forall X e U k,
  X \notin fv_te e ->
  open_te_rec k U e = subst_te X U (open_te_rec k (t_fvar X) e).
Proof.
  induction e; intros U k Fr; simpl in *; f_equal;
    auto using subst_tt_intro_rec.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_te_intro : forall X U e, 
  X \notin fv_te e -> type U ->
  open_te e U = subst_te X U (e open_te_var X).
Proof.
  introv Fr Wu. rewrite* subst_te_open_te.
  rewrite* subst_te_fresh. simpl. case_var*.
Qed.


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
Qed.

Lemma open_ee_rec_type_aux : forall e j V u i,
  open_te_rec j V e = open_ee_rec i u (open_te_rec j V e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; intros j V u i H; simpl; inversion H; f_equal; eauto.
Qed.

Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_ee_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_ee_rec. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_fvar x)).
  unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (e_fvar x)).
  unfolds open_ee. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_fvar x)).
  unfolds open_te. pick_fresh X.
   apply* (@open_ee_rec_type_aux e1 0 (t_fvar X)).
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_ee e -> subst_ee x u e = e.
Proof.
  induction e; simpl; intros; f_equal*.
  case_var*.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_ee x u (open_ee t1 t2) =
open_ee (subst_ee x u t1) (subst_ee x u t2).
Proof.
  intros. unfold open_ee. generalize 0.
  induction t1; intros; simpls; f_equal*.
  case_nat*.
  case_var*. rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_ee x u e) open_ee_var y = subst_ee x u (e open_ee_var y).
Proof.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl. case_var*.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_ee e -> lc_exp u ->
  open_ee e u = subst_ee x u (e open_ee_var x).
Proof.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl. case_var*.
Qed.

(** Interactions between type substitutions in terms and opening
  with term variables in terms. *)

  Lemma subst_te_open_ee_var : forall Z P x e,
  (subst_te Z P e) open_ee_var x = subst_te Z P (e open_ee_var x).
Proof.
  introv. unfold open_ee. generalize 0.
  induction e; intros; simpl; f_equal*. case_nat*.
Qed.

(** Interactions between term substitutions in terms and opening
  with type variables in terms. *)

Lemma subst_ee_open_te_var : forall z u e X, lc_exp u ->
  (subst_ee z u e) open_te_var X = subst_ee z u (e open_te_var X).
Proof.
  introv. unfold open_te. generalize 0.
  induction e; intros; simpl; f_equal*.
  case_var*. symmetry. apply* open_te_rec_expr.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_tt_type : forall T Z P,
  type T -> type P -> type (subst_tt Z P T).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
  apply_fresh* type_all as X. rewrite* subst_tt_open_tt_var.
Qed.

Lemma subst_te_term : forall e Z P,
  lc_exp e -> type P -> lc_exp (subst_te Z P e).
Proof.
  puts: subst_tt_type. induction 1; intros; simpl; auto.
  apply_fresh* lc_e_abs as x. rewrite* subst_te_open_ee_var.
  apply_fresh* lc_e_typeof as x. rewrite* subst_te_open_ee_var.
  rewrite* subst_te_open_ee_var.
  apply_fresh* lc_e_tabs as X. rewrite* subst_te_open_te_var.
Qed.

Lemma subst_ee_term : forall e1 Z e2,
lc_exp e1 -> lc_exp e2 -> lc_exp (subst_ee Z e2 e1).
Proof.
  induction 1; intros; simpl; auto.
  case_var*.
 - apply_fresh* lc_e_abs as y.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* lc_e_typeof as y.
   rewrite* subst_ee_open_ee_var.
   rewrite* subst_ee_open_ee_var.
 - apply_fresh* lc_e_tabs as X.
   rewrite* subst_ee_open_te_var.
Qed.

#[export]
Hint Resolve subst_ee_term subst_te_term subst_tt_type : core.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall PG E,
  okt PG E -> ok E.
Proof.
  induction 1. auto. auto. auto.
Qed.

#[export]
Hint Extern 1 (ok _) => apply (ok_from_okt _ _) : core.

(** Through weakening *)

Lemma wft_weaken : forall PG G T E F,
  wft PG (E & G) T ->
  ok (E & F & G) ->
  wft PG (E & F & G) T.
Proof.
  intros. gen_eq : (E & G) as K. gen E F G.
  induction H; intros; subst; eauto.
  (* case: var *)
  apply (@wft_var PG U). apply* binds_weaken.
  (* case: all *)
  pick_fresh Y.
  apply wft_all with 
  (L:=(((((L \u fv_tt T1) \u fv_tt T2) \u dom E0) \u dom G) \u dom F)); auto.
  intros. apply_ih_bind* H1.
  (* apply_fresh* wft_all as Y. apply_ih_bind* H1. *)
Qed.

Lemma wft_weaken_right : forall PG T E F,
  wft PG E T ->
  ok (E & F) ->
  wft PG (E & F) T.
Proof.
  intros.
  assert (E & F & empty = E & F).
  rewrite~ concat_empty_r.
  rewrite <- H1 in *.
  assert (E = E & empty).
  rewrite~ concat_empty_r.
  rewrite H2 in H.
  apply~ wft_weaken.
Qed.

Lemma append_empty_right : forall (E : env),
  E = E & empty.
Proof.
  intros.
  rewrite~ concat_empty_r.
Qed.

(** Extraction from a disjointness assumption in a well-formed environments *)

Lemma wft_from_env_has_sub : forall PG x U E,
  okt PG E -> binds x (bind_disj U) E -> wft PG E U.
Proof.
  unfold binds. introv OK.
  induction OK; introv B.
  - rewrite get_empty in B.
    inverts B.
  - rewrite get_push in B.
    case_var.
    forwards* : IHOK B.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
  - rewrite get_push in B.
    case_var.
    inverts B.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
    forwards* : IHOK B.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
Qed.


(** Extraction from a typing assumption in a well-formed environments *)

Lemma wft_from_env_has_typ : forall PG x U E,
  okt PG E -> binds x (bind_typ U) E -> wft PG E U.
Proof.
  unfold binds. introv OK.
  induction OK; introv B.
  - rewrite get_empty in B.
    inverts B.
  - rewrite get_push in B.
    case_var.
    inverts B.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
    forwards* : IHOK B.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
  - rewrite get_push in B.
    case_var.
    apply* wft_weaken_right.
    apply ok_from_okt in OK; auto.
Qed.

(** Automation *)

(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** If a type is well-formed in an environment then it is locally closed. *)

Lemma type_from_wft : forall PG E T,
  wft PG E T -> type T.
Proof.
  induction 1; eauto. 
Qed.

(** Through narrowing *)

Lemma wft_narrow : forall PG V F U T E X,
  wft PG (E & X ~*: V & F) T ->
  okt PG (E & X ~*: U & F) -> 
  wft PG (E & X ~*: U & F) T.
Proof.
  intros. gen_eq : (E & X ~*: V & F) as K. gen E F.
  induction H; intros; subst; eauto.
  binds_cases H.
    eapply wft_var. apply* binds_concat_left_ok.
    apply ok_from_okt in H0; auto.
     apply (@wft_var PG U). apply* binds_middle_eq.
    eapply wft_var. apply* binds_concat_right.
  pick_fresh Y.
  apply wft_all with (L:=(((((((L \u \{ X}) \u fv_tt V) \u fv_tt U) \u fv_tt T1) \u fv_tt T2) \u
  dom E0) \u dom F)); auto. 
  intros. apply_ih_bind* H1.
Qed.

(** Through strengthening *)

Lemma wft_strengthen : forall PG E F x U T,
 wft PG (E & x ~: U & F) T -> wft PG (E & F) T.
Proof.
  intros. gen_eq : (E & x ~: U & F) as G. gen F.
  induction H; intros F EQ; subst; auto.
  apply* (@wft_var PG U0). binds_cases H; try discriminate; autos*.
  pick_fresh Y.
  apply wft_all with (L:=((((((L \u \{ x}) \u fv_tt U) \u fv_tt T1) \u fv_tt T2) \u dom E) \u
  dom F)); auto.
  intros. apply_ih_bind* H1.
Qed.

(** Through type substitution *)

(** Inversion lemma *)

Lemma okt_push_inv : forall PG E x T,
  okt PG (E & x ~: T) -> okt PG E /\ x # E /\ wft PG E T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). inverts M. subst. autos.
    lets (?&M&?): (eq_push_inv H). inverts M.
Qed.

Lemma okt_push_inv_tt : forall PG E X T,
  okt PG (E & X ~*: T) -> okt PG E /\ X # E /\ wft PG E T.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). inverts M.
    lets (?&M&?): (eq_push_inv H). inverts M. subst. autos.
Qed.

#[export]
Hint Resolve wft_weaken_right : core.

#[export]
Hint Immediate wft_from_env_has_sub wft_from_env_has_typ : core.

#[export]
Hint Resolve okt_push_inv okt_push_inv_tt : core.

(** Through narrowing *)

Lemma okt_narrow : forall PG V E F U X,
  okt PG (E & X ~*: V & F) ->
  wft PG E U ->
  okt PG (E & X ~*: U & F).
Proof.
  induction F using env_ind; intros.
  rewrite <- append_empty_right in *.
  apply okt_push_inv_tt in H. destructs H.
  apply* okt_disj.
  destruct v.
  rewrite concat_assoc in *.
  apply okt_push_inv_tt in H. destructs H.
  apply* okt_disj.
  apply* wft_narrow.
  rewrite concat_assoc in *.
  apply okt_push_inv in H. destructs H.
  apply* okt_typ.
  apply* wft_narrow.
Qed.

(** Through strengthening *)

Lemma okt_strengthen : forall PG x T (E F : env),
  okt PG (E & x ~: T & F) ->
  okt PG (E & F).
Proof.
  introv O. induction F using env_ind.
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
  rewrite concat_assoc in *.
  destruct v.
  apply okt_push_inv_tt in O. destructs O.
  apply okt_disj; auto.
  apply wft_strengthen in H1; auto. 
  apply okt_push_inv in O. destructs O.
  apply okt_typ; auto.
  apply wft_strengthen in H1; auto.
Qed.

Lemma okt_concat_inv : forall PG E F x V,
  okt PG (E & (x ~: V) & F) -> okt PG E /\ x # E /\ wft PG E V.
Proof.
  intros PG E F. gen PG E.
  induction F using env_ind; introv; rew_env_concat; auto; introv ok.
  destruct v.
  apply okt_push_inv_tt in ok.
  destruct ok.
  forwards*: IHF H.
  apply okt_push_inv in ok.
  destruct ok.
  forwards*: IHF H.
Qed.

Lemma okt_concat_inv_tt : forall PG E F X V,
  okt PG (E & (X ~*: V) & F) -> okt PG E /\ X # E /\ X # F /\ wft PG E V.
Proof.
  intros PG E F. gen PG E.
  induction F using env_ind; introv; rew_env_concat; auto; introv ok.
  apply okt_push_inv_tt in ok. split*.
  destruct v.
  apply okt_push_inv_tt in ok.
  destruct ok.
  forwards*: IHF H.
  apply okt_push_inv in ok.
  destruct ok.
  forwards*: IHF H.
Qed.


(** Automation *)

#[export]
Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The subtyping relation is restricted to well-formed objects. *)

Lemma sub_regular : forall PG E S T,
  sub PG E S T -> okenvp PG /\ wft PG E S /\ wft PG E T /\ okt PG E.
Proof.
  induction 1; autos*.
  (*all case*)
  split*. splits.
  - pick_fresh Y.
    apply wft_all with (L:=(((((L \u fv_tt S1) \u fv_tt S2) \u fv_tt T1) \u fv_tt T2) \u dom G)); auto. 
    destructs~ IHsub.
    intros. destructs~ (H1 X).
    rewrite (append_empty_right (G & X ~*: S1)).
    eapply wft_narrow with (V:=T1).
    rewrite~ <- append_empty_right.
    rewrite~ <- append_empty_right.
    apply* okt_disj.
  - pick_fresh Y.
    apply wft_all with (L:=(((((L \u fv_tt S1) \u fv_tt S2) \u fv_tt T1) \u fv_tt T2) \u dom G)); auto.
    destructs~ IHsub.
    forwards* (_&_&_&ok): H1 Y.
    apply okt_push_inv_tt in ok.
    destructs~ ok. 
    intros. destruct~ (H1 X).
    rewrite (append_empty_right (G & X ~*: T1)).
    destructs H7.
    rewrite~ concat_empty_r.
  -  destructs IHsub; auto.
Qed.

(* Regularity of disjointness *)

Lemma disj_regular : forall PG E A B,
  Disj PG E A B ->
  okenvp PG /\ okt PG E /\ wft PG E A /\ wft PG E B.
Proof.
  introv Disj.
  induction Disj; eauto.
  all: autos*.
  all: forwards*: sub_regular H0.
Qed.

Require Import TLC.LibEnv.

Lemma notin_fv_tt_open : forall Y X T,
  X \notin fv_tt (T open_tt_var Y) ->
  X \notin fv_tt T.
Proof.
 intros Y X T. unfold open_tt.
 generalize 0.
 induction T; simpl; intros k Fr; eauto.
 apply notin_union in Fr. destruct~ Fr. notin_simpl; eauto.
 apply notin_union in Fr. destruct~ Fr. notin_simpl; eauto.
 apply notin_union in Fr. destruct~ Fr. notin_simpl; eauto.
 apply notin_union in Fr. destruct~ Fr. notin_simpl; eauto.
Qed.

(**************************************************************)
(** Substitution in a ground type returns ground type *)


Lemma wft_subst_tb : forall PG F Q E Z P T,
  wft PG (E & Z ~*: Q & F) T ->
  wft PG E P ->
  ok (E & map (subst_tb Z P) F) ->
  wft PG (E & map (subst_tb Z P) F) (subst_tt Z P T).
Proof.
  introv WT WP. gen_eq : (E & Z ~*: Q & F) as G. gen F.
  induction WT; intros F EQ Ok; subst; simpl subst_tt; auto.
  case_var*.
    binds_cases H. 
      apply* wft_var.
      apply (@wft_var PG (subst_tt Z P U)). unsimpl_map_bind*.
  pick_fresh Y.
  apply wft_all with (L:=(((((((L \u \{ Z}) \u fv_tt Q) 
    \u fv_tt P) \u fv_tt T1) \u fv_tt T2) \u dom E) \u dom F)); intros; auto.
   forwards*: type_from_wft WP.
   unsimpl ((subst_tb Z P) (bind_disj T1)).
   puts : type_from_wft.
   rewrite*  subst_tt_open_tt_var.
   apply_ih_map_bind* H0.
Qed.

(** Through type reduction *)

Lemma wft_open : forall PG E U T1 T2,
  ok E ->
  wft PG E (t_all T1 T2) -> 
  wft PG E U ->
  wft PG E (open_tt T2 U).
Proof.
  introv Ok WA WU. inversions WA. pick_fresh X. 
  puts : type_from_wft. rewrite* (@subst_tt_intro X).
  forwards* K: (@wft_subst_tb PG empty T1 E X U (T2 open_tt_var X)).
  forwards* : H3 X. rewrite~ concat_empty_r.
  rewrite map_empty. rewrite~ concat_empty_r.
  rewrite map_empty in K. rewrite~ concat_empty_r in K.
Qed.

Lemma typing_regular : forall PG E e T,
  typing PG E e T -> okenvp PG /\ okt PG E /\ lc_exp e /\ wft PG E T.
Proof.
  induction 1; try splits*.
  - (*case arrow*)
    destructs IHtyping1. inverts* H4.
  - (*case subsumption*)
    apply sub_regular in H0. destructs~ H0.
  (* - pick_fresh y. specializes H0 y. destructs~ H0.
   apply okt_push_inv in H0. destruct H0. auto. *)
 - (*case abs*)
   apply lc_e_abs with (L:=L). intros.
   specializes H2 x. destructs~ H2.
 - (*case abs*)
   pick_fresh x.
   forwards* : H2 x. destructs H3.
   apply okt_push_inv in H4. destructs H4.
   rewrite (append_empty_right ((G & x ~: A))) in H6.
   apply wft_strengthen in H6.
   rewrite~ <- append_empty_right in H6.
 - (*case typeof*)
   apply lc_e_typeof with (L:=L); intros. destructs~ IHtyping.
   destructs~ IHtyping. inverts H8.
   apply type_from_wft with (PG:=PG) (E:=G); auto.
   destructs~ IHtyping. inverts H8.
   apply type_from_wft with (PG:=PG) (E:=G); auto.
   forwards* (?&?&?): H1 x.
   forwards* (?&?): H3 x.
 - (*case tabs*)
   pick_fresh x.
   forwards*(?&?&?&?): H1 x.
   rewrite (@append_empty_right (G & x ~: A)) in H8.
   apply wft_strengthen in H8.
   rewrite~ <- append_empty_right in H8.
 (* - pick_fresh X. specializes H0 X. destructs~ H0.
  apply okt_push_inv_tt in H0. destruct H0. auto. *)  
 - apply_fresh lc_e_tabs as X.
   pick_fresh X.
   forwards* (?&?&?&?): H2 X.
   apply okt_push_inv_tt in H4. destructs H4.
   apply type_from_wft in H8; auto.
   forwards* : H2 X.
 - pick_fresh Y.
   apply wft_all with (L:=(((((L \u fv_ee e) \u fv_te e) \u fv_tt A) \u fv_tt B) \u dom G)); auto.
   forwards*(?&?&?&?): H2 Y.
   apply okt_push_inv_tt in H4. destructs~ H4.
   forwards*(_&okt&_): H2 Y.
   apply okt_push_inv_tt in okt. destructs~ okt.
   intros. forwards*(?&?&?&?): H2 X.
 - apply lc_e_tapp. destructs~ IHtyping.
   apply disj_regular in H0.
   destructs H0.
   apply type_from_wft in H2; auto.
 - destructs~ IHtyping.
   forwards* (okp&_&WFA&_): disj_regular H0.
   apply ok_from_okt in H2.
   forwards*: wft_open H2 H4 WFA.
Qed.

(** The value relation is restricted to well-formed objects. *)

Lemma value_regular : forall t,
  value t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

#[export]
Hint Immediate value_regular : core.

(** The reduction relation is restricted to well-formed objects. *)

Lemma step_regular : forall PG E t t',
  step PG E t t' -> lc_exp t /\ lc_exp t'.
Proof.
  induction 1; split*.
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
  - inverts H. destructs IHstep.
    apply_fresh* lc_e_typeof as y.
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
  - inverts H. pick_fresh Y. rewrite* (@subst_te_intro Y).
Qed.

(** Automation *)

#[export]
Hint Extern 1 (okt ?PG ?E) =>
  match goal with
  | H: sub _ _ _ _ |- _ => apply (proj31 (sub_regular H))
  | H: typing _ _ _ _ |- _ => apply (proj31 (typing_regular H))
  end : core.

#[export]
Hint Extern 1 (wft ?PG ?E ?T) =>
  match goal with
  | H: typing PG E _ T |- _ => apply (proj33 (typing_regular H))
  | H: sub PG E T _ |- _ => apply (proj32 (sub_regular H))
  | H: sub PG E _ T |- _ => apply (proj33 (sub_regular H))
  end : core.

#[export]
Hint Extern 1 (type ?T) =>
  let go PG E := apply (@type_from_wft PG E); auto in
  match goal with
  | H: typing _ ?E _ T |- _ => go E
  | H: sub _ ?E T _ |- _ => go E
  | H: sub _ ?E _ T |- _ => go E
  end : core.

#[export]
Hint Extern 1 (lc_exp ?e) =>
  match goal with
  | H: typing _ _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: step _ _ ?e _ |- _ => apply (proj1 (step_regular H))
  | H: step _ _ _ ?e |- _ => apply (proj2 (step_regular H))
  end : core.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

(*********** Subtyping Reflexivity **********)

Lemma sub_refl : forall (PG:envp) G (A:typ), 
  okt PG G ->
  okenvp PG ->
  wft PG G A -> 
  sub PG G A A.
Proof.
  introv OK OKP WF. induction WF; eauto.
  apply* s_ora.
  apply* s_anda.
  pick_fresh Y.
  apply s_all with (L:=(((L \u fv_tt T1) \u fv_tt T2) \u dom E)); auto.
Defined.

#[export]
Hint Resolve sub_refl : core.

#[export]
Hint Resolve wft_narrow : core.

(*********** Subtyping Transitivity **********)

Lemma sub_narrowing_aux : forall PG Q F E Z P S T,
  sub PG (E & Z ~*: P & F) S T ->
  sub PG E P Q ->
  okt PG (E & Z ~*: Q & F) ->
  sub PG (E & Z ~*: Q & F) S T.
Proof.
  introv SsubT PsubQ Ok.
  gen_eq : (E & Z ~*: P & F) as G. gen F P Q.
  forwards*: sub_regular SsubT. destructs H.
  induction SsubT; introv SsubQ EQ Ok; subst; try (forwards*: sub_regular SsubQ).
  - (*case arrow*)
    forwards*: sub_regular SsubT1.
    forwards*: sub_regular SsubT2.
  - (*case A1 | A2 <: A*)
    forwards*: sub_regular SsubT1.
    forwards*: sub_regular SsubT2.
  - (*case A <: A1*)
    forwards*: sub_regular SsubT.
  - (*case A <: A2*)
    forwards*: sub_regular SsubT.
  - (*case A <: A1 & A2*)
    forwards*: sub_regular SsubT1.
    forwards*: sub_regular SsubT2.
  - (*case A1 <: A*)
    forwards*: sub_regular SsubT.
  - (*case A2 <: A*)
    forwards*: sub_regular SsubT.
  - (*case All*)
    apply s_all with (L:=L).
    forwards*: sub_regular SsubT.
    intros. 
    forwards*: H3 X. inverts H0.
    apply sub_regular in H7. destructs H7.
    forwards*: H4 X (F & X ~*: T1) P Q.
    rewrite~ concat_assoc.
    apply okt_push_inv_tt in H9.
    destructs H9.
    apply* okt_disj.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc in H10.
Qed.

(***********************************************

Supertypes properties for subtyping transitivity

************************************************)

Lemma getsubtypes_inversion_temp12 : forall (PG : envp),
  forall (n1 i : nat) (A B:typ),
  set_In n1 (get_all_subtypes ((i , A) :: PG) B) ->
  ((n1 = i) /\ (issupertype ((i, A) :: PG) (t_prim i) B = true) ) 
  \/ set_In n1 (get_all_subtypes PG B).
Proof.
   destruct PG; intros.
  - simpl in H. destruct (eq_dec B A).
    destruct (eq_dec_nat i i); simpl in H.
    destruct H. left. split. auto.
    subst. simpl.
    destruct (eq_dec A A).
    destruct (eq_dec_nat n1 n1); simpl.
    auto. contradiction.
    contradiction.
    inverts H. contradiction.
    destruct (eq_dec_nat i i); simpl in H.
    inverts H. inverts H.
  - destruct p as [j C].
    simpl.

    simpl in H. destruct (eq_dec B C).

    destruct (eq_dec B A).
    destruct  (eq_dec_nat i i).
    simpl in H.
    destruct H; auto.
    contradiction.
    destruct  (eq_dec_nat j j).
    destruct  (eq_dec_nat i j).
    simpl in H. simpl.
    destruct (eq_dec A (t_prim j)).
    destruct (eq_dec_nat i i); simpl in *.
    destruct H; auto.
    contradiction.
    destruct (eq_dec_nat i i); simpl in *.
    subst.
    destruct (issupertype PG A C).
    simpl in H. destruct H; auto.
    simpl in H. destruct H; auto.
    contradiction.
    destruct ((eq_dec_nat i i)); simpl in H.
    destruct (eq_dec A (t_prim j)); simpl in *.
    destruct H; auto.
    subst.
    destruct (issupertype PG A C); simpl in *.
    destruct H; auto.
    destruct H; auto.
    contradiction.
    contradiction.

    destruct (eq_dec B A).
    destruct (eq_dec_nat i i); simpl in *.
    destruct ((eq_dec_nat j j)); simpl in *.
    destruct H; auto.
    contradiction.
    contradiction.

    destruct (eq_dec_nat i i); simpl in *.
    destruct (eq_dec_nat j j); simpl in *.
    destruct (eq_dec A (t_prim j)); simpl in *.
    destruct (issupertype PG C B); simpl in *.
    destruct H; auto.
    auto.
    destruct (issupertype PG A B); simpl in *.
    destruct H; auto.
    destruct (issupertype PG C B); simpl in *.
    destruct H; auto.
    auto.
    contradiction.
    contradiction.
Qed.

Lemma nats_to_types_iff : forall i l,
  set_In i l <-> set_In (t_prim i) (nats_to_types l).
Proof.
  split.
  - gen i. induction l; intros.
    inverts H.
    simpl. simpl in H.
    destruct H.
    auto. auto.
  - gen i. induction l; intros.
    inverts H.
    simpl in H. simpl.
    destruct H.
    inverts H. auto.
    forwards*: IHl H.
Qed.

Lemma subpertypes_inversion : forall PG,
  forall i n,
  issupertype PG (t_prim i) (t_prim n) = true ->
  set_In i (get_all_subtypes PG (t_prim n)).
Proof.
  induction PG; introv EQ.
  - inverts EQ.
  - destruct a as [j A].
    destruct A; simpl in *.
   + (*case top*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_top (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_top (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case int*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_int (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_int (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case bot*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_bot (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_bot (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case arrow*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_arrow A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_arrow A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case union*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_union A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_union A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case intersection*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_and A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_and A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case unit*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_unit (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG t_unit (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case bvar*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_bvar n0) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_bvar n0) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case fvar*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_fvar v) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_fvar v) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (*case all*)
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_all A1 A2) (t_prim n)); simpl in *.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_all A1 A2) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
   + (* case P *)
     destruct (eq_dec_nat n n0); simpl in *.
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     auto.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     forwards*: IHPG EQ.
     contradiction.
     destruct (eq_dec_nat i j); simpl in *.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_prim n0) (t_prim n)); simpl.
     auto.
     inverts EQ.
     contradiction.
     destruct (eq_dec_nat j j); simpl.
     destruct (issupertype PG (t_prim n0) (t_prim n)); simpl.
     forwards*: IHPG EQ.
     forwards*: IHPG EQ.
     contradiction.
Defined.

Lemma issupertype_inverse : forall PG i A n,
  issupertype ((i, A) :: PG) (t_prim i) (t_prim n) = true ->
  A = (t_prim n) \/ issupertype PG A (t_prim n) = true.
Proof.
  destruct PG; intros.
  - destruct A; simpl in *;
    try solve [destruct (eq_dec_nat i i); simpl in *;
    inverts H].
    destruct (eq_dec_nat n n0); simpl in *.
    destruct (eq_dec_nat i i); simpl in *.
    auto. contradiction.
    destruct (eq_dec_nat i i); simpl in *.
    inverts H.  contradiction.
  - destruct p as [j C].
    destruct A;
    (*all cases except P*)
    destruct C; simpl in *; 
    try solve [
    destruct (eq_dec_nat i j); simpl in *;
    destruct (eq_dec_nat i i); simpl in *;
    auto; contradiction;
    destruct (eq_dec_nat i i); simpl in *;
    auto; contradiction].

    + (*case A = top, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = int, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = bot, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = arrow, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = union, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = intersection, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = unit, C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = (t_bvar n1), C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = (t_fvar v), C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = (t_all C1 C2), C = P*)
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *.
      subst. auto.
      contradiction.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

    + (*case A = P, C = P*)
      destruct (eq_dec_nat n n1); simpl in *.
      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

      destruct (eq_dec_nat i j); simpl in *.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.

      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
      destruct (eq_dec_nat n0 j); simpl in *.
      destruct (eq_dec_nat n n0); simpl in *.
      auto. auto.
      destruct (eq_dec_nat n n0); simpl in *.
      subst. auto.
      destruct (eq_dec_nat i i); simpl in *. auto.
      contradiction.
Defined.

Lemma issupertype_top_p : forall PG n,
  issupertype PG (t_top) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec t_top (t_prim i)).
    inverts e. auto.
Defined.

Lemma issupertype_int_p : forall PG n,
  issupertype PG (t_int) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec t_int (t_prim i)).
    inverts e.
    apply IHPG.
Defined.

Lemma issupertype_bot_p : forall PG n,
  issupertype PG (t_bot) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec t_bot (t_prim i)).
    inverts e.
    apply IHPG.
Defined.

Lemma issupertype_unit_p : forall PG n,
  issupertype PG (t_unit) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec t_unit (t_prim i)).
    inverts e. 
    apply IHPG.
Defined.

Lemma issupertype_arrow_p : forall PG A B n,
  issupertype PG (t_arrow A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_arrow A B) (t_prim i)).
    inverts e.
    apply IHPG.
Defined.

Lemma issupertype_union_p : forall PG A B n,
  issupertype PG (t_union A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_union A B) (t_prim i)).
    inverts e.
    apply IHPG.
Defined.

Lemma issupertype_inter_p : forall PG A B n,
  issupertype PG (t_and A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_and A B) (t_prim i)).
    inverts e. 
    apply IHPG.
Defined.

Lemma issupertype_bvar_p : forall PG j n,
  issupertype PG (t_bvar j) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_bvar j) (t_prim i)).
    inverts e. 
    apply IHPG.
Defined.

Lemma issupertype_fvar_p : forall PG v n,
  issupertype PG (t_fvar v) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_fvar v) (t_prim i)).
    inverts e. 
    apply IHPG.
Defined.

Lemma issupertype_all_p : forall PG A B n,
  issupertype PG (t_all A B) (t_prim n) = false.
Proof.
  induction PG; intros.
  - simpl. auto.
  - destruct a as [i C].
    simpl. destruct (eq_dec (t_all A B) (t_prim i)).
    inverts e. 
    apply IHPG.
Defined.

Lemma issupertype_weakening : forall PG n1 n2,
  issupertype PG (t_prim n1) (t_prim n2) = true ->
  forall i A,
  ~ set_In i (domain_envp PG) ->
  issupertype ((i, A) :: PG) (t_prim n1) (t_prim n2) = true.
Proof.
  introv EQ NOTIN.
  destruct A;
  try (simpl; destruct (eq_dec_nat n1 i); subst; simpl; auto);
  try solve [apply subpertypes_inversion in EQ;
  apply allsubtypes_in_to_domain_nat in EQ;
  contradiction].
Qed.

Lemma get_all_subtypes_issupertype : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  issupertype PG (t_prim n1) (t_prim n2) = true.
Proof.
  introv OK.
  induction OK; intros.
  - simpl in H. inverts H.
  - destruct A.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_top_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_int_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_bot_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_arrow_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_union_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_inter_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_unit_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + (*case bvar*)
      simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_bvar_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + (*case fvar*)
      simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_fvar_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + (*case all*)
      simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      rewrite issupertype_all_p in H1.
      destruct (eq_dec_nat n1 i); simpl. subst.
      apply allsubtypes_in_to_domain_nat in H1.
      contradiction.
      apply IHOK in H1. auto.
      contradiction.
    + (*case P*)
      apply getsubtypes_inversion_temp12 in H1; auto.
      destruct H1. destruct  H1.
      subst. auto.
      apply IHOK in H1.
      forwards: issupertype_weakening H1 (t_prim n) H0.
      auto.
Qed.


Lemma n_in_semi_trans : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall i,
  set_In i (get_all_subtypes ((i, t_prim n1) :: PG) (t_prim n2)).
Proof.
  intros.
  simpl.
  destruct (eq_dec_nat n2 n1); simpl.
  destruct (eq_dec_nat i i); simpl.
  auto.
  contradiction.
  destruct (eq_dec_nat i i); simpl.
  apply get_all_subtypes_issupertype in H0; auto.
  rewrite H0. simpl. auto.
  contradiction.
Defined.

Lemma demorgan2 : forall P Q, ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not in *; intros.
  splits; intros.
  apply H; auto.
  apply H; auto.
Qed.

Lemma not_in_domain_issupertype_false : forall PG,
  okenvp PG ->
  forall i, ~ set_In i (domain_envp PG) -> 
  forall A, issupertype PG A (t_prim i)  = false.
Proof.
  introv OK.
  induction OK; intros.
  - simpl. auto.
  - simpl in H1.
    apply demorgan2 in H1. destruct H1.
    destruct A; simpl; destruct (eq_dec A0 (t_prim i)); simpl;
    (*all cases except P*)
    try solve [
      forwards*: IHOK H2 t_top;
      forwards*: IHOK H2].
    (*case P*)
    destruct (eq_dec_nat i0 n); simpl.
    subst. inverts H. contradiction.
    forwards*: IHOK H2 (t_prim n).
Defined.

Lemma not_in_domain_subtypes_empty : forall PG,
  okenvp PG -> forall i,
  ~ set_In i (domain_envp PG) ->
  (get_all_subtypes PG (t_prim i)) = [].
Proof.
  introv OK.
  induction OK; intros.
  - simpl. auto.
  - simpl in H1.
    apply demorgan2 in H1. destruct H1.
    destruct A;
    simpl; destruct (eq_dec_nat i i); simpl; try solve [contradiction].
    + forwards* FALSE: not_in_domain_issupertype_false OK t_top;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_int;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_bot;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_arrow A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_union A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_and A1 A2);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK t_unit;
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_bvar n);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_fvar v);
      rewrite* FALSE.
    + forwards* FALSE: not_in_domain_issupertype_false OK (t_all A1 A2);
      rewrite* FALSE.
    + (*case P*)
      destruct (eq_dec_nat i0 n); simpl.
      subst. inverts H. contradiction.
      forwards FALSE: not_in_domain_issupertype_false OK H2 (t_prim n).
      rewrite FALSE. auto.
Defined.


Lemma ord_in_findsubtypes : forall PG G i j,
  sub PG G (t_prim i) (t_prim j) ->  
  set_In i (j::get_all_subtypes PG (t_prim j)).
Proof.
  introv Sub.
  - (*case P*)
    inductions Sub; intros; eauto.
    simpl. auto.
    simpl. right.
    apply nats_to_types_iff; auto.
Qed.


Lemma p_sub_getallsubtypes_not_empty : forall PG E i j k,
  sub PG E (t_prim i) (t_prim j) ->
  sub PG E (t_prim i) (t_prim k) ->
  ((j::(get_all_subtypes PG (t_prim j))) `inter`
  (k::(get_all_subtypes PG (t_prim k)))) <> [].
Proof.
  introv Sub1 Sub2.
  apply ord_in_findsubtypes in Sub1.
  apply ord_in_findsubtypes in Sub2.
  unfold not. intros INTER.
  assert (IN: set_In i ((j :: get_all_subtypes PG (t_prim j)) `inter`
  (k :: get_all_subtypes PG (t_prim k)))).
  apply set_inter_intro; auto.
  rewrite INTER in IN. inverts IN.
Qed.


Lemma set_in_weakening : forall PG n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall i A,
  set_In n1 (get_all_subtypes ((i, A) :: PG) (t_prim n2)).
Proof.
  destruct PG; intros.
  - simpl in H. inverts H.
  - destruct p as [j C].
    destruct A.
   + (*case A = top*)
     destruct C.

     * (*case top top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      simpl.
      simpl in H. auto. auto.
      contradiction.
      contradiction.

    * (*case top int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_int (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    *  (*case top bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case top intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case top P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_top (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = int*)
     destruct C.

     * (*case int top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case int int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case int bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case int intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case int bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case int P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.
      
   + (*case A = bot*)
     destruct C.

     * (*case bot top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case bot int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case bot bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case bot arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case bot intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case bot P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = arrow*)
     destruct C.

     * (*case arrow top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case arrow bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case arrow union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case arrow intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case arrow P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = union*)
     destruct C.

     * (*case union top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case union bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case union union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    * (*case union intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case union P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = intersection*)
     destruct C.

     * (*case intersection top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case intersection bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case intersection unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case intersection bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case intersection fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case intersection all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case intersection P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = unit*)
     destruct C.

    * (*case unit top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case unit int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case unit bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case unit intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case unit bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case unit P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = Tbvar*)
     destruct C.

    * (*case unit top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case Tbvar int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case Tbvar bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case Tbvar intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl. auto. auto.
      contradiction.
      contradiction.

    * (*case Tbvar fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tbvar P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = TFvar*)
     destruct C.

    * (*case TFvar top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case Tfvar int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG t_int (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case Tfvar bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case Tfvar intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_bvar n) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case Tfvar all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case Tfvar P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = All*)
     destruct C.

    * (*case All top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case All int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl.
      auto. auto.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl.
      auto. auto.
      contradiction.
      contradiction.

    *  (*case All bot*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_bot (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case All arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case All union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.
    
    * (*case All intersection*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case All unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl in *.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in H. simpl. auto.
      simpl. auto.
      destruct (issupertype PG t_unit (t_prim n2)).
      simpl in *. auto.
      auto.
      contradiction.
      contradiction.

    * (*case All bvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case All fvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case All all*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case All P*)
      simpl in *.
      destruct (eq_dec_nat n2 n); simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i i); simpl in *.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      simpl. auto.
      simpl. auto.
      contradiction.
      contradiction.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all A1 A2) (t_prim n2)).
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

   + (*case A = P*)
     destruct C.

    * (*case P top*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_top (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P int*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_int (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P bot*)   
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_bot (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P arrow*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_arrow C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P union*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_union C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P intersection*) 
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_and C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P unit*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG t_unit (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P Tbvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_bvar n0) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P Tfvar*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_fvar v) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P All*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)).
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      destruct (issupertype PG (t_all C1 C2) (t_prim n2)); simpl in *.
      auto. auto.
      contradiction.
      contradiction.

    * (*case P P*)
      simpl in *.
      destruct (eq_dec_nat j j); simpl in *.
      destruct (eq_dec_nat n2 n0); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      (*repeatition started in reverse*)

      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (*repeatition from (eq_dec_nat i j) *)

      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (**** repeatition from (eq_dec_nat n2 n0) *****)

      destruct (eq_dec_nat n2 n0); simpl in *.
      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      (*repeatition started in reverse*)

      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      (*repeatition from (eq_dec_nat i j) *)

      destruct (eq_dec_nat i j); simpl.
      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n j); simpl.
      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n0) (t_prim n2)); simpl.
      auto. auto. contradiction.

      destruct (eq_dec_nat n2 n); simpl.
      destruct (eq_dec_nat i i); simpl.
      auto. contradiction.
      destruct (eq_dec_nat i i); simpl.
      destruct (issupertype PG (t_prim n) (t_prim n2)); simpl.
      auto. auto. contradiction.
Defined.


Lemma p_in_sub_nat62 : forall PG,
  okenvp PG ->
  forall n1 n2,
  set_In n1 (get_all_subtypes PG (t_prim n2)) ->
  forall n3, set_In n2 (get_all_subtypes PG (t_prim n3)) ->
  set_In n1 (get_all_subtypes PG (t_prim n3)).
Proof.
  introv OK.
  inductions OK; intros.
  - inverts H0.
  - apply getsubtypes_inversion_temp12 in H1. destruct H1.
    destruct H1.
    apply getsubtypes_inversion_temp12 in H2. destruct H2.
    destruct H2.
    subst.
    apply subpertypes_inversion; auto.

    subst.
    forwards*: issupertype_inverse H3.
    destruct H1. subst.
    apply n_in_semi_trans; auto.
    simpl in *.
    destruct A.
    rewrite issupertype_top_p in H1. inverts H1.
    rewrite issupertype_int_p in H1. inverts H1.
    rewrite issupertype_bot_p in H1. inverts H1.
    rewrite issupertype_arrow_p in H1. inverts H1.
    rewrite issupertype_union_p in H1. inverts H1.
    rewrite issupertype_inter_p in H1. inverts H1.
    rewrite issupertype_unit_p in H1. inverts H1.
    rewrite issupertype_bvar_p in H1. inverts H1.
    rewrite issupertype_fvar_p in H1. inverts H1.
    rewrite issupertype_all_p in H1. inverts H1.

    forwards*: subpertypes_inversion H1.
    forwards*: IHOK H4 H2.
    apply n_in_semi_trans; auto.
    apply getsubtypes_inversion_temp12 in H2. destruct H2.
    destruct H2. subst.
    apply not_in_domain_subtypes_empty in H0; auto.
    rewrite H0 in H1. inverts H1.
    forwards*: IHOK H1 H2.
    apply set_in_weakening. auto.
Defined.

Lemma p_in_sub : forall PG n1 n2,
  okenvp PG ->
  set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n2))) ->
  forall n3, set_In (t_prim n2) (nats_to_types (get_all_subtypes PG (t_prim n3))) ->
  set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n3))).
Proof.
  intros.
  apply nats_to_types_iff.
  apply nats_to_types_iff in H0.
  apply nats_to_types_iff in H1.
  eapply p_in_sub_nat62 with (n2:=n2); auto.
Qed.

(* ********************************************************************** *)
(** Subtyping Transitivity *)

Lemma sub_transitivity : forall B PG G A C, sub PG G A B -> sub PG G B C -> sub PG G A C.
Proof.
  intros B PG G A C ASubB BSubC.
  assert (W : (type B)).
  forwards*: sub_regular ASubB.
  destructs H.
  forwards*: type_from_wft H1.
  generalize dependent C.
  generalize dependent A.
  generalize dependent G.
  generalize dependent PG.
  remember B as B' in |- *.
  generalize dependent B'.
  induction W; intros B' EQ PG G A ASubB.
  
  1:{ (* Case Top *)
      intros; inductions ASubB; eauto; try discriminate.
      inductions BSubC; eauto.
      forwards*: sub_regular BSubC.
    }

  1:{ (* Case Int *)
      intros; inductions ASubB; eauto; try discriminate.
      forwards*: sub_regular BSubC.
    }

  1:{ (* Case Bot *)
      intros; inductions ASubB; eauto; try discriminate.
      forwards*: sub_regular BSubC.
    }
    
  1:{ (* Case Arrow *)
      intros; inductions ASubB; eauto; try discriminate.
      inductions BSubC; eauto.
      forwards*: sub_regular ASubB1.
      forwards*: sub_regular ASubB2.
      forwards*: sub_regular BSubC.
    }

  1:{ (* Case Union *)
      intros; inductions ASubB; eauto; try discriminate.
      inductions BSubC; eauto.
      forwards*: sub_regular ASubB.
      inverts EQ.
      apply sub_or in BSubC. destruct BSubC.
      forwards*: IHW2 T2 A C.
      forwards*: sub_regular BSubC.
    }

  1:{ (* Case And *)
      intros; inductions ASubB; eauto; try discriminate.
      inductions BSubC; eauto.
      forwards*: sub_regular ASubB1.
      forwards*: sub_regular BSubC.
    }

  1:{ (* Case TVar *)
      intros; inductions ASubB; eauto; try discriminate.
      forwards*: sub_regular BSubC.
    }

  1:{  (* Case Disjoint Quantification *)
      intros; inductions ASubB; eauto; try discriminate.
      forwards*: sub_regular BSubC.
      inductions BSubC; eauto.
      (* All <: Top *)
      assert (sub PG G (t_all S1 S2) (t_all T1 T2)).
      pick_fresh Y.
      apply s_all with (L:=((((((L \u L0) \u fv_tt T1) \u fv_tt T2) \u fv_tt S1) \u fv_tt S2) \u
      dom G)); auto.
      forwards*: sub_regular H6.
      (* All <: All *)
      clear H4 IHBSubC.
      pick_fresh Y.
      apply s_all with (L:=(((((((((L \u L0) \u L1) \u fv_tt T1) \u fv_tt T2) \u fv_tt S1) \u
      fv_tt S2) \u fv_tt T4) \u fv_tt T5) \u dom G)); autos*.
      intros.
      lapply (H0 X); [ intros K | auto ].
      apply (K (T2 open_tt_var X)); auto.
      rewrite (append_empty_right (G & X ~*: T4)).
      eapply sub_narrowing_aux; eauto.
      assert (NOTIN : X \notin L0) by auto.
      forwards: H1 X NOTIN.
      rewrite~ <- append_empty_right.
      forwards* TEMP1: H3 X.
      forwards* (_&_&_&TEMP2): sub_regular TEMP1.
      apply okt_push_inv_tt in TEMP2.
      destructs TEMP2.
      rewrite~ <- append_empty_right.
    }

  1:{  (* Case Unit *)
      intros; inductions ASubB; eauto; try discriminate.
      forwards*: sub_regular BSubC.
    }

  1:{
      intros; inductions BSubC; eauto; try discriminate.
      (*case bot <: C*)
      forwards*: sub_regular ASubB.
      (*case P <: C *)
      forwards*: sub_regular ASubB.
      inductions ASubB; eauto.
      forwards*: IHASubB1.
      split*. split*. destructs H4. inverts* H5.
      forwards*: IHASubB2.
      split*. split*. destructs H4. inverts* H6.
      forwards*: IHASubB.
      split*. split*. destructs H5. inverts* H6.
      forwards*: IHASubB.
      split*. split*. destructs H5. inverts* H6.
      forwards*: p_in_sub H3 H8.
    }
Defined.


(* ********************************************************************** *)
(** Subtyping Weakening *)

Lemma sub_weakening : forall PG E F G S T,
   sub PG (E & G) S T -> 
   okt PG (E & F & G) ->
   sub PG (E & F & G) S T.
Proof.
  introv Typ. gen_eq : (E & G) as H. gen G.
  induction Typ; introv EQ Ok; subst; eauto.
  - apply wft_weaken with (F:=F) in H1; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H1; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H1; auto.
    apply ok_from_okt in Ok; auto.
  - pick_fresh Y.
    apply s_all with (L:=(
    ((((((L \u fv_tt S1) \u fv_tt S2) \u fv_tt T1) \u fv_tt T2) \u dom E) \u dom F) \u
    dom G0)); auto.
    intros.
    forwards* : H0 X (G0 & X ~*: T1).
    rewrite~ concat_assoc.
    apply sub_regular in Typ. destructs Typ.
    forwards*: ok_from_okt Ok.
    forwards* : wft_weaken H4.
    forwards*: H Y.
    forwards*(_&_&_&TEMP1): sub_regular H8.
    apply okt_push_inv_tt in TEMP1.
    destructs TEMP1.
    rewrite~ concat_assoc.
    rewrite~ concat_assoc in H2.
  - apply wft_weaken with (F:=F) in H1; auto.
    apply ok_from_okt in Ok; auto.
  - apply wft_weaken with (F:=F) in H1; auto.
    apply wft_weaken with (F:=F) in H2; auto.
    apply ok_from_okt in Ok; auto.
    apply ok_from_okt in Ok; auto.
Qed.

(* ********************************************************************** *)
(** Subtyping Strengthening (6) *)

Lemma sub_strengthening : forall PG x U E F S T,
  sub PG (E & x ~: U & F) S T ->
  sub PG (E & F) S T.
Proof.
  intros PG x U E F S T SsubT.
  gen_eq : (E & x ~: U & F) as G. gen F.
  induction SsubT; introv EQ; subst; autos*; 
  try solve [apply wft_strengthen in H1;
  apply okt_strengthen in H0; auto];
  try solve [apply wft_strengthen in H; auto];
  try solve [apply okt_strengthen in H; auto].
  (* case: all *)
  pick_fresh Y.
  apply s_all with (L:=((((((((L \u \{ x}) \u fv_tt U) 
    \u fv_tt S1) \u fv_tt S2) \u fv_tt T1) \u fv_tt T2) \u
    dom E) \u dom F)); auto; intros. 
  apply_ih_bind* H0.
  apply wft_strengthen in H2;
  apply wft_strengthen in H1;
  apply okt_strengthen in H0; auto.
Qed.


(********************************************)
(** Disjointness Weakening **)


Lemma p_diff_env : forall PG E1 E2 i j,
  sub PG E1 (t_prim i) (t_prim j) ->
  okt PG E2 ->
  (* wft PG E2 (t_prim i) -> *)
  wft PG E2 (t_prim j) ->
  sub PG E2 (t_prim i) (t_prim j).
Proof.
  introv sub ok WF. inverts sub; eauto.
  lets TEMP1: H6.
  apply nats_to_types_iff in TEMP1.
  forwards*: allsubtypes_in_to_domain_nat.
Qed.


Lemma disj_weakening : forall PG F E G S T,
   PG; (E & G) |= S *a T -> 
   okt PG (E & F & G) ->
   PG; (E & F & G) |= S *a T.
Proof.
  introv Disj Ok.
  induction Disj; auto.
  - lets: ok_from_okt Ok.
    eapply wft_weaken in H1; eauto.
  - lets: ok_from_okt Ok.
    eapply wft_weaken in H1; eauto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
    (* apply wft_weaken with (F:=F) in H1; auto. *)
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
    (* apply wft_weaken with (F:=F) in H1; auto. *)
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
    (* apply wft_weaken with (F:=F) in H1; auto. *)
  - (*or1*)
    lets: ok_from_okt Ok.
    apply* disj_or1.
    apply wft_weaken with (F:=F) in H; auto.
  - lets: ok_from_okt Ok.
    apply* disj_or2.
    apply wft_weaken with (F:=F) in H; auto.
  - (*and cases*)
    lets: ok_from_okt Ok.
    apply* disj_and1.
    apply wft_weaken with (F:=F) in H; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H; auto.
  - (*all cases*)
    lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
    apply wft_weaken with (F:=F) in H2; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
    apply wft_weaken with (F:=F) in H2; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
  - lets: ok_from_okt Ok.
    apply wft_weaken with (F:=F) in H1; auto.
  - (*TVar cases*)
    lets: ok_from_okt Ok.
    forwards TEMP1: sub_weakening F H0; auto.
    eapply disj_fvarl; eauto.
    apply* binds_weaken.
  - lets: ok_from_okt Ok.
    forwards TEMP1: sub_weakening F H0; auto.
    eapply disj_fvarr; eauto.
    apply* binds_weaken.
  - lets okt: ok_from_okt Ok.
    apply* disj_prim.
    apply wft_weaken with (F:=F) in H1; auto.
    apply wft_weaken with (F:=F) in H2; auto.
Qed.


(* ********************************************************************** *)
(** Typing Weakening *)

Lemma typing_weakening : forall PG E F G e T,
   typing PG (E & G) e T ->
   okt PG (E & F & G) ->
   typing PG (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. 
    apply* binds_weaken.
    apply ok_from_okt in Ok; auto.
  - apply* typ_app.
  - apply* typ_sub.
    apply* sub_weakening.
  - pick_fresh y.
    apply typ_abs with (L:=((((((L \u fv_ee e) \u fv_te e) 
      \u fv_tt A) \u fv_tt B) \u dom E) \u dom G) \u dom F); auto.
    intros.
    forwards~: (H1 x).
    apply_ih_bind (H2 x); eauto.
    apply* okt_typ.
    apply* wft_weaken.
    apply typing_regular in H4. destructs~ H4.
    apply okt_push_inv in H5. destructs~ H5.
    apply ok_from_okt in Ok; auto.
  - pick_fresh y.
    apply typ_typeof with (L:=(((((((L \u fv_ee e) 
      \u fv_te e) \u fv_tt A) \u fv_tt B) \u dom E) \u dom G) \u dom F)); intros; autos*.
    + forwards* : H x. apply_ih_bind (H0 x); eauto.
      apply okt_typ; auto. apply* wft_weaken.
      forwards* (?&?&?&?): typing_regular Typ. inverts* H9.
      apply ok_from_okt in Ok; auto.
    + forwards* : H1 x. apply_ih_bind (H2 x); eauto.
      apply okt_typ; auto. apply* wft_weaken.
      forwards* (?&?&?&?): typing_regular Typ. inverts* H9.
      apply ok_from_okt in Ok; auto.
    + (* TODO: need some work here *)
      apply* disj_weakening. 
  - apply* typ_inter.
  - pick_fresh Y.
    apply typ_tabs with (L:=(((((((L \u fv_ee e) \u fv_te e) \u fv_tt A) 
      \u fv_tt B) \u dom E) \u dom G) \u dom F)); auto; intros.
    apply_ih_bind (H2 X); eauto.
    apply okt_disj; auto.
    apply* wft_weaken.
    forwards* : H1 Y.
    forwards* (?&?&?): typing_regular H4.
    apply* (@okt_push_inv_tt PG (E & G) Y A).
    apply ok_from_okt in Ok; auto.
  - eapply typ_tapp; eauto.
    (* TODO: need some work here *)
    apply* disj_weakening.
  - (*Case P*)
    apply* typ_prim.
    apply* wft_weaken.
    apply* ok_from_okt. 
Qed.


(************************************************************************ *)
(** Preservation by Type Narrowing *)


(********************************************)
(** Disjointness Narrowing **)


Lemma disj_narrowing : forall PG F E Z P S T,
  PG; (E & Z ~*: P & F) |= S *a T ->
  forall Q, sub PG E P Q ->
  PG; (E & Z ~*: Q & F) |= S *a T.
Proof.
  introv Disj Sub. gen Q.
  induction Disj; intros.
  1,2,3,4,5,6,7,8,15,16,17,18,19,20: 
    try solve [forwards TEMP1: sub_regular Sub; 
    forwards OK1: okt_narrow P Q H0; autos*].
  7: { (*case varl*)
    assert (TEMP1: PG; E & Z ~*: P & F |= t_fvar X *a A); auto.
    apply* disj_fvarl.
    forwards (OKP&WFA&WFT&OK): sub_regular H0.
    forwards (_&WFP&WFQ&_): sub_regular Sub.
    forwards OK1: okt_narrow Q OK; auto.
    forwards WFT': wft_narrow WFT OK1.
    forwards Sub1: sub_narrowing_aux H0 Sub; auto.
    clear H0.
    (* case analysis on binding of X *)
    binds_cases H;
    (* solve trivial goals *)
    try solve [eapply disj_fvarl with (T:=T); auto].
    (* case when X equals Z *)
    inverts EQ.
    eapply disj_fvarl with (T:=Q); auto.
    (* rewrite <- (concat_empty_r E) in Sub.
    rewrite <- (concat_empty_r (E & X ~*: P & F)) in OK. *)
    lets Sub2: sub_weakening E.
    specialize (Sub2 (X ~*: Q & F) empty).
    rewrite concat_empty_r in Sub2.
    rewrite concat_empty_r in Sub2.
    rewrite concat_assoc in Sub2.
    specialize (Sub2 P Q Sub OK1).
    forwards: sub_transitivity Sub1 Sub2; auto.
    (* apply* binds_narrowing. *)
  }
  7: { (*case varr*)
    assert (TEMP1: PG; E & Z ~*: P & F |= t_fvar X *a A); auto.
    apply* disj_fvarl.
    forwards (OKP&WFA&WFT&OK): sub_regular H0.
    forwards (_&WFP&WFQ&_): sub_regular Sub.
    forwards OK1: okt_narrow Q OK; auto.
    forwards WFT': wft_narrow WFT OK1.
    forwards Sub1: sub_narrowing_aux H0 Sub; auto.
    clear H0.
    (* case analysis on binding of X *)
    binds_cases H;
    (* solve trivial goals *)
    try solve [eapply disj_fvarr with (T:=T); auto].
    (* case when X equals Z *)
    inverts EQ.
    eapply disj_fvarr with (T:=Q); auto.
    (* rewrite <- (concat_empty_r E) in Sub.
    rewrite <- (concat_empty_r (E & X ~*: P & F)) in OK. *)
    lets Sub2: sub_weakening E.
    specialize (Sub2 (X ~*: Q & F) empty).
    rewrite concat_empty_r in Sub2.
    rewrite concat_empty_r in Sub2.
    rewrite concat_assoc in Sub2.
    specialize (Sub2 P Q Sub OK1).
    forwards: sub_transitivity Sub1 Sub2; auto.
  }
  1: { (*case union*)
    forwards: IHDisj1 Sub.
    forwards: IHDisj2 Sub.
    apply* disj_or1.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular H1.
  }
  1: { (*case union*)
    forwards: IHDisj1 Sub.
    forwards: IHDisj2 Sub.
    apply* disj_or2.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular H1.
  }
  1: { (*case and*)
    forwards Disj1: IHDisj Sub.
    apply* disj_and1.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular Disj1.
  }
  1: { (*case and*)
    forwards Disj1: IHDisj Sub.
    apply* disj_and2.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular Disj1.
  }
  1: { (*case and*)
    forwards Disj1: IHDisj Sub.
    apply* disj_and3.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular Disj1.
  }
  1: { (*case and*)
    forwards Disj1: IHDisj Sub.
    apply* disj_and4.
    apply wft_narrow with (V:=P); auto.
    forwards*: disj_regular Disj1.
  }
  1:{ (*case P*)
     apply disj_prim; auto.
     apply* okt_narrow.
     forwards*: sub_regular Sub.
     apply wft_narrow with (V:=P); auto.
     apply okt_narrow with (V:=P); auto.
     forwards*: sub_regular Sub.
     apply wft_narrow with (V:=P); auto.
     apply okt_narrow with (V:=P); auto.
     forwards*: sub_regular Sub.
  }
Qed.


(********************************************)
(** Typing Narrowing **)

Lemma typing_narrowing : forall PG Q E F X P e T,
  sub PG E P Q ->
  typing PG (E & X ~*: P & F) e T ->
  typing PG (E & X ~*: Q & F) e T.
Proof.
  introv PsubQ Typ. gen_eq : (E & X ~*: P & F) as E'. gen F.
  forwards*: sub_regular PsubQ. destructs H.
  induction Typ; introv EQ; subst; auto.
  - apply* typ_lit.
    apply* okt_narrow.
  - apply* typ_null.
    apply* okt_narrow.
  - binds_cases H5. apply* typ_var.
    apply* okt_narrow.
    apply* typ_var. apply* okt_narrow.
  - apply* typ_app.
  - apply* typ_sub.
    forwards*: sub_narrowing_aux H3 PsubQ.
    forwards* (_&_&_&TEMP1): sub_regular H3.
    apply* okt_narrow.
  - pick_fresh y.
    apply typ_abs with (L:=(((((((((L \u \{ X}) \u fv_ee e) 
      \u fv_te e) \u fv_tt Q) \u fv_tt P) \u fv_tt A) \u
      fv_tt B) \u dom E) \u dom F)); intros; auto.
    apply* okt_narrow.
    apply_ih_bind* H6.
  - pick_fresh y.
    apply typ_typeof with (L:=((((((((((((((L \u \{ X}) \u fv_ee e) 
      \u fv_ee e1) \u fv_ee e2) \u fv_te e) \u fv_te e1) \u
      fv_te e2) \u fv_tt Q) \u fv_tt P) \u fv_tt A) \u fv_tt B) \u 
      fv_tt C) \u dom E) \u dom F)) ; intros; auto.
    apply_ih_bind* H4.
    apply_ih_bind* H6.
    (* TODO: need some work here *)
    apply* disj_narrowing.
  - pick_fresh Y.
    apply typ_tabs with (L:=(((((((((L \u \{ X}) \u fv_ee e) 
      \u fv_te e) \u fv_tt Q) \u fv_tt P) \u fv_tt A) \u
      fv_tt B) \u dom E) \u dom F)); intros; auto.
    apply* okt_narrow.
    apply_ih_bind* H6.
  - apply* typ_tapp.
    (* TODO: need some work here *)
    apply* disj_narrowing.
  - (*case P*)
    apply* typ_prim.
    apply* okt_narrow.
    apply* wft_narrow.
    apply* okt_narrow.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma binds_strengthen : forall X T E x U F,
  binds X (bind_disj T) (E & x ~: U & F) ->
  binds X (bind_disj T) (E & F).
Proof.
  introv B.
  binds_cases B; auto.
Qed.


Lemma disj_strengthening : forall PG x U E F S T,
  PG; (E & x ~: U & F) |= S *a T ->
  PG; (E & F) |= S *a T.
Proof.
  introv Disj.
  induction Disj.
  (*trivial cases*)
  all:  try solve [
        apply okt_strengthen in H0; auto;
        apply wft_strengthen in H1; auto].
  (*arrow cases*)
  all: try solve [
       apply okt_strengthen in H0;
       apply wft_strengthen in H1;
       apply wft_strengthen in H2; auto].
  (*union cases*)
  1,2 : apply wft_strengthen in H.
        apply disj_or1 with (A1:=A1) (A2:=A2); auto.
        apply disj_or2 with (B1:=B1) (B2:=B2); auto.
  (*inter cases*)
  1-6: try (apply wft_strengthen in H);
       try (apply wft_strengthen in H0).
       eapply disj_and1; eauto.
       eapply disj_and2; eauto.
       eapply disj_and3; eauto.
       eapply disj_and4; eauto.
       (* eapply disj_and5; eauto.
       eapply disj_and6; eauto. *)
  (*var cases*)
  1,2: try (apply binds_strengthen in H);
       try (apply sub_strengthening in H0).
       apply disj_fvarl with (T:=T); auto.
       apply disj_fvarr with (T:=T); auto.
Qed.

Lemma typing_through_subst_ee : forall PG E F x T e u U,
   typing PG (E & x ~: U & F) e T ->
   typing PG E u U ->
   typing PG (E & F) (subst_ee x u e) T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; simpl.
(*case int*)
 - apply* typ_lit.
 - (*case null*)
   apply* typ_null.
(*case var*)
 - case_var.
  + binds_get H1.
    apply ok_from_okt in H; auto.
    lets M: (typing_weakening PG E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H1; apply* typ_var.
(*case app*)
 - eapply typ_app; eauto.
(*case sub*)
 - forwards* : IHTypT E F TypU TypT.
   eapply typ_sub; eauto.
   apply sub_strengthening in H; auto.
(*case abs*)
 - pick_fresh y.
   apply typ_abs with (L:=((((((((((L \u \{ x}) \u fv_ee u) 
     \u fv_ee e) \u fv_te u) \u fv_te e) \u fv_tt U) \u
     fv_tt A) \u fv_tt B) \u dom E) \u dom F)); intros; autos*.
   assert (x0 \notin L) by auto.
   specialize (H2 x0 H4 E (F & x0 ~: A)).
   rewrite* subst_ee_open_ee_var.
   lets : H2 x U.
   forwards* : H5.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destructs~ TypU.
(*case typeof*)
 - pick_fresh y.
   apply typ_typeof with (L:=(((((((((((((((L \u \{ x}) \u fv_ee u) 
     \u fv_ee e) \u fv_ee e1) \u fv_ee e2) \u fv_te u) \u
     fv_te e) \u fv_te e1) \u fv_te e2) \u fv_tt U) \u fv_tt A) \u 
     fv_tt B) \u fv_tt C) \u dom E) \u dom F)); intros; eauto.
 + rewrite* subst_ee_open_ee_var.
   forwards*: H x0.
   forwards*: H0 x0 E (F & x0 ~: A) x.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destructs~ TypU.
 + rewrite* subst_ee_open_ee_var.
   forwards*: H1 x0.
   forwards*: H2 x0 E (F & x0 ~: B) x.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destructs~ TypU.
 + (* need work here *)
   apply disj_strengthening in H3; auto.
- apply* typ_inter.
- pick_fresh Y.
  apply typ_tabs with (L:=((((((((((L \u \{ x}) \u fv_ee u) 
    \u fv_ee e) \u fv_te u) \u fv_te e) \u fv_tt U) \u
    fv_tt A) \u fv_tt B) \u dom E) \u dom F)); intros; autos*.
  assert (X \notin L) by auto.
   specialize (H1 X H4).
   rewrite* subst_ee_open_te_var.
   lets : H2 X H4 E (F & X ~*: A) x.
   lets : H5 U.
   forwards*: H6.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destructs~ TypU.
- eapply typ_tapp; eauto.
  (* need work here *)
  apply disj_strengthening in H; auto.
- (*Case P*)
  apply* typ_prim.
  apply* wft_strengthen.
Qed.

Lemma okt_subst_tb : forall PG Q Z P E F,
  okt PG (E & Z ~*: Q & F) ->
  wft PG E P ->
  okt PG (E & map (subst_tb Z P) F).
Proof.
  induction F using env_ind; intros Ok WP.
  - (*case F = empty*)
    rewrite concat_empty_r in Ok.
    rewrite map_empty.
    rewrite concat_empty_r.
    apply okt_push_inv_tt in Ok. destructs~ Ok.
  - (*case F = x ~ v*)
    rewrite concat_assoc in Ok.
    (* destruc ~ to ~:* and ~: *)
    destruct v.
    apply okt_push_inv_tt in Ok. destructs Ok.
    forwards*: IHF.
    rewrite map_concat.
    rewrite map_single. simpl.
    forwards*: okt_disj PG (E & (map (subst_tb Z P) F)) x (subst_tt Z P t).
    apply ok_from_okt in H2.
    forwards*: wft_subst_tb H1 H2.
    rewrite~ concat_assoc.
    apply okt_push_inv in Ok. destructs Ok.
    forwards*: IHF.
    rewrite map_concat.
    rewrite map_single. simpl.
    forwards*: okt_typ PG (E & (map (subst_tb Z P) F)) x (subst_tt Z P t).
    apply ok_from_okt in H2.
    forwards*: wft_subst_tb H1 H2.
    rewrite~ concat_assoc.
Qed.


(* ********************************************************************** *)
(** Type substitution in Types Preserves Subtyping (10) *)


Lemma sub_through_subst_tt : forall PG Q E F Z S T P,
  sub PG (E & Z ~*: Q & F) S T ->
  PG; E |= P *a Q ->
  okt PG ((E & map (subst_tb Z P) F)) ->
  sub PG (E & map (subst_tb Z P) F) (subst_tt Z P S) (subst_tt Z P T).
Proof.
  introv SsubT PsubQ ok.
  gen_eq : (E & Z ~*: Q & F) as G. gen F.
  induction SsubT; introv okt EQ; subst; simpl subst_tt; eauto.
  - (*case top*)
    forwards*: ok_from_okt okt.
    forwards*: disj_regular PsubQ.
    destructs H3.
    forwards*: wft_subst_tb H1 H2.
  - (*case A <: A1 | A2*)
    forwards* Sub: IHSsubT.
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    forwards*: wft_subst_tb H OK.
  - (*case A <: A1 | A2*)
    forwards* Sub: IHSsubT.
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    forwards*: wft_subst_tb H OK.
  - (*case A1 & A2 <: A*)
    forwards* Sub: IHSsubT.
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    forwards*: wft_subst_tb H OK.
  - (*case A1 & A2 <: A*)
    forwards* Sub: IHSsubT.
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    forwards*: wft_subst_tb H OK.
  - (*case bot <: A*)
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    forwards*: wft_subst_tb H1 OK.
  - (*case fvar*)
    case_var.
    forwards*: disj_regular PsubQ.
    apply* sub_refl.
    apply* wft_weaken_right.
    apply ok_from_okt in okt. auto.
    forwards* OK: ok_from_okt okt.
    forwards*: disj_regular PsubQ.
    apply* sub_refl.
    forwards*: wft_subst_tb H1 OK.
    rewrite~ (subst_tt_fresh Z P (t_fvar X)) in H3.
    simpl. auto.
  - (*case all*)
    forwards* Sub: IHSsubT.
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    pick_fresh Y.
    apply s_all with (L:=( ((((((((L \u \{ Z}) \u fv_tt Q) \u fv_tt P) 
     \u fv_tt S1) \u fv_tt S2) \u
    fv_tt T1) \u fv_tt T2) \u dom E) \u dom F)); auto; intros.
    forwards*: H0 X (F & X ~*: T1).
    rewrite map_concat. rewrite map_single. simpl.
    rewrite concat_assoc.
    apply* okt_disj.
    forwards* (_&_&WFT1&_): sub_regular SsubT.
    forwards*: wft_subst_tb WFT1 WFP OK.
    apply type_from_wft in WFP.
    assert (NOTIN: X \notin L) by auto.
    specialize (H X). apply H in NOTIN.
    forwards* (_&_&_&TEMP1): sub_regular NOTIN.
    apply okt_push_inv_tt in TEMP1.
    destructs TEMP1.
    rewrite~ concat_assoc.
    rewrite map_concat in H2.
    rewrite map_single in H2.
    unsimpl_map_bind.
    rewrite~ (subst_tt_open_tt_var).
    rewrite~ (subst_tt_open_tt_var).
    rewrite~ concat_assoc in H2.
    apply type_from_wft in WFP; auto.
    apply type_from_wft in WFP; auto.
  - (*case Prim*)
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    apply* sub_refl.
    forwards*: wft_subst_tb H1 OK.
  - (*case Prim*)
    forwards* OK: ok_from_okt okt.
    forwards* (okp&okte&WFP&WFQ): disj_regular PsubQ.
    apply* s_p_sub.
    forwards*: wft_subst_tb H1 OK.
    forwards*: wft_subst_tb H2 OK.
Qed.

(************************************************************************ *)
(** Preservation by Type Substitution of Types in Terms (11) *)

Lemma notin_fv_wf : forall PG E X T,
  wft PG E T -> X # E -> X \notin fv_tt T.
Proof.
  induction 1; intros Fr; simpl; eauto.
  rewrite notin_singleton. intro. subst. apply Fr.
  apply binds_get in H.
  apply get_none in Fr.
  rewrite H in Fr. inverts Fr.
  notin_simpl; auto. pick_fresh Y.
  forwards*: H1 Y.
  apply* (@notin_fv_tt_open Y).
Qed.

(************************************************************************ *)
(** ** Type substitution preserves typing (11) *)

Lemma map_subst_tb_id : forall PG G Z P,
  okt PG G ->
  Z \notin dom G ->
  G = map (subst_tb Z P) G.
Proof with auto.
  intros PG G Z P H.
  induction H; simpl; intros Fr.
  rewrite~ map_empty.
  forwards*: IHokt.
  rewrite map_concat.
  rewrite map_single.
  simpl.
  rewrite (subst_tt_fresh Z P T); eauto.
  rewrite H2 at 1; auto.
  forwards*: notin_fv_wf Z H0.
  forwards*: IHokt.
  rewrite map_concat.
  rewrite map_single.
  simpl.
  rewrite (subst_tt_fresh Z P T); eauto.
  rewrite H2 at 1; auto.
  forwards*: notin_fv_wf Z H0.
Qed.


Lemma not_supertype_subtype : forall PG E A B,
  not (sub PG E A B) ->
  forall C, sub PG E A C ->
  not (sub PG E C B).
Proof.
  introv Nsub Sub1.
  unfold not in *; introv Sub2.
  apply Nsub.
  eapply sub_transitivity in Sub2; eauto.
Qed.

Lemma not_sub_union : forall PG E A B C,
  wft PG E A ->
  wft PG E B ->
  not (sub PG E (t_union A B) C) ->
  not ((sub PG E A C) /\ (sub PG E B C)).
Proof.
  introv WFA WFB Nsub.
  unfold not in *.
  intros. destruct H.
  apply Nsub; auto.
Qed.


Lemma not_sub_inter : forall PG E A B C,
  wft PG E A ->
  wft PG E B ->
  not (sub PG E (t_and A B) C) ->
  not (sub PG E A C) /\ not (sub PG E B C).
Proof.
  introv WFA WFB Nsub.
  unfold not in *. split; intros.
  apply Nsub; auto.
  apply Nsub; auto.
Qed.


Lemma US_after_subst_US : forall A A1 A2,
  US A A1 A2 ->
  forall Z P, US (subst_tt Z P A) (subst_tt Z P A1) (subst_tt Z P A2).
Proof.
  introv ord.
  induction ord; intros; simpl; auto.
Qed.


Lemma disj_sym : forall PG E A B,
  PG; E |= A *a B ->
  PG; E |= B *a A.
Proof.
  induction 1; auto.
  (*union cases*)
  apply* disj_or2. apply* disj_or1.
  (*var cases*)
  apply* disj_fvarr. apply* disj_fvarl.
  apply* disj_prim.
  (*it requires symmetry of set intersection*)
  assert (EQ: ((j :: get_all_subtypes PG (t_prim j)
    `inter` i :: get_all_subtypes PG (t_prim i)) = []) \/
    (j :: get_all_subtypes PG (t_prim j)
    `inter` i :: get_all_subtypes PG (t_prim i)) <> []).
  apply list_empty_decide with (l:=(j :: get_all_subtypes PG (t_prim j)
  `inter` i :: get_all_subtypes PG (t_prim i))).
  destruct EQ as [EQ | EQ]; auto.
  apply not_empty_in_exist in EQ.
  destruct EQ as [k IN].
  apply set_inter_elim in IN.
  destruct IN as [IN1 IN2].
  forwards*: set_inter_intro eq_dec_nat IN2 IN1.
  rewrite H3 in H4. inverts H4.
Qed.

Lemma US_UO : forall PG E A,
  wft PG E A ->
  UO A \/ (exists A1 A2, US A A1 A2).
Proof.
  induction 1; eauto.
  destruct IHwft1; destruct IHwft2; auto.
  destruct H2 as [B1 [B2 SPL]].
  right. exists*.
  destruct H1 as [B1 [B2 SPL]].
  right. exists*.
  destruct H1 as [B1 [B2 SPL1]].
  destruct H2 as [C1 [C2 SPL2]].
  right*.
Qed.

Lemma UO_sub_union : forall PG E B B1 B2,
  US B B1 B2 ->
  forall A, UO A ->
  sub PG E A B ->
  sub PG E A B1 \/ sub PG E A B2.
Proof.
  induction 1;
  introv Ord Sub.
  induction Ord; inverts* Sub.
  inverts* H1.
  1,2: apply sub_and in Sub;
       forwards*: IHUS Ord.
Qed.

Require Import Lia.

Lemma US_size_red : forall A A1 A2,
  US A A1 A2 -> t_size A1 < t_size A /\ t_size A2 < t_size A.
Proof.
  induction 1; intros; simpl. lia.
  destruct IHUS. split. lia. lia.
  destruct IHUS. split. lia. lia.
Defined.

Lemma US_sub : forall PG E A A1 A2,
  okenvp PG ->
  okt PG E ->
  wft PG E A -> wft PG E A1 -> wft PG E A2 ->
  US A A1 A2 ->
  sub PG E A1 A /\ sub PG E A2 A.
Proof.
  induction 6; eauto.
  inverts* H0. inverts H1. inverts H2.
  destruct IHUS; auto. inverts* H3. inverts* H3.
  inverts H1. inverts H2. inverts H3.
  destruct IHUS; auto.
Qed.

Lemma US_wft : forall PG E A A1 A2,
  US A A1 A2 ->
  wft PG E A ->
  wft PG E A1 /\ wft PG E A2.
Proof.
  induction 1; introv WFT.
  inverts* WFT.
  inverts* WFT.
  inverts* WFT.
Qed.

Lemma bot_sub_disjoint : forall PG E A,
  sub PG E A t_bot ->
  forall B, 
  wft PG E B ->
  PG; E |= A *a B.
Proof.
  introv Sub. inductions Sub; introv WFB; eauto.
  forwards*: IHSub1 B.
  forwards*: IHSub2 B.
  apply disj_or1 with (A1:=A1) (A2:=A2); auto.
  forwards*: sub_regular Sub1.
  forwards*: sub_regular Sub2.
  (* forwards*: IHSub A1.
  apply disj_sym in H0; auto. *)
Qed.

Lemma sub_disjoint3 : forall n PG E A B C,
  (t_size A + t_size B + t_size C) < n ->
  PG; E |= A *a B ->
  sub PG E C A ->
  PG; E |= C *a B.
Proof.
  induction n.
  intros. lia.
  introv Less Disj Sub. gen C.
  induction Disj; intros; eauto.
  9: { (*union*)
    forwards*: sub_regular Sub.
    forwards* TEMP1: US_UO C.
    destruct TEMP1 as [UOR | USPL].
    (*UO*)
    forwards* TEMP2: UO_sub_union Sub.
    destruct TEMP2 as [TEMP2 | TEMP2].
    forwards*: IHDisj1 TEMP2.
    simpl in *.
    forwards* (LESS1&LESS2): US_size_red H0. lia.
    forwards*: IHDisj2 TEMP2.
    simpl in *.
    forwards* (LESS1&LESS2): US_size_red H0. lia.
    (*US*)
    destruct USPL as [C1 [C2 USPL]].
    assert (Disj PG E A B); eauto.
    forwards* (_&WFC&_&_): sub_regular Sub.
    forwards*: US_sub PG E USPL.
    forwards*: US_wft USPL WFC.
    forwards*: US_wft USPL WFC.
    destruct H3 as [Sub1 Sub2].
    forwards* Sub3: sub_transitivity Sub1 Sub.
    forwards* Sub4: sub_transitivity Sub2 Sub.
    clear Sub1 Sub2 Sub.
    forwards*: IHn E A B C1.
    forwards*(LESS1&LESS2): US_size_red USPL.
    simpl in *. lia.
    forwards*: IHn E A B C2.
    forwards*(LESS1&LESS2): US_size_red USPL.
    simpl in *. lia.
  }
  9: { (*union*)
    forwards*: IHDisj1 Sub.
    forwards*(LESS1&LESS2): US_size_red H0.
    simpl in *. lia.
    forwards*: IHDisj2 Sub.
    forwards*(LESS1&LESS2): US_size_red H0.
    simpl in *. lia.
  }
  (*and cases*)
  9: {
      apply sub_and in Sub. destruct Sub.
      simpl in *.
      forwards*: IHDisj H0. lia.
  }
  9:{
     apply sub_and in Sub. destruct Sub.
     simpl in *.
     forwards*: IHDisj H1. lia.
  }
  9: {
    forwards*: IHDisj Sub. simpl in *. lia.
  }
  9:{ (*and case: same as above*)
    forwards*: IHDisj Sub. simpl in *. lia.
  }

  15: { (*varl*)    
    inductions Sub; eauto.
    (* union *)
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: disj_regular H1.
    forwards*: disj_regular H2.
    (*and*)
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
    apply* disj_botl.
    forwards*: sub_regular H0.
  }
  15: { (*varr*)
    forwards*: sub_transitivity Sub H0.
  }
  1: { (*bot*)
    forwards*: bot_sub_disjoint Sub A.
  }
  1: { (*bot*)
    apply* disj_botr.
    forwards*: sub_regular Sub.
  }
  1: { (*int arrow*)
    inductions Sub; eauto.
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
  }
  1: { (*int arrow*)
    inductions Sub; eauto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub1 IHn A B. simpl in *. lia.
    forwards*: IHSub2 IHn A B. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub IHn A B. simpl in *. lia.
    forwards*: IHSub IHn A B. simpl in *. lia.
  }
  1: { (*int arrow*)
    inductions Sub; eauto.
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
  }
  1: { (*int arrow*)
  inductions Sub; eauto.
  forwards*: sub_regular Sub1.
  forwards*: sub_regular Sub2.
  forwards*: IHSub1 IHn A B. simpl in *. lia.
  forwards*: IHSub2 IHn A B. simpl in *. lia.
  apply disj_or1 with (A1:=A1) (A2:=A2); auto.
  forwards*: sub_regular Sub1.
  forwards*: sub_regular Sub2.
  forwards*: IHSub IHn A B. simpl in *. lia.
  forwards*: IHSub IHn A B. simpl in *. lia.
 }
   1: { (*int unit*)
    inductions Sub; eauto.
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
  }
  1: { (*int unit*)
    inductions Sub; eauto.
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
  }
    1: { (*all unit*)
      inductions Sub; eauto.
      forwards*: IHSub1 IHn A B. simpl in *. lia.
      forwards*: IHSub2 IHn A B. simpl in *. lia.
      apply disj_or1 with (A1:=A1) (A2:=A2); auto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub IHn A B. simpl in *. lia.
      forwards*: IHSub IHn A B. simpl in *. lia.

      forwards*: sub_regular Sub.
      inverts* H1.
      destructs H4.
      apply* disj_all_intl.
      pick_fresh X.
      apply wft_all with (L:=((((((L \u L0) \u fv_tt S1) \u fv_tt S2) \u fv_tt A) \u
      fv_tt B) \u dom G)); eauto.
      intros.
      forwards*: H3 X0.
      forwards*: sub_regular H10.
      destructs H11.
      rewrite <- (concat_empty_r (G & X0 ~*: A)) in H12.
      rewrite <- (concat_empty_r (G & X0 ~*: A)) in H14.
      forwards: okt_narrow H14 H4.
      forwards: wft_narrow H12 H15.
      rewrite concat_empty_r in H16; auto.
    }
  1: { (*all int*)
    inductions Sub; eauto.
    forwards*: IHSub1. simpl in *. lia.
    forwards*: IHSub2. simpl in *. lia.
    apply disj_or1 with (A1:=A1) (A2:=A2); auto.
    forwards*: sub_regular Sub1.
    forwards*: sub_regular Sub2.
    forwards*: IHSub. simpl in *. lia.
    forwards*: IHSub. simpl in *. lia.
  }
    1: { (*arrow all*)
      inductions Sub; eauto.
      forwards*: IHSub1 IHn A1 B1. simpl in *. lia.
      forwards*: IHSub2 IHn A1 B1. simpl in *. lia.
      apply disj_or1 with (A1:=A3) (A2:=A0); auto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub IHn A1 B1. simpl in *. lia.
      forwards*: IHSub IHn A1 B1. simpl in *. lia.

      forwards* TEMP1: sub_regular Sub.
      inverts H1. inverts* H2.
      destructs TEMP1.
      apply* disj_all_arrl.
      pick_fresh X.
      apply wft_all with (L:=((((((((L \u L0) \u fv_tt A2) \u fv_tt B2) \u
      fv_tt S1) \u fv_tt S2) \u fv_tt A1) \u 
      fv_tt B1) \u dom G)); eauto.
      intros.
      forwards* TEMP2: H3 X0.
      forwards*: sub_regular TEMP2.
      destructs H12.
      rewrite <- (concat_empty_r (G & X0 ~*: A1)) in H13.
      rewrite <- (concat_empty_r (G & X0 ~*: A1)) in H15.
      forwards: okt_narrow H15 H2.
      forwards: wft_narrow H13 H16.
      rewrite concat_empty_r in H17; auto.
    }
    1: { (*int arrow*)
      inductions Sub; eauto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub1 IHn A1 B1. simpl in *. lia.
      forwards*: IHSub2 IHn A1 B1. simpl in *. lia.
      apply disj_or1 with (A1:=A3) (A2:=A0); auto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub IHn A1 B1. simpl in *. lia.
      forwards*: IHSub IHn A1 B1. simpl in *. lia.
    }
    1: { (*all unit*)
      inductions Sub; eauto.
      forwards*: IHSub1 IHn A B. simpl in *. lia.
      forwards*: IHSub2 IHn A B. simpl in *. lia.
      apply disj_or1 with (A1:=A1) (A2:=A2); auto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub IHn A B. simpl in *. lia.
      forwards*: IHSub IHn A B. simpl in *. lia.

      forwards*: sub_regular Sub.
      inverts* H1.
      destructs H4.
      apply* disj_all_nulll.
      pick_fresh X.
      apply wft_all with (L:=((((((L \u L0) \u fv_tt S1) \u fv_tt S2) \u fv_tt A) \u
      fv_tt B) \u dom G)); eauto.
      intros.
      forwards*: H3 X0.
      forwards*: sub_regular H10.
      destructs H11.
      rewrite <- (concat_empty_r (G & X0 ~*: A)) in H12.
      rewrite <- (concat_empty_r (G & X0 ~*: A)) in H14.
      forwards: okt_narrow H14 H4.
      forwards: wft_narrow H12 H15.
      rewrite concat_empty_r in H16; auto.
    }
    1: { (*all unit*)
      inductions Sub; eauto.
      forwards*: IHSub1. simpl in *. lia.
      forwards*: IHSub2. simpl in *. lia.
      apply disj_or1 with (A1:=A1) (A2:=A2); auto.
      forwards*: sub_regular Sub1.
      forwards*: sub_regular Sub2.
      forwards*: IHSub. simpl in *. lia.
      forwards*: IHSub. simpl in *. lia.
    }
    1:{ (*case P*)
        inductions Sub; eauto.
        (*case union*)
        forwards*: IHn (t_prim i) (t_prim j) A1.
        simpl in *. lia.
        forwards*: IHn (t_prim i) (t_prim j) A2.
        simpl in *. lia.
        apply disj_or1 with (A1:=A1) (A2:=A2); auto.
        forwards*: sub_regular Sub1.
        forwards*: sub_regular Sub2.
        (*case and*)
        forwards*: IHn (t_prim i) (t_prim j) A1.
        simpl in *. lia.
        forwards*: IHn (t_prim i) (t_prim j) A2.
        simpl in *. lia.
        (*case P*)
        apply disj_prim; auto.
        assert (EQ: ((n1 :: get_all_subtypes PG (t_prim n1)
        `inter` j :: get_all_subtypes PG (t_prim j)) = []) \/
        ((n1 :: get_all_subtypes PG (t_prim n1)
        `inter` j :: get_all_subtypes PG (t_prim j)) <> [])).
        apply list_empty_decide with (l:=(n1 :: get_all_subtypes PG (t_prim n1)
        `inter` j :: get_all_subtypes PG (t_prim j))).
        destruct EQ as [EQ | EQ]; auto.
        apply not_empty_in_exist with (l:=(n1 :: get_all_subtypes PG (t_prim n1)
        `inter` j :: get_all_subtypes PG (t_prim j))) in EQ.
        destruct EQ as [k IN].
        apply set_inter_elim in IN.
        destruct IN as [IN1 IN2].
        simpl in IN1.
        destruct IN1 as [IN1 | IN1].
        (*case*)
        subst.
        apply nats_to_types_iff in H8.
        assert (IN3: set_In k (i::get_all_subtypes PG (t_prim i))).
        simpl. right; auto.
        forwards*: set_inter_intro eq_dec_nat IN3 IN2.
        rewrite H3 in H9. inverts H9.
        (*case*)
        apply nats_to_types_iff in H8.
        (* assert (Sub1: sub PG E (t_prim k) (t_prim n1)). *)
        forwards* IN3: p_in_sub_nat62 IN1 H8.
        clear IN1.
        assert (IN4: set_In k (i::get_all_subtypes PG (t_prim i))).
        simpl. right; auto.
        clear IN3.
        forwards*: set_inter_intro eq_dec_nat IN4 IN2.
        rewrite H3 in H9. inverts H9.
    }
Qed.

Lemma disj_subst : forall PG Q E F Z A B P,
  PG; (E & Z ~*: Q & F) |= A *a B ->
  PG; E  |= P *a Q ->
  okt PG (E & map (subst_tb Z P) F) ->
  PG; (E & map (subst_tb Z P) F) |= (subst_tt Z P A) *a (subst_tt Z P B).
Proof.
  introv Disj1 Disj2 ok. gen P.
  induction Disj1; intros; auto.
  1: { (*case bot*)
    lets OK: ok_from_okt.
    simpl.
    apply* disj_botl.
    eapply wft_subst_tb; eauto.
    forwards*: disj_regular Disj2.
  }
  1: { (*case bot*)
    lets OK: ok_from_okt.
    simpl.
    apply* disj_botr.
    eapply wft_subst_tb; eauto.
    apply disj_regular in Disj2.
    destructs Disj2; auto.
  }
  1: { (*case int arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [ _ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_int_arrl. 
    forwards: wft_subst_tb H1 WFP OK1.
    simpl in H1. auto.
  }
  1: { (*case int arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_int_arrr.
    forwards: wft_subst_tb H1 WFP OK1.
    simpl in H1. auto.
  }
  1: { (*case unit arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_null_arrl.
    forwards: wft_subst_tb H1 WFP OK1.
    simpl in H1. auto.
  }
  1: { (*case unit arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_null_arrr.
    forwards: wft_subst_tb H1 WFP OK1.
    simpl in H1. auto.
  }
    1: { (*case union*)
    forwards: IHDisj1_1 Disj2; auto.
    forwards: IHDisj1_2 Disj2; auto.
    apply disj_regular in Disj2.
    destructs~ Disj2.
    forwards OK1: ok_from_okt ok; auto.
    eapply disj_or1 with (A1:=(subst_tt Z P A1)) 
    (A2:=(subst_tt Z P A2)); eauto.
    apply wft_subst_tb with (Q:=Q); auto.
    apply* US_after_subst_US.
  }
  1: { (*case union*)
    forwards: IHDisj1_1 Disj2; auto.
    forwards: IHDisj1_2 Disj2; auto.
    apply disj_regular in Disj2.
    destructs~ Disj2.
    forwards OK1: ok_from_okt ok; auto.
    eapply disj_or2 with (B1:=(subst_tt Z P B1)) 
    (B2:=(subst_tt Z P B2)); eauto.
    apply wft_subst_tb with (Q:=Q); auto.
    apply* US_after_subst_US.
  }
  1:{ (*case and*)
    forwards OK1: ok_from_okt ok.
    forwards (_&_&WFP&WFQ): disj_regular Disj2.
    eapply disj_and1 with (A1:=(subst_tt Z P A1)) 
    (A2:=(subst_tt Z P A2)); eauto.
    forwards: wft_subst_tb H WFP OK1; auto.
  }
  1: { (*case and*)
    forwards OK1: ok_from_okt ok.
    forwards (_&_&WFP&WFQ): disj_regular Disj2.
    eapply disj_and2 with (A1:=(subst_tt Z P A1)) 
    (A2:=(subst_tt Z P A2)); eauto.
    forwards: wft_subst_tb H WFP OK1; auto.
  }
  1: { (*case and*)
    forwards OK1: ok_from_okt ok.
    forwards (_&_&WFP&WFQ): disj_regular Disj2.
    eapply disj_and3 with (B1:=(subst_tt Z P B1)) 
    (B2:=(subst_tt Z P B2)); eauto.
    forwards: wft_subst_tb H WFP OK1; auto.
  }
  1: { (*case and*)
    forwards OK1: ok_from_okt ok.
    forwards (_&_&WFP&WFQ): disj_regular Disj2.
    eapply disj_and4 with (B1:=(subst_tt Z P B1)) 
    (B2:=(subst_tt Z P B2)); eauto.
    forwards: wft_subst_tb H WFP OK1; auto.
  }

  1: { (*case all int*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_intl.
    forwards*: wft_subst_tb H1 OK1.
  }
  1: { (*case all int*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_intr.
    forwards*: wft_subst_tb H1 OK1.
  }
  1: { (*case all arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_arrl.
    forwards*: wft_subst_tb H1 OK1.
    forwards*: wft_subst_tb H2 OK1.
  }
  1: { (*case all arrow*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_arrr.
    forwards*: wft_subst_tb H1 OK1.
    forwards*: wft_subst_tb H2 OK1.
  }
  1: { (*case all unit*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_nulll.
    forwards*: wft_subst_tb H1 OK1.
  }
  1: { (*case all unit*)
    simpl.
    apply disj_regular in Disj2.
    destruct Disj2 as [_ [OKE [WFP WFQ]]].
    forwards OK1: ok_from_okt ok.
    apply* disj_all_nullr.
    forwards*: wft_subst_tb H1 OK1.
  }
  1: { (*case fvar*)
     lets OK1: ok_from_okt ok.
     forwards (_&WFA&WFT&OK): sub_regular H0.
     lets OK2: ok_from_okt OK.
     forwards (OKE&ZNE&ZNF&WFQ): okt_concat_inv_tt OK.
     simpl.
     case_var.
     (*case 1: X = Z*)
     (*proveable: T and Q are equal*)
     forwards*: binds_middle_eq_inv H; auto.
     inverts H1.
     forwards: sub_through_subst_tt H0 Disj2 ok.
     (*
       Z is not in Q because Q is well-formed in
       E and Z is not in E 
      *)
     forwards NOTIN: notin_fv_wf WFQ ZNE.
     forwards EQ: subst_tt_fresh P NOTIN.
     (* Search (subst_tt_fresh). *)
     rewrite EQ in H1.
     (* proveable *)
     rewrite <- (concat_empty_r E) in Disj2.
     apply disj_weakening with (F:=(map (subst_tb Z P) F)) in Disj2.
     rewrite concat_empty_r in Disj2.
     apply disj_sym in Disj2.
     forwards*: sub_disjoint3 Disj2 H1.
     apply* disj_sym.
     rewrite~ concat_empty_r.
     (*case 2 X <> Z*)
     (* proveable *)
     forwards Sub2: sub_through_subst_tt H0 Disj2 ok.
     binds_cases H.
     apply disj_fvarl with (T:=T); auto.
     (*
       Z is not in T because T is well-formed in
       E and Z is not in E 
      *)
     forwards WFT': wft_from_env_has_sub OKE B0.
     forwards NOTIN: notin_fv_wf WFT' ZNE.
     forwards EQ: subst_tt_fresh P NOTIN.
     rewrite EQ in Sub2; auto.
     (*another case*)
     clear H0.
     apply disj_fvarl with (T:=subst_tt Z P T); auto.
     apply binds_map with (f:=((subst_tb Z P))) in B0.
     simpl in B0; auto.
  }
  1: { (*case fvar*)
     forwards (_&WFA&WFT&OK): sub_regular H0.
     lets OK1: ok_from_okt OK. 
     forwards (OKE&ZNE&ZNF&WFQ): okt_concat_inv_tt OK.
     simpl.
     case_var.
     (*case 1: X = Z*)
     (*proveable: T and Q are equal*)
     forwards: binds_middle_eq_inv H; auto.
     inverts H1.
     forwards: sub_through_subst_tt H0 Disj2 ok.
     (*
       Z is not in Q because Q is well-formed in
       E and Z is not in E 
      *)
     forwards NOTIN: notin_fv_wf WFQ ZNE.
     forwards EQ: subst_tt_fresh P NOTIN.
     rewrite EQ in H1.
     (* proveable *)
     rewrite <- (concat_empty_r E) in Disj2.
     apply disj_weakening with (F:=(map (subst_tb Z P) F)) in Disj2; auto.
     rewrite concat_empty_r in Disj2.
     apply disj_sym in Disj2.
     forwards*: sub_disjoint3 Disj2 H1.
     rewrite~ concat_empty_r.
     (*case 2 X <> Z*)
     (* proveable *)
     forwards Sub2: sub_through_subst_tt H0 Disj2 ok.
     binds_cases H.
     apply disj_fvarr with (T:=T); auto.
     (*
       Z is not in T because T is well-formed in
       E and Z is not in E 
      *)
     forwards WFT': wft_from_env_has_sub OKE B0.
     forwards NOTIN: notin_fv_wf WFT' ZNE.
     forwards EQ: subst_tt_fresh P NOTIN.
     rewrite EQ in Sub2; auto.
     (*another case*)
     clear H0.
     apply disj_fvarr with (T:=subst_tt Z P T); auto.
     apply binds_map with (f:=((subst_tb Z P))) in B0.
     simpl in B0; auto.
  }
  1:{ (*case P*)
     simpl.
     lets okt: ok_from_okt ok.
     forwards* (_&_&OKP&OKQ): disj_regular Disj2.
     apply disj_prim; auto.
     assert (EQ: t_prim i = subst_tt Z P (t_prim i)).
     simpl. auto.
     rewrite EQ.
     apply wft_subst_tb with (Q:=Q); eauto.
     assert (EQ: t_prim j = subst_tt Z P (t_prim j)).
     simpl. auto.
     rewrite EQ.
     apply wft_subst_tb with (Q:=Q); eauto.
  }
Qed.


Lemma typing_through_subst_te : forall PG Q E F Z e T P,
  typing PG (E & Z ~*: Q & F) e T ->
  PG; E |= P *a Q ->
  okt PG (E & map (subst_tb Z P) F) ->
  typing PG (E & map (subst_tb Z P) F) (subst_te Z P e) (subst_tt Z P T).
Proof.
  introv Typ Disj Ok. gen_eq : (E & Z ~*: Q & F) as G. gen F.
  induction Typ; introv Ok EQ; subst; simpls subst_tt; simpls subst_te.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var.
    binds_cases H1.
   +  apply okt_concat_inv_tt in H. destruct H as [oke [znote [znotf _]]].
     forwards*: wft_from_env_has_typ B0.
     forwards*: notin_fv_wf H.
     forwards*: subst_tt_fresh P H1.
     rewrite H2.
     apply* binds_concat_left.
   + apply* binds_concat_right.
     unsimpl_map_bind.
     apply* binds_map.
  - eapply typ_app; eauto.
  - forwards*: IHTyp F.
    lets TEMP: sub_through_subst_tt.
    specialize (TEMP PG Q E F Z B A P H Disj Ok).
    (apply typ_sub with (B:=(subst_tt Z P B))); auto.
  - pick_fresh y.
    apply typ_abs with (L:=(((((((((L \u \{ Z}) \u fv_ee e) \u fv_te e) \u fv_tt Q) \u fv_tt P) \u
    fv_tt A) \u fv_tt B) \u dom E) \u dom F)); auto.
    intros.
    forwards*: H2 x (F & x ~: A).
    (*repeatition*)
    rewrite map_concat.
    rewrite map_single.
    simpl.
    rewrite concat_assoc.
    apply* okt_typ.
    assert (NOTIN: x \notin L) by auto.
    apply (H1 x) in NOTIN.
    forwards* TEMP: NOTIN.
    apply typing_regular in TEMP. destruct TEMP as [okp [okt [LC _]]].
    apply okt_push_inv in okt. destruct okt as [okt [_ WFA ]].
    forwards*(_&_&WFP&_): disj_regular Disj.
    apply ok_from_okt in Ok.
    forwards*: wft_subst_tb WFA WFP.
    (*repeatition end*)
    rewrite~ concat_assoc.
    rewrite map_concat in H4.
    rewrite map_single in H4.
    unsimpl_map_bind.
    rewrite (subst_te_open_ee_var).
    rewrite~ concat_assoc in H4.
  - pick_fresh y.
    apply typ_typeof with (L:=((((((((((((((L \u \{ Z}) \u fv_ee e) \u fv_ee e1) \u fv_ee e2) \u
        fv_te e) \u fv_te e1) \u fv_te e2) \u 
        fv_tt Q) \u fv_tt P) \u fv_tt A) \u fv_tt B) \u 
        fv_tt C) \u dom E) \u dom F)); auto; intros.
    forwards* : H0 x (F & x ~: A).
    (*repeatition*)
    rewrite map_concat.
    rewrite map_single.
    simpl.
    rewrite concat_assoc.
    apply* okt_typ.
    assert (NOTIN: x \notin L) by auto.
    apply (H x) in NOTIN.
    forwards* TEMP: NOTIN.
    apply typing_regular in TEMP. destruct TEMP as [okp [okt [LC _]]].
    apply okt_push_inv in okt. destruct okt as [okt [_ WFA ]].
    forwards*(_&_&WFP&_): disj_regular Disj.
    apply ok_from_okt in Ok.
    forwards*: wft_subst_tb WFA WFP.
    (*repeatition end*)
    rewrite~ concat_assoc.
    rewrite map_concat in H5.
    rewrite map_single in H5.
    unsimpl_map_bind.
    rewrite concat_assoc in H5.
    rewrite~ subst_te_open_ee_var.
    forwards*: H2 x (F & x ~: B).
    (*repeatition*)
    rewrite map_concat.
    rewrite map_single.
    simpl.
    rewrite concat_assoc.
    apply* okt_typ.
    assert (NOTIN: x \notin L) by auto.
    apply (H1 x) in NOTIN.
    forwards* TEMP: NOTIN.
    apply typing_regular in TEMP. destruct TEMP as [okp [okt [LC _]]].
    apply okt_push_inv in okt. destruct okt as [okt [_ WFA ]].
    forwards*(_&_&WFP&_): disj_regular Disj.
    apply ok_from_okt in Ok.
    forwards*: wft_subst_tb WFA WFP.
    (*repeatition end*)
    rewrite~ concat_assoc.
    rewrite map_concat in H5.
    rewrite map_single in H5.
    unsimpl_map_bind.
    rewrite concat_assoc in H5.
    rewrite~ subst_te_open_ee_var.
    (* lemma that substitution preserves disjointness *)
    forwards*: disj_subst H3 Disj.
  - apply* typ_inter.
  - pick_fresh Y.
    apply typ_tabs with (L:=(((((((((L \u \{ Z}) \u fv_ee e) \u fv_te e) 
    \u fv_tt Q) \u fv_tt P) \u
    fv_tt A) \u fv_tt B) \u dom E) \u dom F)); auto.
    intros.
    forwards*: H1 X.
    forwards*: H2 X (F & X ~*: A).
        (*repeatition*)
    rewrite map_concat.
    rewrite map_single.
    simpl.
    rewrite concat_assoc.
    apply* okt_disj.
    assert (NOTIN: X \notin L) by auto.
    apply (H1 X) in NOTIN.
    forwards* TEMP: NOTIN.
    apply typing_regular in TEMP. destruct TEMP as [okp [okt [LC _]]].
    apply okt_push_inv_tt in okt. destruct okt as [okt [_ WFA ]].
    forwards*(_&_&WFP&_): disj_regular Disj.
    apply ok_from_okt in Ok.
    forwards*: wft_subst_tb WFA WFP.
    forwards* (_&TEMP1&_): typing_regular H4.
    apply okt_push_inv_tt in TEMP1. destructs TEMP1.
    forwards* (_&TEMP1&WFP&_): disj_regular Disj.
    (*repeatition end*)
    rewrite~ concat_assoc.
    forwards*: disj_regular Disj.
    rewrite map_concat in H5.
    rewrite map_single in H5.
    unsimpl_map_bind.
    rewrite~ subst_te_open_te_var.
    rewrite~ concat_assoc in H5.
    rewrite~ subst_tt_open_tt_var.
    forwards*(_&_&WFP&_): disj_regular.
    apply type_from_wft in WFP; auto.
    forwards*(_&_&WFP&_): disj_regular.
    apply type_from_wft in WFP; auto.
  - rewrite subst_tt_open_tt.
    apply* typ_tapp.
    (* lemma that substitution preserves disjointness *)
    forwards*: disj_subst H Disj.
    apply disj_regular in Disj. destructs Disj.
    apply type_from_wft in H2; auto.
  - (*case P*)
    apply* typ_prim.
    assert (EQ: (t_prim i) = ((subst_tt Z P) (t_prim i))).
    simpl. auto. rewrite EQ.
    apply* wft_subst_tb.
    forwards*: disj_regular Disj.
    apply* ok_from_okt.
Qed.


(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma inv_int : forall PG E A i5,
typing PG E (e_lit i5) A -> typing PG E (e_lit i5) t_int /\ sub PG E t_int A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - specialize (IHTyp i5).
  forwards* : IHTyp. destruct H0.
  split*.
  eapply sub_transitivity; eauto.
  - forwards* : IHTyp1. destruct H.
    forwards* : IHTyp2.
Qed.

Lemma abs_typ_arrow_sub : forall PG G e A,
typing PG G (e_abs e) A ->
exists A1 B1, sub PG G (t_arrow A1 B1) A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards* : IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply sub_transitivity; eauto.
    - exists* A B.
      pick_fresh x.
      forwards* : H1 x.
      apply typing_regular in H3. destructs H3.
      apply okt_push_inv in H4. destructs~ H4.
      rewrite (@append_empty_right (G & x ~: A)) in H6.
      apply wft_strengthen in H6.
      rewrite~ <- (@append_empty_right G) in H6.
    - forwards* : IHTyp1.
      forwards* : IHTyp2.
      destruct H as [x1 [x2 H3]].
      destruct H0 as [x3 [x4 H4]].
      exists t_top t_bot.
      apply s_anda.
      forwards* : sub_regular H3. destructs H.
      apply typing_regular in Typ1. destructs~ Typ1. inverts H0.
      assert (sub PG G (t_arrow t_top t_bot) (t_arrow x1 x2)); eauto.
      eapply sub_transitivity; eauto.
      forwards* : sub_regular H4. destructs H.
      apply typing_regular in Typ2. destructs Typ2. inverts H0.
      assert (sub PG G (t_arrow t_top t_bot) (t_arrow x3 x4)); eauto.
      eapply sub_transitivity; eauto.
Qed.

Lemma abs_typ_all_sub : forall PG G e A B,
typing PG G (e_tabs A e) B ->
exists A1 B1, sub PG G (t_all A1 B1) B.
Proof.
    introv Typ.
    inductions Typ.
    - forwards* : IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply sub_transitivity; eauto.
    - forwards~ : IHTyp1.
      forwards~ : IHTyp2.
      destruct H as [x1 [x2 H3]].
      destruct H0 as [x3 [x4 H4]].
      exists t_bot t_bot.
      apply s_anda.
      + forwards* (?&?&?&?): sub_regular H3.
        inverts H0. 
        assert (sub PG G (t_all t_bot t_bot) (t_all x1 x2)); auto.
        pick_fresh Y.
        apply s_all with (L:=((((((((((L \u fv_ee e) \u fv_te e) 
          \u fv_tt A) \u fv_tt A0) \u fv_tt B) \u
          fv_tt x1) \u fv_tt x2) \u fv_tt x3) \u fv_tt x4) \u 
    dom G)); intros; auto.
        eapply sub_transitivity; eauto.

      + forwards* (?&?&?&?): sub_regular H4.
        inverts H0. 
        assert (sub PG G (t_all t_bot t_bot) (t_all x3 x4)).
        pick_fresh Y.
        apply s_all with (L:=((((((((((L \u fv_ee e) \u fv_te e) 
          \u fv_tt A) \u fv_tt A0) \u fv_tt B) \u
          fv_tt x1) \u fv_tt x2) \u fv_tt x3) \u fv_tt x4) \u 
          dom G)); intros; auto.
        eapply sub_transitivity; eauto.

    - exists t_bot t_bot.
      pick_fresh Y.
      apply s_all with (L:=(((((L \u fv_ee e) \u fv_te e) 
        \u fv_tt A) \u fv_tt B) \u dom G)); intros; auto.
      forwards* : H1 Y.
      forwards* (?&?&?&?) : typing_regular H3.
      apply okt_push_inv_tt in H5. destructs~ H5.
      forwards* : H1 X.
      forwards* (?&?&?&?) : typing_regular H4.
Qed.

Lemma inv_and_arrow : forall PG G e A1 A2 B1 B2,
  typing PG G (e_abs e) (t_and A1 A2) ->
  sub PG G (t_and A1 A2) (t_arrow B1 B2) ->
  sub PG G A1 (t_arrow B1 B2) \/ sub PG G A2 (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
Qed.

Lemma inv_and_all : forall PG G e A1 A2 B1 B2 A,
  typing PG G (e_tabs A e) (t_and A1 A2) ->
  sub PG G (t_and A1 A2) (t_all B1 B2) ->
  sub PG G A1 (t_all B1 B2) \/ sub PG G A2 (t_all B1 B2).
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
Qed.

Lemma inv_abs_sub : forall PG G e A B1 B2,
    typing PG G (e_abs e) A ->
    sub PG G A (t_arrow B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing PG (G & x ~: C1) (e open_ee_var x) C2)
           /\ sub PG G (t_arrow C1 C2) (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: sub PG G B (t_arrow B1 B2)) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* [HS|HS]: inv_and_arrow Sub.
Qed.

Lemma inv_all_sub : forall PG G e A B B1 B2,
    typing PG G (e_tabs A e) B ->
    sub PG G B (t_all B1 B2) ->
         exists C1 C2,
           (exists L, forall X , X \notin  L -> typing PG (G & X ~*: B1) (e open_te_var X) (C2 open_tt_var X))
           /\ sub PG G (t_all C1 C2) (t_all B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: sub PG G B (t_all B1 B2)) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* : inv_and_all Sub.
  - exists* A B. split*.
    exists L. intros.
    inverts Sub.
    forwards*: H1 X.
    rewrite (append_empty_right (G & X ~*: B1)).
    apply typing_narrowing with (P:=A); auto.
    rewrite~ concat_empty_r.
Qed.

Lemma inv_arrow : forall PG G e A1 A2,
    typing PG G (e_abs e) (t_arrow A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing PG (G & x ~: B1) (e open_ee_var x) B2)
                  /\ sub PG G (t_arrow B1 B2) (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards* : inv_abs_sub H.
  - exists A1 A2. split*.
    pick_fresh x.
    forwards* : H5 x.
    forwards* (?&?&?&?): typing_regular H.
    apply okt_push_inv in H1. destructs H1.
    rewrite (@append_empty_right (G & x ~: A1)) in H6.
    apply wft_strengthen in H6.
    rewrite~ <- (@append_empty_right G) in H6.
Qed.

Lemma inv_all : forall PG G e A A1 A2,
    typing PG G (e_tabs A e) (t_all A1 A2) ->
    exists B1 B2, (exists L, forall X , X \notin  L -> typing PG (G & X ~*: A1) (e open_te_var X) (B2 open_tt_var X))
                  /\ sub PG G (t_all B1 B2) (t_all A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards* : inv_all_sub H.
  - exists A1 A2. split*.
    pick_fresh Y.
    apply s_all with (L:=(((((L \u fv_ee e) \u fv_te e) 
      \u fv_tt A1) \u fv_tt A2) \u dom G)); intros; auto.
    forwards* : H6 Y.
    forwards*(?&?&?&?): typing_regular H.
    apply okt_push_inv_tt in H1. destructs~ H1.
    forwards* : H6 X.
    apply typing_regular in H0. destructs H0.
    apply okt_push_inv_tt in H1. destructs~ H1.
Qed.

Lemma inv_abs_union : forall PG G e A A1 A2,
    typing PG G (e_abs e) A ->
    sub PG G A (t_union A1 A2) ->
    typing PG G (e_abs e) A1 \/ typing PG G (e_abs e) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts* Sub.
  - inverts* Sub.
Qed.

Lemma inv_all_union : forall PG G e A B A1 A2,
    typing PG G (e_tabs A e) B ->
    sub PG G B (t_union A1 A2) ->
    typing PG G (e_tabs A e) A1 \/ typing PG G (e_tabs A e) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts* Sub.
  - inverts* Sub.
Qed.

Lemma inv_null : forall PG E A,
typing PG E e_null A -> typing PG E e_null t_unit /\ sub PG E t_unit A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - split*.
  (*case typ_sub*)
 - forwards* : IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
 - forwards* : IHTyp1.
Qed.

(*
e = \x.x
\x.x : (Int -> Int) /\ (Bool -> Bool) | (Int -> Int) /\ (Bool -> Bool)

\x.x : (Int -> Int) /\ (Bool -> Bool)
\x.x : (Int -> Int) /\ (Bool -> Bool)
*)

Lemma inv_P : forall PG E P A,
typing PG E (e_new P) A -> typing PG E (e_new P) (t_prim P) /\ sub PG E (t_prim P) A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_int*)
 - forwards*: IHTyp. destruct H0.
   split*.
   eapply sub_transitivity; eauto.
  (*case typ_sub*)
 - forwards*: IHTyp1.
   forwards*: IHTyp2.
 - (*Case P*)
    split*.
Qed.

Lemma check_or_typ : forall PG E e A B,
   value e ->
   typing PG E e (t_union A B) ->
   typing PG E e A \/ typing PG E e B.
Proof.
  introv Val Typ.
  inverts Val.
  (*subsumption again*)
 - apply inv_int in Typ. destruct Typ.
   inverts* H0.
 - inverts Typ.
   eapply inv_abs_union in H0; eauto.
 - apply inv_null in Typ. destruct Typ.
   inverts* H0.
 - inverts Typ.
   eapply inv_all_union in H0; eauto.
 - apply inv_P in Typ. destruct Typ.
   inverts* H0.
Qed.

Lemma uord_sub_union : forall PG E B B1 B2,
  US B B1 B2 ->
  forall A, Ord A ->
  sub PG E A B ->
  sub  PG E A B1 \/ sub PG E A B2.
Proof.
  induction 1;
  introv Ord Sub.
  inverts Ord; inverts* Sub.
  1,2: apply sub_and in Sub;
       forwards*: IHUS Ord.
Qed.

Lemma sub_ord_disjoint_types : forall PG E A B,
  PG; E |= A *a B ->
  forall C, Ord C ->
  sub PG E C A ->
  sub PG E C B -> False.
Proof.
  introv Disj Ord SubA SubB.
  gen C.
  induction Disj; intros.
  (*trivial cases*)
  all: try solve [ 
    inverts Ord; inverts SubA;
    inverts SubB
    ].
  1: eapply uord_sub_union in SubA; eauto.
    destruct SubA; eauto.
  1: eapply uord_sub_union in SubB; eauto.
    destruct SubB; eauto.
  1,2: apply sub_and in SubA;
    destruct SubA; eauto.
  1,2: apply sub_and in SubB;
    destruct SubB; eauto.
    (*case P*)
  1: inverts Ord; try solve [inverts SubB].
     forwards*: p_sub_getallsubtypes_not_empty SubA SubB.
Qed.


(********************************************************)
(** A value cannot check against disjoint types **)

Lemma val_check_disjoint_types : forall PG E v A B,
  PG; E |= A *a B ->
  value v ->
  typing PG E v A ->
  typing PG E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  inverts Val.
  - apply inv_int in Typ1. destruct Typ1.
    apply inv_int in Typ2. destruct Typ2.
    forwards*: sub_ord_disjoint_types Disj H0 H2.
  - apply abs_typ_arrow_sub in Typ1.
    destruct Typ1 as [A1 [B1]].
    assert (sub PG E (t_arrow t_top t_bot) (t_arrow A1 B1)).
    forwards* (?&?&?&?): sub_regular H0. inverts* H2. 
    apply abs_typ_arrow_sub in Typ2.
    destruct Typ2 as [A2 [B2]].
    assert (sub PG E (t_arrow t_top t_bot) (t_arrow A2 B2)).
    forwards* (?&?&?&?): sub_regular H2. inverts* H4.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A1 B1)) (C:=A) in H1; auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A2 B2)) (C:=B) in H3; auto.
    forwards*: sub_ord_disjoint_types Disj H1 H3.
  - apply inv_null in Typ1. destruct Typ1.
    apply inv_null in Typ2. destruct Typ2.
    forwards*: sub_ord_disjoint_types Disj H0 H2.
  - apply abs_typ_all_sub in Typ1.
    destruct Typ1 as [A1 [B1]].
    forwards* (?&?&?&?): sub_regular H0.
    inverts H2.
    assert (sub PG E (t_all t_bot t_bot) (t_all A1 B1)).
    pick_fresh Y.
    apply s_all with (L:=((((((((L \u fv_ee e) \u fv_te e) 
      \u fv_tt A) \u fv_tt B) \u fv_tt T) \u
      fv_tt A1) \u fv_tt B1) \u dom E)); intros; auto.
    apply abs_typ_all_sub in Typ2.
    destruct Typ2 as [A2 [B2]].
    forwards* (?&?&?&?): sub_regular H5.
    inverts H7.
    assert (sub PG E (t_all t_bot t_bot) (t_all A2 B2)).
    pick_fresh Y.
    apply s_all with (L:=(((((((((((L \u L0) \u fv_ee e) \u fv_te e) 
      \u fv_tt A) \u fv_tt B) \u fv_tt T) \u fv_tt A2) \u fv_tt B2) 
      \u fv_tt A1) \u fv_tt B1) \u dom E)); intros; auto.
    eapply sub_transitivity with (A:=(t_all t_bot t_bot)) (B:=(t_all A1 B1)) (C:=A) in H0; auto.
    eapply sub_transitivity with (A:=(t_all t_bot t_bot)) (B:=(t_all A2 B2)) (C:=B) in H5; auto.
    forwards*: sub_ord_disjoint_types Disj H0 H5.
  - apply inv_P in Typ1. destruct Typ1.
    apply inv_P in Typ2. destruct Typ2.
    forwards*: sub_ord_disjoint_types Disj H0 H2.
Qed.

(*******************************************************)
(** findtype gives least type of an expressions **)

Lemma check_find_type : forall PG E e A B,
typing PG E e A ->
findtype e B ->
sub PG E B A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ.
    destruct~ Typ.
  - apply abs_typ_arrow_sub in Typ.
    destruct Typ as [A1 [B1]].
    forwards* (?&?&?&?): sub_regular H0. inverts H2.
    assert (sub PG E (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
    eapply sub_transitivity; eauto.
  - apply inv_null in Typ. destruct~ Typ.
  - apply abs_typ_all_sub in Typ.
    destruct Typ as [A1 [B1]].
    forwards* (?&?&?&?): sub_regular H. inverts H1.
    assert (sub PG E (t_all t_bot t_bot) (t_all A1 B1)).
    pick_fresh Y.
    apply s_all with (L:=(((((((L \u fv_ee e) \u fv_te e) \u fv_tt A) 
    \u fv_tt T) \u fv_tt A1) \u fv_tt B1) \u dom E)); intros; auto.
    eapply sub_transitivity; eauto.
  - apply inv_P in Typ. destruct~ Typ.
Qed.

(********************************************)
(** Values have ordinary types **)

Lemma findtype_ord_type : forall v A,
  findtype v A ->
  Ord A.
Proof.
  introv Find.
  inverts* Find.
Qed.

(*******************************)
(****  Preservation Lemma  *****)
(*******************************)

Lemma preservation : forall PG E e e' T,
  typing PG E e T ->
  step PG E e e' ->
  typing PG E e' T.
Proof.
  introv Typ. gen e'.
  induction Typ; introv Red; try solve [ inverts* Red ].
  - (* app *)
    inverts* Red.
    (* beta *)
        forwards* : inv_arrow Typ1.
        destruct H as [A1[B1 [H H']]]. 
        destruct H as [L].
        pick_fresh x.
        assert (x \notin L) by auto.
        lets: H x H0.
        assert (G & x ~: A1 = G & x ~: A1 & empty).
        rewrite* concat_empty_r.
        rewrite H4 in H2.
        assert (G = G & empty).
        rewrite* concat_empty_r. rewrite H5.
        lets: typing_through_subst_ee.
        inverts H'.
        forwards* : H6 H2.
        rewrite* (@subst_ee_intro x).
        apply typ_sub with (B:=B1). auto.
        rewrite concat_empty_r. auto.
  - (* typeof *)
    inverts* Red.
    
    + (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*true goal*)
       pick_fresh y. assert (y \notin L) by auto.
       forwards* : H H5.
       assert  (G & y ~: A = G & y ~: A & empty).
       rewrite* concat_empty_r. rewrite H7 in H6.
       assert (G = G & empty).
       rewrite* concat_empty_r.
       rewrite H8.
       forwards* : typing_through_subst_ee.
       rewrite* (@subst_ee_intro y).
     * (*false goal, value e checks against disjoint types A and B*)
       lets temp1: check_find_type G e B C0 H4.
       lets SubB: temp1 H12.
       inverts H12;
       forwards*: sub_ord_disjoint_types H3 H13 SubB.
    +  (* value checks against disjoint types *)
      lets temp: check_or_typ G e A B H11.
      lets DisjOr: temp Typ.
      destruct DisjOr.
     * (*false goal, value e checks against disjoint types A and B*)
        lets temp1: check_find_type G e A C0 H4.
        lets SubA: temp1 H12.
        inverts H12;
        forwards*: sub_ord_disjoint_types H3 SubA H13.
     * (*true goal*)
        pick_fresh y. assert (y \notin L) by auto.
        forwards* : H1 H5.
        assert  (G & y ~: B = G & y ~: B & empty).
        rewrite* concat_empty_r. rewrite H7 in H6.
        assert (G = G & empty).
        rewrite* concat_empty_r.
        rewrite H8.
        forwards* : typing_through_subst_ee.
        rewrite* (@subst_ee_intro y).
    - forwards* : IHTyp1.
    - (* case tapp *)
      inverts* Red.
      clear IHTyp.
      forwards* : inv_all Typ.
      destruct H0 as [A1[B1 [H' H'']]].
      destruct H' as [L].
      (*
       G |- A1 <: B
       G, X * B |- B1^X <: C^X
        A *s B
        A1 * A
       *)
      inverts H''.
      pick_fresh X.
      forwards*: H0 X.
      forwards*: H9 X.
      rewrite* (@subst_te_intro X).
      rewrite* (@subst_tt_intro X).
      rewrite (append_empty_right G).
      rewrite <- (map_empty ((subst_tb X A))).
      apply* (typing_through_subst_te PG B).
      rewrite* concat_empty_r.
      rewrite* map_empty.
      rewrite concat_empty_r.
      forwards*: sub_regular H7.
Qed.


(*******************************)
(******  Progress Lemma  *******)
(*******************************)

Lemma progress : forall PG e T,
typing PG empty e T -> (value e) \/ (exists e', step PG empty e e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 (*case null*)
 - left*.
 (*case var*)
 - apply binds_empty_inv in H1. inversion H1.
 (*case typ-app*)
 -  right. forwards* : IHTyp1.
   destruct H.
  + forwards* : IHTyp2.
    destruct H0.
   * inverts* H.
     (*i infers arrow*)
     apply inv_int in Typ1.
     destruct Typ1.
     inverts H1.
     apply inv_null in Typ1.
     destruct Typ1.
     inverts H1.
     apply abs_typ_all_sub in Typ1.
     destruct Typ1 as [A1 [B1]]. inverts H.
     apply inv_P in Typ1. destruct Typ1.
     inverts H1.
     (*case step-appl*)
   * destruct H0.
     exists* (e_app e1 x).
   (*case step-appr*)
  + destruct H.
    exists (e_app x e2). apply* step_appl.
    forwards* : typing_regular Typ2.
(*case typ-sub*)
 - forwards* : IHTyp.
(*case typ-abs*)
 - left. forwards* : typing_regular Typ'.
(*case typ-typeof*)
 - right. forwards* : IHTyp. 
   destruct H4.
  + apply check_or_typ in Typ; auto.
    destruct Typ.
    (*case typeofl*)
   * destruct H4.
     { (*case e = int*)
      apply inv_int in H5. destruct H5.
      exists (open_ee e1 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H y H6.
      eapply step_typeofl with (C:=t_int); eauto.
      forwards* : typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      forwards* : sub_regular H5. destructs H6. inverts H7.
      assert (sub PG empty (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H5; eauto.
      exists (open_ee e1 (e_abs e)).
      pick_fresh y.
      forwards*: H y.
      eapply step_typeofl with (C:=(t_arrow t_top t_bot)); eauto.
      forwards* : typing_regular Typ'.
     }
     {
       (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_ee e1 e_null).
       pick_fresh y.
       assert (y \notin L) by auto.
       lets: H y H6.
       eapply step_typeofl with (C:=t_unit); eauto.
       forwards* : typing_regular Typ'.
     }
     {
       (* case e = e A *)
       apply abs_typ_all_sub in H5.
       destruct H5 as [A1 [B1]].
       forwards*(?&?&?&?): sub_regular H5. inverts H7.
       assert (sub PG empty (t_all t_bot t_bot) (t_all A1 B1)).
       pick_fresh Y.
       apply s_all with (L:=(((((((((((((L \u L0) \u fv_ee e1) 
         \u fv_ee e2) \u fv_ee e) \u fv_te e1) \u
         fv_te e2) \u fv_te e) \u fv_tt A) \u fv_tt B) \u 
         fv_tt C) \u fv_tt T) \u fv_tt A1) \u fv_tt B1)); auto.
       eapply sub_transitivity in H5; eauto.
       exists (open_ee e1 (e_tabs T e)).
       pick_fresh y.
       forwards*: H y.
       eapply step_typeofl with (C:=(t_all t_bot t_bot)); eauto.
       forwards* : typing_regular Typ'.
     }
     {
       (* case e = e_new *)
       apply inv_P in H5. destruct H5.
       exists (open_ee e1 (e_new P)).
       pick_fresh y.
       assert (y \notin L) by auto.
       lets: H y H6.
       eapply step_typeofl with (C:=(t_prim P)); eauto.
       forwards* : typing_regular Typ'.
     }
   * (*case typeofr*)
     destruct H4.
     apply inv_int in H5. destruct H5.
     { (*case e = int*)
      exists (open_ee e2 (e_lit i5)).
      pick_fresh y.
      assert (y \notin L) by auto.
      lets: H1 y H6.
      eapply step_typeofr with (C:=t_int); eauto.
      forwards* : typing_regular Typ'.
     }
     { (*case e = \x.e*)
      apply abs_typ_arrow_sub in H5.
      destruct H5 as [A1 [B1]].
      forwards* : sub_regular H5. destructs H6. inverts H7.
      assert (sub PG empty (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
      eapply sub_transitivity in H5; eauto.
      exists (open_ee e2 (e_abs e)).
      pick_fresh y.
      forwards*: H1 y.
      eapply step_typeofr with (C:=(t_arrow t_top t_bot)); eauto.
      forwards* : typing_regular Typ'.
     }
     { (*case e = null*)
       apply inv_null in H5. destruct H5.
       exists (open_ee e2 e_null).
       pick_fresh y.
       forwards*: H y.
       eapply step_typeofr with (C:=t_unit); eauto.
       forwards* : typing_regular Typ'.
     }
     {
       (* case e = e A *)
       apply abs_typ_all_sub in H5.
       destruct H5 as [A1 [B1]].
       forwards*(?&?&?&?): sub_regular H5. inverts H7.
       assert (sub PG empty (t_all t_bot t_bot) (t_all A1 B1)).
       pick_fresh Y.
       apply s_all with (L:=((((((((((((L \u L0) \u fv_ee e1) 
         \u fv_ee e2) \u fv_ee e) \u fv_te e1) \u
         fv_te e2) \u fv_te e) \u fv_tt A) \u fv_tt B) \u 
         fv_tt C) \u fv_tt T) \u fv_tt A1) \u fv_tt B1); auto.
       eapply sub_transitivity in H5; eauto.
       exists (open_ee e2 (e_tabs T e)).
       pick_fresh y.
       forwards*: H y.
       eapply step_typeofr with (C:=(t_all t_bot t_bot)); eauto.
       forwards* : typing_regular Typ'.
     }
     {
       (* case e = e_new *)
       apply inv_P in H5. destruct H5.
       exists (open_ee e2 (e_new P)).
       pick_fresh y.
       forwards*: H y.
       eapply step_typeofr with (C:=(t_prim P)); eauto.
       forwards* : typing_regular Typ'.       
     }
  + (*case typeof*)
    destruct H4.
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards* : typing_regular Typ'.
  - forwards* : IHTyp1.
  - left. apply* val_tabs.
    forwards* : typing_regular Typ'.
 - (*case typ-app*) 
   right. forwards* : IHTyp.
   destruct H0 as [TEMP1 | TEMP1].
  + inverts* TEMP1.
     (*i infers arrow*)
     apply inv_int in Typ.
     destruct Typ.
     inverts H1.
     apply abs_typ_arrow_sub in Typ.
     destruct Typ as [A1 [B1]]. inverts H1.
     apply inv_null in Typ.
     destruct Typ.
     inverts H1.
     exists ((open_te e0 A)).
     apply* step_tabs.
     apply typing_regular in Typ'. destructs~ Typ'.
     inverts~ H3.
     apply inv_P in Typ. destruct Typ.
     inverts H1.
     (*case step-appl*)
   + destruct TEMP1.
     exists* (e_tapp x A).
     apply* step_tapp.
     apply typing_regular in Typ'. destructs Typ'.
     inverts~ H3.
  - (*case P*)
    left*.
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

Lemma inv_app : forall PG E e1 e2 A,
typing PG E (e_app e1 e2) A ->
exists A1 B1, typing PG E e1 (t_arrow A1 B1) /\ typing PG E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
 - exists* A B.
 - specialize (IHTyp e1 e2).
  forwards* : IHTyp.
 - forwards* : IHTyp1.
Qed.

Lemma inv_typeof : forall PG E e e1 e2 A B C,
typing PG E (e_typeof e A e1 B e2) C ->
exists D, typing PG E e D /\ PG; E |= A *a B.
Proof.
  introv Typ.
  inductions Typ.
  - specialize (IHTyp e e1 e2 A B).
    forwards* : IHTyp.
  - exists* (t_union A B).
  - forwards* : IHTyp1.
Qed.

Lemma inv_tapp : forall PG E e A B,
typing PG E (e_tapp e A) B ->
exists A1 A2, typing PG E e (t_all A1 A2).
Proof.
  introv Typ.
  inductions Typ.
  - forwards* : IHTyp.
  - forwards* : IHTyp1.
  - exists* B C.
Qed.

(********************************************)
(** Value is normal form **)

Lemma value_not_step : forall PG E v e',
  value v ->
  step PG E v e' -> False.
Proof.
  intros.
  inverts H; try solve [inverts H0].
Qed.

(********************************************)
(** findtype uniqueness **)

Lemma findtype_unique : forall v A B,
  findtype v A ->
  findtype v B ->
  A = B.
Proof.
  introv TypA TypB.
  inverts TypA;
  inverts* TypB.
Qed.

Lemma determinism : forall PG E e e1 e2 A, 
  typing PG E e A ->
  step PG E e e1 -> step PG E e e2 -> e1 = e2.
Proof.
  introv Typ He1. gen e2 A.
  induction He1; introv Typ He2.
  (*case step-appl*)
  - inverts* He2.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards* : IHHe1. rewrite* H3.
   + inverts* H2; inverts He1.
   + inverts* He1.
(*case step-appr*)
  - inverts* He2.
   + inverts* H; inverts* H4.
   + apply inv_app in Typ.
     destruct Typ as [A1 [B1]]. destruct H0.
     forwards* : IHHe1 H1. rewrite* H3.
   + inverts H4; inverts He1.
(*case step-beta*)
  - inverts* He2.
   + inverts* H5.
   + inverts H0; inverts H5.
(*case step-typeof*)
 - inverts* He2.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H0.
    forwards* : IHHe1. rewrite* H2.
  + inverts H8; inverts He1.
  + inverts H8; inverts He1.
(*case step-typeofl*)
 - inverts* He2.
  + apply value_not_step in H10; eauto.
    inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    forwards*: findtype_unique H1 H11. subst.
    forwards*: findtype_ord_type H1.
    forwards*: sub_ord_disjoint_types Disj H2 H12.
(*case step-typeofr*)
- inverts* He2.
  + inverts H0; inverts H10.
  + apply inv_typeof in Typ.
    destruct Typ as [D]. destruct H3 as [H3 Disj].
    forwards*: findtype_unique H1 H11. subst.
    forwards*: findtype_ord_type H1.
    forwards*: sub_ord_disjoint_types Disj H12 H2.
(*case step-tapp*)
- inverts He2.
  + apply inv_tapp in Typ.
    destruct Typ as [A1 [A2]].
    forwards* : IHHe1 H0.
    rewrite~ H1.
  + inverts He1.
- inverts* He2. inverts H5.
Qed.