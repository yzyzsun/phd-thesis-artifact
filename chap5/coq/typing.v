(*

This file contains \um calculus,
which corresponds to chapter 5 in thesis.

Feb 07, 2023:
------------------
-> no disjointness and no determinism
-> type assignment system
-> Progress and Preservation
-> Fix point
-> reduced annotations from values
-> drop annotations from application typing rule

March 14, 2023:
-----------------
-> From typing_standard_app.v in simple-design

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.
Require Import Program.Equality.
(* Require Import Coq.Lists.ListSet. *)
From Coq Require Export Lists.List.
Export ListNotations.
(* Require Import Coq.Strings.String. *)
Require Import Lia.

Require Import syntax.


(*******************************)
(*******************************)

(* Typing Part *)

(*******************************)
(*******************************)


Inductive exp : Set :=  (*r expression *)
 | e_var_b  : nat -> exp
 | e_var_f  : var -> exp
 | e_lit    : nat -> exp
 | e_ann    : exp -> typ -> exp
 | e_abs    : exp -> typ -> typ -> exp
 | e_app    : exp -> exp -> exp
 | e_merg   : exp -> exp -> exp
 | e_top    : exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_fix    : exp -> typ -> exp.


(** Environment is an associative list of bindings. *)

Definition ctx : Set := list ( atom * typ ).


(** opening up abstractions *)
Fixpoint open_exp_wrt_exp_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_var_b nat) => if (k == nat) then e_5 else (e_var_b nat)
  | (e_var_f x) => e_var_f x
  | (e_lit i5) => e_lit i5
  | (e_ann e A) => e_ann (open_exp_wrt_exp_rec k e_5 e) A
  | (e_abs e A B) => e_abs (open_exp_wrt_exp_rec (S k) e_5 e) A B
  | (e_app e1 e2) => e_app (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | (e_merg e1 e2) => e_merg (open_exp_wrt_exp_rec k e_5 e1) (open_exp_wrt_exp_rec k e_5 e2)
  | e_top         => e_top
  | (e_typeof e A e1 B e2) => e_typeof (open_exp_wrt_exp_rec k e_5 e) A (open_exp_wrt_exp_rec (S k) e_5 e1) B (open_exp_wrt_exp_rec (S k) e_5 e2)
  | (e_fix e A) => e_fix (open_exp_wrt_exp_rec (S k) e_5 e) A
  end.

Definition open_exp_wrt_exp e_5 e__6 := open_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_exp_wrt_exp t (e_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     (lc_exp (e_var_f x))
 | lc_e_lit : forall i5,
     (lc_exp (e_lit i5))
 | lc_e_ann : forall (e:exp) (A:typ),
     (lc_exp e) ->
     (lc_exp (e_ann e A))
 | lc_e_abs : forall (L:vars) (e:exp) A B,
      ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e (e_var_f x) )  )  ->
     (lc_exp (e_abs e A B))
 | lc_e_app : forall (e1 e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_app e1 e2))
 | lc_e_merg : forall (e1:exp) (e2:exp),
     (lc_exp e1) ->
     (lc_exp e2) ->
     (lc_exp (e_merg e1 e2))
 | lc_e_top :
      lc_exp e_top
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     (lc_exp e) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e1 (e_var_f x) )  ) ->
     ( forall x , x \notin  L  -> lc_exp  ( open_exp_wrt_exp e2 (e_var_f x) )  ) ->
     (lc_exp (e_typeof e A e1 B e2))
 | lc_fix : forall (L:vars) (e:exp) A,
      (forall x , x \notin L -> lc_exp (open_exp_wrt_exp e (e_var_f x)))  ->
      lc_exp (e_fix e A).

#[export]
Hint Constructors lc_exp uniq : core.

(** free variables *)
Fixpoint fv_exp (e_5:exp) : vars :=
  match e_5 with
  | (e_var_b nat) => {}
  | (e_var_f x) => {{x}}
  | (e_lit i5) => {}
  | (e_ann e A) => (fv_exp e)
  | (e_abs e A B) => (fv_exp e)
  | (e_app e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_merg e1 e2) => (fv_exp e1) \u (fv_exp e2)
  | (e_top)       => {}
  | (e_typeof e A e1 B e2) => (fv_exp e) \u (fv_exp e1) \u (fv_exp e2)
  | (e_fix e A) => fv_exp e
end.

(** substitutions *)
Fixpoint subst_exp (e_5:exp) (x5:var) (e__6:exp) {struct e__6} : exp :=
  match e__6 with
  | (e_var_b nat) => e_var_b nat
  | (e_var_f x) => (if x == x5 then e_5 else (e_var_f x))
  | (e_lit i5) => e_lit i5
  | (e_ann e A) => e_ann (subst_exp e_5 x5 e) A
  | (e_abs e A B) => e_abs (subst_exp e_5 x5 e) A B
  | (e_app e1 e2) => e_app (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_merg e1 e2) => e_merg (subst_exp e_5 x5 e1) (subst_exp e_5 x5 e2)
  | (e_top)    => e_top
  | (e_typeof e A e1 B e2) => e_typeof (subst_exp e_5 x5 e) A (subst_exp e_5 x5 e1) B (subst_exp e_5 x5 e2)
  | (e_fix e A) => e_fix (subst_exp e_5 x5 e) A
  end.

(** definitions *)

(* defns PreValue *)
Inductive pexpr : exp -> Prop :=    (* defn pexpr *)
 | pexpr_int : forall i5,
     pexpr (e_lit i5)
 | pexpr_abs : forall (e:exp) (A B:typ),
     lc_exp (e_abs e A B) ->
     pexpr (e_abs e A B)
 | pexpr_top :
     pexpr e_top
 | pexpr_merg : forall p1 p2,
    pexpr p1 ->
    pexpr p2 ->
    pexpr (e_merg p1 p2).


(* defns value *)
Inductive value : exp -> Prop :=    (* defn value *)
 | val_pexpr : forall p,
    pexpr p ->
    value p.

#[export]
Hint Constructors pexpr value : core.


Inductive ptyp : exp -> typ -> Prop :=    (* defn pexpr *)
 | ptyp_int : forall i5,
     ptyp (e_lit i5) t_int
 | ptyp_abs : forall (e:exp) (A B:typ),
     lc_exp (e_abs e A B) ->
     ptyp (e_abs e A B) (t_arrow A B)
 | ptyp_top :
     ptyp e_top t_top
 | ptyp_merg : forall p1 p2 A B,
    ptyp p1 A ->
    ptyp p2 B ->
    ptyp (e_merg p1 p2) (t_and A B).

Lemma eq_dec_nat : forall n1 n2:nat, {n1 = n2} + {n1 <> n2}.
Proof.
  decide equality.
Defined.

(* #[export]
Hint Constructors unambigous ordu : core. *)

Reserved Notation "e ~~> A --> e'" (at level 80).

Inductive tred : exp -> typ -> exp -> Prop := (*typed red*)
 | tred_lit : forall i5,
    tred (e_lit i5) t_int (e_lit i5)
 | tred_arrow : forall e A1 B1 A2 B2,
    lc_exp (e_abs e A1 B1) ->
    (t_arrow A1 B1) <: (t_arrow A2 B2) ->
    tred (e_abs e A1 B1) (t_arrow A2 B2) (e_abs e A1 B1)
 | tred_mergev1 : forall p1 p2 p1' A,
    lc_exp p2 ->
    Ord A ->
    tred p1 A p1' ->
    tred (e_merg p1 p2) A p1'
 | tred_mergev2 : forall p1 p2 p2' A,
    lc_exp p1 ->
    Ord A ->
    tred p2 A p2' ->
    tred (e_merg p1 p2) A p2'
 | tred_and : forall p p1 p2 A B,
    tred p A p1 ->
    tred p B p2 ->
    tred p (t_and A B) (e_merg p1 p2)
 | tred_top : forall p,
    lc_exp p ->
    tred p t_top e_top
 | tred_or1 : forall p p' A B,
    tred p A p' ->
    (* ptyp p T ->
    T <: (t_union A B) -> *)
    tred p (t_union A B) p'
 | tred_or2 : forall p p' A B,
    tred p B p' ->
    tred p (t_union A B) p'
where "e ~~> A --> e'" := (tred e A e') : env_scope.

(*
getInType returns the input type of a
given functional value
*)

Inductive getInType : exp -> typ -> Prop :=
  | intyp_abs : forall e A B,
      getInType (e_abs e A B) A
  | intyp_merg : forall e1 e2 A B,
      getInType e1 A ->
      getInType e2 B ->
      getInType (e_merg e1 e2) (t_union A B)
  | intyp_int : forall i,
      getInType (e_lit i) t_bot
  | intyp_top :
      getInType e_top t_bot.
  

Inductive dynSemantics : exp -> exp -> Prop :=
    | dyn_merge1 : forall v1 v2 v A B C,
        ptyp v A ->
        getInType v1 B ->
        getInType v2 C ->
        A <: B ->
        not (A <: C) ->
        dynSemantics (e_app (e_merg v1 v2) v) (e_app v1 v)
   | dyn_merge2 : forall v1 v2 v A B C,
        ptyp v A ->
        getInType v1 B ->
        getInType v2 C ->
        not (A <: B) ->
        A <: C ->
        dynSemantics (e_app (e_merg v1 v2) v) (e_app v2 v)
   | dyn_merge3 : forall v1 v2 v A B C,
        ptyp v A ->
        getInType v1 B ->
        getInType v2 C ->
        A <: B ->
        A <: C ->
        dynSemantics (e_app (e_merg v1 v2) v) (e_merg (e_app v1 v) (e_app v2 v)).

(* defns Reduction *)
Reserved Notation "e ~~> e'" (at level 80).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     step e e' ->
     step (e_app v e) (e_app v e')
 | step_beta : forall (e:exp) (A1 B1:typ) (p p':exp) (C:typ),
     lc_exp (e_abs e A1 B1) ->
     pexpr p ->
     tred p A1 p' ->
     e_app (e_abs e A1 B1) p ~~> e_ann (open_exp_wrt_exp e p') B1
 | step_betam : forall (v p1 p2 e':exp),
     value v ->
     value (e_merg p1 p2) ->
     dynSemantics (e_app (e_merg p1 p2) v) e' ->
     e_app (e_merg p1 p2) v ~~> e'
 | step_ann : forall (e:exp) (A:typ) (e':exp),
     (* not (value (e_ann e A)) -> *)
     step e e' ->
     step (e_ann e A) (e_ann e' A)
 | step_annov : forall p p' A,
     pexpr p ->
     (* tred p A p1 -> *)
     tred p A p' ->
     step (e_ann p A) p'
 | step_mergl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_merg e1 e2) (e_merg e1' e2)
 | step_mergr : forall (v e e':exp),
     value v ->
     step e e' ->
     step (e_merg v e)  (e_merg v e')
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     step e e' ->
     step (e_typeof e A e1 B e2) (e_typeof e' A e1 B e2)
 | step_typeofl : forall (p p' :exp) (A B:typ) (e1 e2:exp),
     lc_exp (e_typeof p A e1 B e2) ->
     pexpr p ->
     tred p A p' ->
     step (e_typeof p A e1 B e2)  (open_exp_wrt_exp e1 p')
 | step_typeofr : forall (p p':exp) (A B:typ) (e1 e2:exp),
    lc_exp (e_typeof p A e1 B e2) ->
     pexpr p ->
     tred p B p' ->
     step (e_typeof p A e1 B e2)  (open_exp_wrt_exp e2 p')
 | step_fix : forall (e:exp) (A:typ),
     lc_exp (e_fix e A) ->
     step (e_fix e A) (open_exp_wrt_exp e (e_fix e A))
where "e ~~> e'" := (step e e') : env_scope.



(* defns Typing *)
Inductive typing : ctx -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:ctx) i5,
      uniq  G  ->
     typing G (e_lit i5) t_int
 | typ_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
     typing G (e_var_f x) A
 | typ_ann : forall (G:ctx) (e:exp) (A:typ),
     typing G e A ->
     typing G (e_ann e A) A
 | typ_app : forall (G:ctx) (e1 e2:exp) (B A:typ),
     typing G e1 (t_arrow A B) ->
     typing G e2 A ->
     typing G (e_app e1 e2) B
 | typ_sub : forall (G:ctx) (e:exp) (A B:typ),
     typing G e B ->
     B <: A ->
     typing G e A
 | typ_abs : forall (L:vars) (G:ctx) (e:exp) (A B:typ),
     (forall x , x \notin L -> typing ([(x, A)] ++ G) (open_exp_wrt_exp e (e_var_f x)) B)  ->
     typing G (e_abs e A B) (t_arrow A B)
 | typ_merg : forall (G:ctx) (e1 e2:exp) (A B:typ),
     typing G e1 A ->
     typing G e2 B ->
     typing G (e_merg e1 e2) (t_and A B)
 | typ_top: forall (G:ctx),
     uniq G ->
     typing G e_top t_top
 | typ_typeof : forall (L:vars) (G:ctx) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e (t_union A B) ->
     ( forall x , x \notin  L  -> typing ([(x, A)] ++ G) (open_exp_wrt_exp e1 (e_var_f x))  C) ->
     ( forall x , x \notin  L  -> typing ([(x, B)] ++ G) (open_exp_wrt_exp e2 (e_var_f x))  C) ->
     typing G (e_typeof e A e1 B e2) C
 | typ_fix : forall L e G A,    
     (forall x, x \notin L -> typing ([(x, A)] ++ G) ( open_exp_wrt_exp e (e_var_f x)) A) ->
     typing G (e_fix e A) A.

#[export]
Hint Constructors tred typing step : core.

(** Gathering free names already used in the proofs *)

Ltac gather_atoms ::=
  let A := gather_atoms_with (fun x : atoms => x) in
  let B := gather_atoms_with (fun x : atom => singleton x) in
  (* let C := gather_atoms_with (fun x : list (var * typ) => dom x) in *)
  let D := gather_atoms_with (fun x : exp => fv_exp x) in
  let E := gather_atoms_with (fun x : ctx => dom x) in
  constr:(A `union` B `union` D `union` E).


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_exp_wrt_exp_rec j v e = open_exp_wrt_exp_rec i u (open_exp_wrt_exp_rec j v e) ->
  e = open_exp_wrt_exp_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  destruct (j == n); auto.
  destruct (i == n);auto.
  rewrite <- e in e0. contradiction.
Qed.

Lemma open_ee_rec_term : forall u e,
  lc_exp e -> forall k, e = open_exp_wrt_exp_rec k u e.
Proof.
  induction 1; intros; simpl; f_equal*.
  unfolds open_exp_wrt_exp. pick fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_var_f x)).
   auto.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e1 0 (e_var_f x)).
   auto.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e2 0 (e_var_f x)).
   auto.
  unfolds open_exp_wrt_exp. pick_fresh x.
   apply* (@open_ee_rec_term_core e 0 (e_var_f x)).
   auto.
Qed.

(** Substitution for a fresh name is identity. *)

Lemma subst_ee_fresh : forall x u e,
  x \notin fv_exp e -> subst_exp u x e = e.
Proof with auto.
  induction e; simpl; intros; f_equal*.
  destruct (a==x)...
  absurd_hyp H; fsetdec.
Qed.

(** Substitution distributes on the open operation. *)

Lemma subst_ee_open_ee : forall t1 t2 u x, lc_exp u ->
subst_exp u x (open_exp_wrt_exp t1 t2) =
open_exp_wrt_exp (subst_exp u x t1) (subst_exp u x t2).
Proof with auto.
  intros. unfold open_exp_wrt_exp. generalize 0.
  induction t1; intros; simpls; f_equal*.
  destruct (n0==n)...
  destruct (a==x)...
  rewrite* <- open_ee_rec_term.
Qed.

(** Substitution and open_var for distinct names commute. *)

Lemma subst_ee_open_ee_var : forall x y u e, y <> x -> lc_exp u ->
  (subst_exp u x e) open_ee_var y = subst_exp u x (e open_ee_var y).
Proof with auto.
  introv Neq Wu. rewrite* subst_ee_open_ee.
  simpl.
  destruct (y==x)...
  contradiction.
Qed.

(** Opening up a body t with a type u is the same as opening
  up the abstraction with a fresh name x and then substituting u for x. *)

Lemma subst_ee_intro : forall x u e,
  x \notin fv_exp e -> lc_exp u ->
  open_exp_wrt_exp e u = subst_exp u x (e open_ee_var x).
Proof with auto.
  introv Fr Wu. rewrite* subst_ee_open_ee.
  rewrite* subst_ee_fresh. simpl.
  destruct (x==x)...
  contradiction.
Qed.

(** Substitutions preserve local closure. *)

Lemma subst_ee_term : forall e1 Z e2,
lc_exp e1 -> lc_exp e2 -> lc_exp (subst_exp e2 Z e1).
Proof.
  induction 1; intros; simpl; auto.
  destruct (x==Z); auto.
  - pick fresh y and apply lc_e_abs.
    rewrite* subst_ee_open_ee_var.
  - pick fresh y and apply lc_e_typeof; auto.
    rewrite* subst_ee_open_ee_var.
    rewrite* subst_ee_open_ee_var.
  - pick fresh y and apply lc_fix.
    rewrite* subst_ee_open_ee_var.
Qed.

#[export]
Hint Resolve subst_ee_term : core.


(* ********************************************************************** *)
(** ** Regularity of relations *)

(** The value relation is restricted to well-formed objects. *)

Lemma prevalue_regular : forall t,
  pexpr t -> lc_exp t.
Proof.
  induction 1; autos*.
Qed.

Lemma value_regular : forall t,
  value t -> lc_exp t.
Proof.
  intros. induction H; eauto.
  induction H; eauto. 
  (* apply prevalue_regular in H; auto. *)
Qed.


#[export]
Hint Immediate value_regular prevalue_regular : core.

(** The subtyping relation is restricted to well-formed objects. *)

(** The typing relation is restricted to well-formed objects. *)

Lemma typing_regular : forall E e T,
  typing E e T -> uniq E /\ lc_exp e.
Proof.
  induction 1; try splits*.
  - pick fresh y. specializes H0 y. destructs~ H0.
    apply uniq_cons_iff in H0. destruct~ H0.
  - apply lc_e_abs with (L:=L). intros.
    specialize (H0 x). destruct~ H0.
  - apply lc_e_typeof with (L:=L); intros. 
    destruct~ IHtyping.
    specialize (H1 x H4). destruct~ H1.
    specialize (H3 x H4). destruct~ H3.
  - pick fresh y. specializes H0 y. destructs~ H0.
    apply uniq_cons_iff in H0. destruct~ H0.
  - apply lc_fix with (L:=L). intros.
    specialize (H0 x). destruct~ H0.
Qed.

(* ********************************************************************** *)
(** Weakening (5) *)


Lemma typing_weakening : forall E F G e T,
   typing (E ++ G) e T ->
   uniq (E ++ F ++ G) ->
   typing (E ++ F ++ G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_var.
  - apply* typ_ann.
  - apply* typ_app.
  - apply* typ_sub.
  - pick fresh x and apply typ_abs.
    forwards*: H0 x ([(x, A)] ++ E) G F.
    simpl_env; auto.
  - apply* typ_merg.
  - apply* typ_top.
  - pick fresh x and apply typ_typeof; auto.
    forwards*: H0 x ([(x, A)] ++ E) G F.
    simpl_env; auto.
    forwards*: H2 x ([(x, B)] ++ E) G F.
    simpl_env; auto.
  - pick fresh x and apply typ_fix.
    forwards*: H0 x ([(x, A)] ++ E) G F.
    simpl_env; auto.
Qed.

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

 Lemma typing_through_subst_ee : forall E F x T e u U,
   typing (E ++ [(x, U)] ++ F) e T ->
   typing E u U ->
   typing (E ++ F) (subst_exp u x e) T.
Proof.
introv TypT TypU.
lets TypT': TypT.
inductions TypT; introv; simpl.
 - (*case int*) 
  apply* typ_lit.
 - (*case var*) 
  destruct (x0==x). 
  + subst.
    apply binds_mid_eq in H0; auto. subst.
    lets M: (typing_weakening E F nil u U).
    simpl_env in M.
    apply M; auto.
    apply uniq_remove_mid in H; auto.
  + apply* typ_var.
 - (*case anno*)
  forwards* : IHTypT.
 - (*case app*)
  eapply typ_app; eauto.
 - (*case sub*)
  eapply typ_sub; eauto.
 - (*case abs*)
   pick fresh y and apply typ_abs.
   assert (y \notin L) by auto.
   specialize (H y H1).
   rewrite* subst_ee_open_ee_var.
   lets : H0 y H1 ((y, A) :: E) F x.
   lets : H2 U.
   simpl_env in H3.
   forwards* : H3.
   simpl_env.
   forwards*: typing_regular TypU.
   apply typing_weakening with (E:=nil) (F:=(y~A)) (G:=E); eauto.
   rewrite_env (y ~ A ++ E).
   destruct H4. auto.
   apply typing_regular in TypU. destruct~ TypU.
 - (*case merge*)
   apply typ_merg; eauto.
 - apply* typ_top.
 - pick fresh y.
   apply typ_typeof with (L:=union L
   (union (singleton x)
      (union (fv_exp u)
         (union (fv_exp e)
            (union (fv_exp e1)
               (union (fv_exp e2) (union (dom E) (dom F)))))))); eauto; intros.
   +  assert (NOTIN: x0 `notin` L) by auto.
      specialize (H x0 NOTIN).
      rewrite* subst_ee_open_ee_var.
      lets TEMP1: H0 x0 NOTIN ((x0, A) :: E) F x.
      lets TEMP2: TEMP1 U.
      simpl_env in TEMP2.
      apply TEMP2; auto.
      simpl_env.
      forwards* (UNIQ&LC): typing_regular TypU.
      apply typing_weakening with (E:=nil) (F:=(x0~A)) (G:=E); eauto.
      apply typing_regular in TypU. destruct~ TypU.
   +  assert (NOTIN: x0 `notin` L) by auto.
      specialize (H1 x0 NOTIN).
      rewrite* subst_ee_open_ee_var.
      lets TEMP1: H2 x0 NOTIN ((x0, B) :: E) F x.
      lets TEMP2: TEMP1 U.
      simpl_env in TEMP2.
      apply TEMP2; auto.
      forwards* (UNIQ&LC): typing_regular TypU.
      apply typing_weakening with (E:=nil) (F:=(x0~B)) (G:=E); eauto.
      apply typing_regular in TypU. destruct~ TypU.
 - (*case fix*)
   pick fresh y and apply typ_fix.
   assert (y \notin L) by auto.
   specialize (H y H1).
   rewrite* subst_ee_open_ee_var.
   lets : H0 y H1 ((y, A) :: E) F x.
   lets : H2 U.
   simpl_env in H3.
   forwards* : H3.
   simpl_env.
   forwards*: typing_regular TypU.
   apply typing_weakening with (E:=nil) (F:=(y~A)) (G:=E); eauto.
   rewrite_env (y ~ A ++ E).
   destruct H4. auto.
   apply typing_regular in TypU. destruct~ TypU.
Qed.


Lemma not_value_ann : forall e A,
  not (value (e_ann e A)) ->
  not (value (e_ann (e_ann e A) A)).
Proof.
  introv NVal.
  unfold not in *; intros.
  inverts H. inverts H0.
Qed.


Lemma ord_sub_either : forall A B C,
Ord A -> A <: t_union B C -> A <: B \/ A <: C.
Proof.
  intros.
  inverts H.
  inverts* H0.
  inverts* H0.
Qed.


Lemma tred_pexpr : forall v A w,
pexpr v -> tred v A w -> pexpr w.
Proof.
  intros.
  induction H0; eauto.
  - inverts* H.
  - inverts* H.
Qed.

Lemma tred_trans :
  forall w, pexpr w ->
  forall A w1, tred w A w1 ->
  forall B, Ord B -> 
  forall w2, tred w1 B w2 ->
  tred w B w2.
Proof.
  introv Val Red1.
  forwards* LC: prevalue_regular Val.
  inductions Red1; introv Ord Red2; eauto.
  - (*case merg1*)
    inverts Val. inverts LC.
    inductions Red2; eauto.
  - (*case merg2*)
    inverts Val. inverts LC.
    inductions Red2; eauto.
  - (*case and*)
    inverts Red2; eauto. inverts Ord. inverts Ord.
    inverts Ord.
  - (*case top*)
    inverts Red2; auto. 
    inverts Ord. inverts Ord. inverts Ord.
Qed.

Lemma pexpr_inf_btm_false : forall p A,
pexpr p -> typing nil p A -> A <: t_bot -> False.
Proof.
  introv Val Typ Sub.
  inductions Typ; try solve [inverts Val];
  try solve [inverts Sub].
  forwards*: IHTyp.
  eapply sub_transitivity; eauto.
  inverts Val. inverts* Sub.
  (* inverts Val. inverts* Sub. *)
Qed.

Lemma sub_and_ord : forall A B C,
Ord C -> t_and A B <: C -> A <: C \/ B <: C.
Proof.
  intros.
  induction H; intros.
  inverts* H0.
  inverts* H0.
Qed.

Lemma ptyp_unique : forall w A B, 
  ptyp w A -> ptyp w B -> A = B.
Proof.
  introv Typ1 Typ2. gen B.
  induction Typ1; intros.
  inverts Typ2; auto.
  inverts Typ2. auto.
  inverts Typ2. auto.
  inverts Typ2.
  forwards*: IHTyp1_1 H1.
  forwards*: IHTyp1_2 H3.
  subst~.
Qed.

(*********************************)

Lemma inv_int : forall E A i5,
typing E (e_lit i5) A -> typing E (e_lit i5) t_int /\ subtyping t_int A.
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
Qed.

Lemma abs_typ_arrow_sub : forall G e D1 D2 A,
typing G (e_abs e D1 D2) A ->
exists A1 B1, subtyping (t_arrow A1 B1) A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards* : IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply sub_transitivity; eauto.
    - exists* D1 D2.
Qed.

Lemma inv_and_arrow : forall G e D1 D2 A1 A2 B1 B2,
  typing G (e_abs e D1 D2) (t_and A1 A2) ->
  subtyping (t_and A1 A2) (t_arrow B1 B2) ->
  subtyping A1 (t_arrow B1 B2) \/ subtyping A2 (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
Qed.

Lemma inv_abs_sub : forall G e D1 D2 A B1 B2,
    typing G (e_abs e D1 D2) A ->
    subtyping A (t_arrow B1 B2) ->
           (exists L, forall x , x \notin  L -> typing ((x, D1) :: G) (e open_ee_var x) D2)
           /\ subtyping (t_arrow D1 D2) (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: subtyping B (t_arrow B1 B2)) by applys sub_transitivity H Sub.
    forwards* (?&?): IHTyp HS.
Qed.

Lemma inv_abs_sub' : forall G e D1 D2 A,
    typing G (e_abs e D1 D2) A ->
        (exists L, forall x , x \notin  L -> typing ((x, D1) :: G) (e open_ee_var x) D2)
           /\ subtyping (t_arrow D1 D2) A.
Proof.
  introv Typ.
  inductions Typ; eauto.
  - forwards* [temp Sub]: IHTyp e D1 D2.
    destruct temp as [L temp].
    split*.
    eapply sub_transitivity; eauto.
Qed.

Lemma inv_abs_sub'' : forall G e D1 D2 A,
    typing G (e_abs e D1 D2) A ->
    typing G (e_abs e D1 D2) (t_arrow D1 D2)
           /\ subtyping (t_arrow D1 D2) A.
Proof.
  introv Typ.
  inductions Typ; eauto.
  - forwards* [temp Sub]: IHTyp e D1 D2.
    split*.
    eapply sub_transitivity; eauto.
Qed.

Lemma inv_arrow : forall G e D1 D2 A1 A2,
    typing G (e_abs e D1 D2) (t_arrow A1 A2) ->
    (exists L, forall x , x \notin  L -> typing ((x, D1)::G) (e open_ee_var x) D2)
                  /\ subtyping (t_arrow D1 D2) (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards* : inv_abs_sub H.
  - split*.
Qed.

Lemma inv_abs_union : forall G e D1 D2 A A1 A2,
    typing G (e_abs e D1 D2) A ->
    subtyping A (t_union A1 A2) ->
    typing G (e_abs e D1 D2) A1 \/ typing G (e_abs e D1 D2) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts* Sub.
Qed.

Lemma inv_top : forall E A,
typing E e_top A -> typing E e_top t_top /\ subtyping t_top A.
Proof.
  introv Typ.
  inductions Typ.
  (*case typ_sub*)
 - forwards* : IHTyp. destruct H0.
    split*.
    eapply sub_transitivity; eauto.
  (*case typ_int*)
 - split*.
Qed.


Lemma inv_anno : forall G e A B,
  typing G (e_ann e A) B ->
  typing G e A /\ A <: B.
Proof.
  introv Typ.
  inductions Typ; eauto.
  forwards*: IHTyp.
  destruct H0.
  split*.
  eapply sub_transitivity; eauto.
Qed.


Lemma inv_merge : forall G e1 e2 A,
  typing G (e_merg e1 e2) A ->
  exists B1 B2, typing G e1 B1 /\ typing G e2 B2 /\ (t_and B1 B2) <: A.
Proof.
  introv Typ.
  inductions Typ; auto.
  - forwards*: IHTyp.
    destruct H0 as [C1 [C2 [Typ1 [Sub Sub2]]]].
    exists* C1 C2.
    splits; eauto.
    eapply sub_transitivity; eauto.
  - exists* A B.
Qed.

Lemma check_or_typ : forall E e A B,
   pexpr e ->
   typing E e (t_union A B) ->
   typing E e A \/ typing E e B.
Proof.
  introv Val Typ.
  induction Val.
  (*subsumption again*)
 - apply inv_int in Typ. destruct Typ.
   inverts* H0.
 - inverts Typ.
   eapply inv_abs_union in H0; eauto.
 - apply inv_top in Typ. destruct Typ.
   inverts* H0.
 - (*Case merge*)
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1 [Typ2 Sub]]]].
    inductions Sub; eauto.
    forwards* [Typ3 | Typ4]: IHVal1.
    forwards* [Typ3 | Typ4]: IHVal2.
Qed.

(*********************************)

Lemma pexpr_ptype_sub_dir_type : forall w A,
  pexpr w ->
  typing nil w A ->
  forall B, ptyp w B ->
  B <: A.
Proof.
  introv Val Typ. gen A.
  dependent induction Val; intros; try solve [inverts Val]; intros.
  - inverts H.
    apply inv_int in Typ.
    destruct Typ; auto.
  - inverts H0.
    apply inv_abs_sub'' in Typ.
    destruct Typ; auto.
  - inverts H.
    apply inv_top in Typ.
    destruct Typ; auto.
  - inverts H.
    apply inv_merge in Typ.
    destruct Typ as [A1 [B1 [Typ1 [Typ2 Sub]]]].
    forwards*: IHVal1.
    forwards*: IHVal2.
    assert (t_and A0 B0 <: t_and A1 B1); auto.
    eapply sub_transitivity; eauto.
Qed.

#[export]
Hint Constructors ptyp : core.

Lemma exists_ptype_pexpr : forall p,
  pexpr p -> exists A, ptyp p A.
Proof.
  induction 1; eauto.
  destruct IHpexpr1 as [A1 H1].
  destruct IHpexpr2 as [A2 H2].
  exists*.
Qed.


Lemma tred_preservation_infer : forall w A w', 
pexpr w -> tred w A w' -> 
forall B, typing nil w B -> typing nil w' A.
Proof.
  introv Val Red.
  induction Red; introv Typ; eauto.
  (* - case int
    assert (typing nil (e_lit i5) infer t_int); auto.
    admit. *)
  - (*case arrow*)
    forwards*: typing_regular Typ. destruct H1.
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ Sub].
    assert (typing nil (e_abs e A1 B1) (t_arrow A1 B1)); eauto.
  - (*mergl*)
    inverts Val.
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1 [Typ2 Sub]]]].
    forwards*: IHRed H3.
  - (*mergr*)
    inverts Val.
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1 [Typ2 Sub]]]].
    forwards*: IHRed H4.
Qed.

Lemma pexpr_infer_ptyp : forall w A,
  pexpr w ->
  ptyp w A ->
  forall B, typing nil w B ->
  typing nil w A.
Proof.
  introv Val Typ Typ1. gen A B.
  dependent induction Val; try solve [inverts Val]; intros;
  try solve [inverts* Typ].
  inverts Typ.
  apply inv_abs_sub'' in Typ1.
  destruct Typ1; auto.
  inverts Typ.
  apply inv_merge in Typ1.
  destruct Typ1 as [B1 [B2 [Typ2 [Typ3 Sub]]]].
  forwards*: IHVal1 H1.
Qed.


Lemma pexper_dir_bot_false : forall p E,
  pexpr p ->
  forall A, typing E p A ->
  A <: t_bot -> False.
Proof.
  introv Val Typ Sub.
  induction Typ; intros; eauto;
  try solve [inverts Sub];
  try solve [inverts Val].
  eapply sub_transitivity in Sub; eauto.
  inverts Val. inverts* Sub.
  (* inverts Val. inverts* Sub. *)
Qed.

Lemma tred_progress_dir : forall v,
pexpr v -> forall A, typing nil v A -> exists v', tred v A v'.
Proof.
  introv Val Typ. gen A.
  induction Val; intros.
  - (* case int *)
    gen i5. induction A; intros; eauto.
    inverts Typ.
    forwards*: pexper_dir_bot_false H H0. inverts H1.
    apply inv_int in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    apply inv_int in Typ.
    destruct Typ as [Typ Sub]. inverts* Sub.
    eapply typ_sub in H1; eauto.
    forwards*: IHA1 H1.
    eapply typ_sub in H1; eauto.
    forwards*: IHA2 H1.
    apply inv_int in Typ.
    destruct Typ as [Typ Sub].
    inverts* Sub.
    assert (typing [] (e_lit i5) A1); eauto.
    forwards*: IHA1 H.
    assert (typing [] (e_lit i5) A2); eauto.
    forwards*: IHA2 H1.
  - (* case arrow *)
    gen A B.
    inductions A0; eauto; intros.
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    inverts Typ.
    forwards*: pexper_dir_bot_false H0. inverts H2.
    clear IHA0_1 IHA0_2.
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ Sub].
    eauto.
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ Sub].
    inverts* Sub.
    eapply typ_sub in Typ; eauto.
    forwards*: IHA0_1 Typ.
    eapply typ_sub in Typ; eauto.
    forwards*: IHA0_2 Typ.
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ  Sub].
    inverts* Sub.
    forwards* (p1'&TEMP1): IHA0_1.
    forwards* (p2'&TEMP2): IHA0_2.
  - (* case top *)
    inductions A; eauto; intros.
    apply inv_top in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    inverts Typ.
    forwards*: pexper_dir_bot_false H. inverts H1.
    apply inv_top in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    apply inv_top in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    forwards* (p1'&TEMP1): IHA1.
    forwards* (p2'&TEMP2): IHA2.
    apply inv_top in Typ.
    destruct Typ as [Typ Sub]. inverts Sub.
    forwards* (p1'&TEMP1): IHA1.
    forwards* (p2'&TEMP2): IHA2.
  - (* case intersection *)
    induction A; intros; eauto.
    (* ordinary int type *)
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1[Typ2 Sub]]]]. 
    inverts* Sub.
    forwards* : IHVal1 t_int.
    forwards* : IHVal2 t_int.
    (* bot type *)
    inverts Typ.
    forwards*: pexper_dir_bot_false H H0. inverts H1.
    (* ordinary arrow type *)
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1[Typ2 Sub]]]]. 
    inverts* Sub.
    forwards* : IHVal1 (t_arrow A1 A2).
    forwards* : IHVal2 (t_arrow A1 A2).
    (*union type*)
    assert (Val: pexpr (e_merg p1 p2)); auto.
    forwards* TEMP4: check_or_typ Typ.
    destruct TEMP4 as [TEMP4 | TEMP4].
    forwards*: IHA1 TEMP4.
    forwards*: IHA2 TEMP4.
    (* intersection type *)
    assert (Sub1: subtyping (t_and A1 A2) A1); auto.
    assert (Sub2: subtyping (t_and A1 A2) A2); auto.
    forwards*: IHA1.
    forwards*: IHA2.
Qed.


Lemma step_not_value: forall (v:exp),
    value v -> forall v', not (step v v').
Proof.
  intros v.
  induction v; introv H; try solve [inverts H; inverts H0];
  unfold not; introv STEP; try solve [inverts STEP].
  - inverts* STEP. inverts* H. inverts* H0. inverts H.
    inverts* H0.
Qed.

Lemma getInTypeSup : forall v,
  value v ->
  forall N1, getInType v N1 ->
  forall A B, typing [] v (t_arrow A B) ->
  A <: N1.
Proof.
  introv VAL. induction 1; introv Typ.
  apply inv_abs_sub'' in Typ.
  destruct Typ. inverts* H0.
  inverts VAL. inverts H1.
  apply inv_merge in Typ.
  destruct Typ as [B1 [B2 [Typ2 [Typ3 Sub]]]].
  inverts* Sub.
  apply inv_int in Typ.
  destruct Typ as [Typ Sub].
  inverts Sub.
  apply inv_top in Typ.
  destruct Typ as [Typ Sub].
  inverts Sub.
Qed.


(*************************)
(***** Ordinary2 Types ****)
(*************************)

Inductive Ord2 : typ -> Prop :=
  | o_int2   : Ord2 t_int
  | o_arrow2 : forall t1 t2, 
                Ord2 (t_arrow t1 t2)
  | o_top2   : Ord2 t_top
  | o_and    : forall A B,
                Ord2 A ->
                Ord2 B ->
                Ord2 (t_and A B).

#[export]
Hint Constructors Ord2 : core.

Lemma ord2_sub_either : forall A B C,
Ord2 A -> A <: t_union B C -> A <: B \/ A <: C.
Proof.
  intros.
  inductions H0; eauto.
  inverts H.
  inverts H. forwards*: IHsubtyping B C.
  destruct H as [Sub | Sub]; eauto.
  inverts H. forwards*: IHsubtyping B C.
  destruct H as [Sub | Sub]; eauto.
Qed.

Lemma ord2_sub_bot_false : forall A,
    Ord2 A -> A <: t_bot -> False.
Proof.
  induction 1; intros Sub; try solve [inverts* Sub].
Qed.

Lemma getInTypeInv' : forall v,
  value v ->
  forall A, getInType v A ->
  forall C, typing [] v C ->
  forall B, Ord2 B ->
  B <: A ->
  typing [] v (t_arrow B t_top).
Proof.
  introv VAL IN. induction IN; introv Typ Ord Sub.
  - (*case abs*)
    apply inv_abs_sub'' in Typ.
    destruct Typ as [Typ Sub1]. eauto.
  - (*case merge*)
    inverts VAL. inverts H.
    apply inv_merge in Typ.
    destruct Typ as [B1 [B2 [Typ1 [Typ2 Sub1]]]].
    forwards* [Sub2 | Sub3]: ord2_sub_either Sub.
    forwards*: IHIN1 B1 Sub2.
    forwards*: IHIN2 B2 Sub3.
  - (*case int*)
    forwards* TEMP1: ord2_sub_bot_false B. inverts TEMP1.
  - (*case top*)
    forwards* TEMP1: ord2_sub_bot_false B. inverts TEMP1.
Qed.

Lemma pty_ord : forall v A,
    ptyp v A -> Ord2 A.
Proof.
    induction 1; eauto.
Qed.


(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma pexpr_reduce_under_arrow_abs : 
  forall p A B p',
  pexpr p ->
  tred p (t_arrow A B) p' ->
  exists e A1 B1, p' = e_abs e A1 B1.
Proof.
  intros.
  inductions H0; eauto.
  forwards*: IHtred. inverts* H.
  forwards*: IHtred. inverts* H.
Qed.

Lemma pexpr_ptyp_infer : forall v A,
    ptyp v A ->
    forall B, typing [] v B ->
    typing [] v A.
Proof.
  induction 1; introv Typ; eauto.
  apply inv_abs_sub'' in Typ.
  destruct Typ; eauto.
  apply inv_merge in Typ.
  destruct Typ as [B1 [B2 [Typ1 [Typ2 Sub]]]]; eauto.
Qed.

Lemma preservation : forall e e' T,
  typing nil e T ->
  e ~~> e' ->
  typing nil e' T.
Proof.
  introv Typ. gen e'.
  inductions Typ; introv Red; try solve [ inverts* Red ].
  - (* anno *)
    inverts* Red.
    forwards*: tred_preservation_infer H3.
  - (* app *)
     inverts* Red.
     (* beta *)
   +  apply inv_abs_sub'' in Typ1.
      destruct Typ1 as [Typ1 Sub2].
      (*for subst lemma*)
      lets TEMP: typing_through_subst_ee.
      eapply inv_abs_sub in Typ1; eauto.
      destruct Typ1 as [Typ1 Sub3].
      destruct Typ1 as [L Typ1].
      inverts Sub2.
      eapply typ_sub; eauto.
      forwards* : tred_preservation_infer H4.
      pick fresh x.
      assert (x \notin L) by auto.
      lets: Typ1 x H0.
      specialize (TEMP nil nil x B1).
      specialize (TEMP (e open_ee_var x) p' A1).
      rewrite_env ([(x,A1)]) in TEMP.
      apply TEMP in H3; eauto.
      simpl_env in H3.
      rewrite* (@subst_ee_intro x).
      forwards*: typing_regular H.
   + (*case dynsemantics*)
      inductions H4.
      (*case 1*)
      apply inv_merge in Typ1.
      destruct Typ1 as [T1 [T2 [Typ3 [Typ4 Sub]]]].
      inverts* Sub.
      eapply typ_sub in Typ4; eauto.
      inverts H2. inverts H6.
      forwards*: getInTypeSup H5 Typ4.
      inverts H1.
      forwards*: pexpr_ptype_sub_dir_type H6.
      clear H4.
      eapply sub_transitivity in H2; eauto.
      contradiction.
      (*case 2*)
      apply inv_merge in Typ1.
      destruct Typ1 as [T1 [T2 [Typ3 [Typ4 Sub]]]].
      inverts* Sub.
      eapply typ_sub in Typ3; eauto.
      inverts H2. inverts H6.
      forwards*: getInTypeSup H0 Typ3.
      inverts H1.
      forwards*: pexpr_ptype_sub_dir_type H6.
      clear H3.
      eapply sub_transitivity in H2; eauto.
      contradiction.
      (*case 3*)
      apply inv_merge in Typ1.
      destruct Typ1 as [T1 [T2 [Typ3 [Typ4 Sub]]]].
      inverts* Sub.
        {
          inverts H2. inverts H6.
          assert (typing [] (e_app p1 e2) B). eauto.
          forwards* ORD2: pty_ord H.
          forwards*: getInTypeInv' H5.
          forwards*: pexpr_ptyp_infer H.
        }
        {
          inverts H2. inverts H6.
          assert (typing [] (e_app p2 e2) B). eauto.
          forwards* ORD2: pty_ord H.
          forwards*: getInTypeInv' H0.
          forwards*: pexpr_ptyp_infer H.
        }
  - (*switch*)
    inverts* Red.
    (* when lies in first branch *)
    pick_fresh y.
    forwards* TEMP1: H y.
    lets TEMP2: tred_preservation_infer H10 H11.
    forwards TEMP21: TEMP2 Typ.
    rewrite* (@subst_ee_intro y); eauto.
    lets TEMP3: typing_through_subst_ee.
    specialize (TEMP3 nil nil y C (e1 open_ee_var y) p').
    specialize (TEMP3 A).
    simpl_env in *.
    forwards*: TEMP3.
    forwards*: typing_regular TEMP21.
    (* when lies in second branch *)
    pick_fresh y.
    forwards* TEMP1: H1 y.
    lets TEMP2: tred_preservation_infer H10 H11.
    forwards TEMP21: TEMP2 Typ.
    rewrite* (@subst_ee_intro y); eauto.
    lets TEMP3: typing_through_subst_ee.
    specialize (TEMP3 nil nil y C (e2 open_ee_var y) p').
    specialize (TEMP3 B).
    simpl_env in *.
    forwards*: TEMP3.
    forwards*: typing_regular TEMP21.
  - (* fix *)
    inverts* Red.
    pick_fresh y.
    rewrite* (@subst_ee_intro y). 
    lets TEMP1: typing_through_subst_ee.
    specialize (TEMP1 nil nil y A (e open_ee_var y) (e_fix e A)).
    specialize (TEMP1 A).
    simpl_env in *.
    forwards*: TEMP1.
Qed.

Lemma pexpr_dec : forall e, lc_exp e -> pexpr e \/ ~ pexpr e.
Proof.
introv lc. intros.
inductions e; try solve [right; unfold not; introv TEMP; inversion TEMP].
  - left*.
  - left*.
  - inverts lc.
    destruct~ IHe1; destruct~ IHe2.
    all: try solve [right; unfold not; introv TEMP; inverts TEMP; eauto].
  - left*.
Qed.

Lemma value_dec : forall e, lc_exp e -> (value e) \/ (~ (value e)).
Proof.
introv lc.
inductions e; eauto;
try solve [right; unfold not; introv TEMP; inverts TEMP; inverts H].
destruct~ IHe1; destruct~ IHe2; inverts* lc;
try solve [inverts* H; inverts* H0].
  - right. unfold not. intros.
    inverts H1. inverts H2.
    assert (value e2); auto.
  - right. unfold not. intros.
    inverts H1. inverts H2.
    assert (value e1); auto.
  - right. unfold not. intros.
    inverts H1. inverts H2.
    assert (value e2); auto.
Qed.


#[export]
Hint Constructors getInType dynSemantics : core.

Lemma exists_intype_pexpr : forall p,
  pexpr p -> exists A, getInType p A.
Proof.
  induction 1; try solve [exists*].
  destruct IHpexpr1 as [A1 H1].
  destruct IHpexpr2 as [A2 H2].
  exists*.
Qed.

Fixpoint t_size (A:typ) : nat :=
  match A with
  | t_top => 1
  | t_int => 1
  | t_bot => 1
  | t_arrow A B => 1 + t_size A + t_size B
  | t_union A B => 1 + t_size A + t_size B
  | t_and A B => 1 + t_size A + t_size B
  end.

Lemma sub_dec_size : forall n A B, ((t_size A + t_size B) < n) ->
  A <: B \/ not (A <: B).
Proof.
  intro n.
  induction n.
  - intros. lia.
  -
  intros A. induction A; eauto; intros.
  1: { induction B; eauto; unfold not in *.
    right; introv Sub. inverts Sub.
    right; introv Sub. inverts Sub.
    right; introv Sub. inverts Sub.
    simpl in *.
    destruct IHB1; destruct IHB2; auto; simpl in *.
    lia. lia. lia. lia. lia.
    right. introv Sub. inverts* Sub.
    simpl in *.
    destruct IHB1; destruct IHB2; auto; simpl.
    lia. lia. lia. lia.
    right; introv Sub. inverts* Sub. lia.
    right; introv Sub. inverts* Sub.
    right; introv Sub. inverts* Sub.
  }
  3: { (*union case*)
    specialize (IHA1 B). specialize (IHA2 B).
    simpl in *.
    destruct IHA1; destruct IHA2; unfold not in *; eauto;
    try solve [lia].
    right. introv Sub.
    apply sub_or in Sub. destruct Sub. contradiction.
    right. introv Sub.
    apply sub_or in Sub. destruct Sub. contradiction.
    right. introv Sub.
    apply sub_or in Sub. destruct Sub. contradiction.
  }
  3: { (*and case*)
    simpl in *.
    induction B; auto; unfold not in *.
    specialize (IHA1 t_int).
    specialize (IHA2 t_int).
    destruct IHA1; destruct IHA2; auto;
    try solve [lia].
    right; introv Sub. inverts* Sub.
    specialize (IHA1 t_bot).
    specialize (IHA2 t_bot).
    destruct IHA1; destruct IHA2; auto;
    try solve [lia].
    right; introv Sub. inverts* Sub.
    specialize (IHA1 (t_arrow B1 B2)).
    specialize (IHA2 (t_arrow B1 B2)).
    destruct IHA1; destruct IHA2; auto;
    try solve [lia].
    right; introv Sub. inverts* Sub.
    simpl in *.
    specialize (IHA1 (t_union B1 B2)).
    specialize (IHA2 (t_union B1 B2)).
    destruct IHA1; destruct IHA2; auto; simpl;
    try solve [lia].
    destruct IHB1; destruct IHB2; auto; simpl;
    try solve [lia].
    right. introv Sub.
    dependent induction Sub; eauto.
    simpl in *.
    destruct IHB1; destruct IHB2; auto; simpl;
    try solve [lia].
    right. introv Sub.
    apply sub_and in Sub. destruct~ Sub.
    right. introv Sub.
    apply sub_and in Sub. destruct~ Sub.
    right. introv Sub.
    apply sub_and in Sub. destruct~ Sub.
  }
  2: { (*arrow case*)
    induction B; eauto.
    right. intros Sub. inverts* Sub.
    right. intros Sub. inverts* Sub.
    clear IHB1 IHB2.
    simpl in *.
    specialize (IHn B1 A1).
    specialize (IHA2 B2).
    destruct IHn; destruct IHA2; auto; simpl in *;
    try solve [lia].
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
    clear IHA1 IHA2.
    destruct IHB1; destruct IHB2; simpl in *; auto;
    try solve [lia].
    right. introv Sub. inverts* Sub.
    clear IHA1 IHA2.
    destruct IHB1; destruct IHB2; simpl in *; auto;
    try solve [lia].
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
  }
  1: { (*case int*)
    induction B; eauto.
    right. intros Sub. inverts* Sub.
    right. intros Sub. inverts* Sub.
    destruct IHB1; destruct IHB2; simpl in *; auto;
    try solve [lia].
    right. introv Sub. inverts* Sub.
    destruct IHB1; destruct IHB2; simpl in *; auto;
    try solve [lia].
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
    right. introv Sub. inverts* Sub.
  }
Qed.


Lemma dynSemanticsProgress : forall v1 v2 A B,
  pexpr v1 -> pexpr v2 ->
  typing [] (e_merg v1 v2) (t_arrow A B) ->
  forall v, pexpr v ->
  typing [] v A->
  exists e', dynSemantics (e_app (e_merg v1 v2) v) e'.
Proof.
  introv PVAL1 PVAL2 Typ1 PVAL Typ2.
  apply inv_merge in Typ1.
  destruct Typ1 as [B1 [B2 [Typ3 [Typ4 Sub]]]].
  forwards* TEMP1: exists_ptype_pexpr PVAL.
  destruct TEMP1 as [A1 PTYP1].
  forwards* TEMP2: exists_intype_pexpr PVAL1.
  forwards* TEMP3: exists_intype_pexpr PVAL2.
  destruct TEMP2 as [N1 INTYP1].
  destruct TEMP3 as [N2 INTYP2].
  forwards* DEC1: sub_dec_size A1 N1.
  forwards* DEC2: sub_dec_size A1 N2.
  destruct DEC1 as [Sub21 | Sub22].
  destruct DEC2 as [Sub31 | Sub32].
  exists*. exists*.
  destruct DEC2 as [Sub31 | Sub32].
  exists*.
  (*this is contradiction*)
  (*this cannot happen*)
  (*A1 should be a subtype of either of N1 or N2*)
  inverts Sub.
  (*Case 1*)
  eapply typ_sub in Typ3; eauto.
  forwards*: getInTypeSup Typ3.
  forwards*: pexpr_ptype_sub_dir_type PTYP1.
  eapply sub_transitivity in H; eauto.
  (*Case 2*)
  eapply typ_sub in Typ4; eauto.
  forwards*: getInTypeSup Typ4.
  forwards*: pexpr_ptype_sub_dir_type PTYP1.
  eapply sub_transitivity in H; eauto.
Qed.


Lemma progress : forall e T,
typing nil e T -> (value e) \/ (exists e', e ~~> e').
Proof.
introv Typ. (*gen_eq E: (@nil typ).*) lets Typ': Typ.
inductions Typ; (*intros EQ; subst;*) eauto.

(*
inductions does the book keeping for us.
So we don't need to keep the manual book keeping by:

gen_eq E: (@nil typ).

And so:

intros EQ; subst
*)

(*case int*)
 (* - right*. *)
 (*case var*)
 - inverts H0.
 (*case anno*)
 - forwards*: IHTyp. destruct~ H.
  + inverts H.
    (*case step-annv*)
    apply tred_progress_dir in Typ; eauto.
    destruct Typ as [v' Typ]. 
    right. exists* v'.
  + (*case step-ann*)
    destruct H as [v' H].
    forwards*: typing_regular Typ'.
(*case typ-app*)
 - right. forwards* TEMP1: IHTyp1.
   destruct TEMP1.
   + forwards* TEMP2: IHTyp2.
     destruct TEMP2.
     *  inverts* H.
        inverts* H1.
        apply inv_int in Typ1.
        destruct Typ1. inverts H1.
        (*need new rule*)
        apply inv_abs_sub'' in Typ1.
        destruct Typ1 as [Typ1 Sub2].
        inverts Sub2.
        forwards* Typ3: typ_sub Typ2 H4.
        inverts H0.
        apply tred_progress_dir in Typ3; auto.
        destruct Typ3 as [v' Tred]. eauto.
        (*top infers arrow*)
        apply inv_top in Typ1.
        destruct Typ1. inverts H1.
        (*merge infers arrow*)
        inverts H0.
        forwards* : dynSemanticsProgress H H2 Typ1 Typ2.
     * destruct H0 as [e'].
       eauto.
  + destruct H.
    exists (e_app x e2). apply* step_appl.
    forwards*: typing_regular Typ2.
(*case typ-abs*)
 - left. forwards*: typing_regular Typ'.
(*case typ-merge*)
 - 
   forwards* TEMP1: IHTyp1.
   destruct~ TEMP1.
   forwards* TEMP2: IHTyp2.
   destruct~ TEMP2.
   destruct H.
   destruct H0.
   eauto.
   right*.
   destruct H as [e'].
   right.
   exists (e_merg e' e2).
   apply step_mergl; auto.
   forwards*: typing_regular Typ2.
 - (*switch*)
   right.
   destruct IHTyp; auto.
   (*value e*)
   inverts H3.
   (*pexpr e*)
   forwards*: check_or_typ H4.
   destruct H3.
   forwards*: tred_progress_dir H3.
   destruct H5 as [p' H5].
   exists* (open_exp_wrt_exp e1 p').
   apply* step_typeofl.
   forwards*: typing_regular Typ'.
   forwards*: tred_progress_dir H3.
   destruct H5 as [p' H5].
   exists* (open_exp_wrt_exp e2 p').
   apply* step_typeofr.
   forwards*: typing_regular Typ'.
   (*e --> e'*)
   destruct H3 as [e'].
   exists* (e_typeof e' A e1 B e2).
   apply* step_typeof.
   forwards*: typing_regular Typ'.
 - (* fix *)
   right. 
   exists (open_exp_wrt_exp e (e_fix e A)).
   apply step_fix.
   apply typing_regular in Typ'.
   destruct~ Typ'.
Qed.