
(*

This file contains the coq formalization
of section Appendix A of thesis.

-> Contains properties of preservation,
   progress, and determinism.

-> Revised Dsijointness Algorithm with COST

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
     value e_null.

(* defns FindType *)
Inductive findtype : exp -> typ -> Prop :=    (* defn findtype *)
 | findtype_int : forall i5,
     findtype (e_lit i5) t_int
 | findtype_arrow : forall (e:exp),
     lc_exp (e_abs e) ->
     findtype  (e_abs e) (t_arrow t_top t_bot)
 | findtype_null :
     findtype e_null t_unit.

#[export]
Hint Constructors value findtype : core.

(****** Counting Free Variables ******)

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
  end.

(***** Substitution Functions ******)

(** Substitution for free type variables in types. *)


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
  end.


(* defns Typing *)
Reserved Notation "G |= e : A" (at level 80, e at next level, A at next level).
Inductive typing : env -> exp -> typ -> Prop :=    (* defn typing *)
 | typ_lit : forall (G:env) i5,
      okt G  ->
     typing G (e_lit i5) t_int
 | typ_null : forall G,
      okt G ->
      typing G e_null t_unit
 | typ_var : forall (G:env) (x:var) (A:typ),
      okt G ->
      binds x (bind_typ A) G  ->
      typing G (e_fvar x) A
 | typ_app : forall (G:env) (e1 e2:exp) (B A:typ),
     typing G e1 (t_arrow A B) ->
     typing G e2 A ->
     typing G (e_app e1 e2) B
 | typ_sub : forall (G:env) (e:exp) (A B:typ),
     typing G e B ->
     sub B A ->
     typing G e A
 | typ_abs : forall (L:vars) (G:env) (e:exp) (A B:typ),
      okt G ->
      ( forall x , x \notin  L  -> typing (G & x ~: A) (open_ee e (e_fvar x)) B)  ->
     typing G (e_abs e) (t_arrow A B)
 | typ_typeof : forall (L:vars) (G:env) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     typing G e (t_union A B) ->
     ( forall x ,x \notin  L -> typing (G & x ~: A ) (open_ee e1 (e_fvar x) ) C) ->
     ( forall x ,x \notin  L -> typing (G & x ~: B ) (open_ee e2 (e_fvar x) ) C) ->
     A *s B ->
     typing G (e_typeof e A e1 B e2) C
 | typ_inter : forall G e A B,
     typing G e A ->
     typing G e B ->
     typing G e (t_and A B)
where "G |= e : A" := (typing G e A).


(* defns Reduction *)
Reserved Notation "e --> e'" (at level 80, e' at next level).
Inductive step : exp -> exp -> Prop :=    (* defn step *)
 | step_appl : forall (e1 e2 e1':exp),
     lc_exp e2 ->
     step e1 e1' ->
     step (e_app e1 e2) (e_app e1' e2)
 | step_appr : forall (v e e':exp),
     value v ->
     step e e' ->
     step (e_app v e) (e_app v e')
 | step_beta : forall (e:exp) (v:exp),
     lc_exp (e_abs e) ->
     value v ->
     step (e_app (e_abs e) v) (open_ee e v)
 | step_typeof : forall (e:exp) (A:typ) (e1:exp) (B:typ) (e2 e':exp),
     lc_exp (e_typeof e A e1 B e2) ->
     step e e' ->
     step (e_typeof e A e1 B e2) (e_typeof e' A e1 B e2)
 | step_typeofl : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
     lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub C A ->
     step (e_typeof v A e1 B e2) (open_ee e1 v)
 | step_typeofr : forall (v:exp) (A:typ) (e1:exp) (B:typ) (e2:exp) (C:typ),
    lc_exp (e_typeof v A e1 B e2) ->
     value v ->
     findtype v C ->
     sub C B ->
     step (e_typeof v A e1 B e2) (open_ee  e2 v )
where "e --> e'" := (step e e') : env_scope.

#[export]
Hint Constructors typing step : core.

(** Gathering free names already used in the proofs **)

Ltac gather_vars :=
  let A := gather_vars_with (fun x : vars => x) in
  let B := gather_vars_with (fun x : var => \{x}) in
  let C := gather_vars_with (fun x : exp => fv_ee x) in
  let D := gather_vars_with (fun x : env => dom x) in
  constr:(A \u B \u C \u D).

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

(* ********************************************************************** *)
(** * Properties of Substitutions *)


(** Substitution for a fresh name is identity. *)

(** Substitution and open_var for distinct names commute. *)


(* ********************************************************************** *)
(** ** Properties of term substitution in terms *)

Lemma open_ee_rec_term_core : forall e j v u i, i <> j ->
open_ee_rec j v e = open_ee_rec i u (open_ee_rec j v e) ->
  e = open_ee_rec i u e.
Proof.
  induction e; introv Neq H; simpl in *; inversion H; f_equal*.
  case_nat*. case_nat*.
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
Qed.

#[export]
Hint Resolve subst_ee_term : core.

(* ********************************************************************** *)
(** * Relations between well-formed environment and types well-formed
  in environments *)

(** If an environment is well-formed, then it does not contain duplicated keys. *)

Lemma ok_from_okt : forall E,
  okt E -> ok E.
Proof.
  induction 1. auto. auto.
Qed.

#[export]
Hint Extern 1 (ok _) => apply (ok_from_okt _) : core.


Lemma append_empty_right : forall (E : env),
  E = E & empty.
Proof.
  intros.
  rewrite~ concat_empty_r.
Qed.

(** Automation *)

(* ********************************************************************** *)
(** ** Properties of well-formedness of an environment *)

(** Through type substitution *)

(** Inversion lemma *)

Lemma okt_push_inv : forall E x T,
  okt (E & x ~: T) -> okt E /\ x # E.
Proof.
  introv O. inverts O.
    false* empty_push_inv.
    lets (?&M&?): (eq_push_inv H). inverts M. subst. autos.
Qed.

#[export]
Hint Resolve okt_push_inv : core.

(** Through strengthening *)

Lemma okt_strengthen : forall x T (E F : env),
  okt (E & x ~: T & F) ->
  okt (E & F).
Proof.
  introv O. induction F using env_ind.
  rewrite concat_empty_r in *. apply okt_push_inv in O. destruct~ O.
  rewrite concat_assoc in *.
  destruct v.
  apply okt_push_inv in O. destructs O.
  apply okt_typ; auto.
Qed.

Lemma okt_concat_inv : forall E F x V,
  okt (E & (x ~: V) & F) -> okt E /\ x # E.
Proof.
  intros E F. gen E.
  induction F using env_ind; introv; rew_env_concat; auto; introv ok.
  apply okt_push_inv in ok.
  destruct ok; auto.
  destruct v.
  apply okt_push_inv in ok.
  destruct ok.
  forwards*: IHF.
Qed.


(** Automation *)

#[export]
Hint Immediate okt_strengthen : core.

(* ********************************************************************** *)
(** ** Regularity of relations *)

Lemma typing_regular : forall E e T,
  typing E e T -> okt E /\ lc_exp e.
Proof.
  induction 1; try splits*.
 - (*case abs*)
   apply lc_e_abs with (L:=L). intros.
   specializes H1 x. destructs~ H1.
 - (*case typeof*)
   apply lc_e_typeof with (L:=L); intros. destructs~ IHtyping.
   destructs~ IHtyping.
   forwards*: H1 x.
   destructs~ IHtyping.
   forwards*: H3 x.
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

Lemma step_regular : forall t t',
  step t t' -> lc_exp t /\ lc_exp t'.
Proof.
  induction 1; split*.
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
  - inverts H. destructs IHstep.
    apply_fresh* lc_e_typeof as y.
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
  - inverts H. pick_fresh y. rewrite* (@subst_ee_intro y).
Qed.

(** Automation *)

#[export]
Hint Extern 1 (okt ?E) =>
  match goal with
  | H: typing _ _ _ |- _ => apply (proj31 (typing_regular H))
  end : core.

#[export]
Hint Extern 1 (lc_exp ?e) =>
  match goal with
  | H: typing _ ?e _ |- _ => apply (proj32 (typing_regular H))
  | H: step ?e _ |- _ => apply (proj1 (step_regular H))
  | H: step _ ?e |- _ => apply (proj2 (step_regular H))
  end : core.

Lemma demorgan2 : forall P Q, ~ (P \/ Q) -> ~P /\ ~Q.
Proof.
  unfold not in *; intros.
  splits; intros.
  apply H; auto.
  apply H; auto.
Qed.


(* ********************************************************************** *)
(** Typing Weakening *)

Lemma typing_weakening : forall E F G e T,
   typing (E & G) e T ->
   okt (E & F & G) ->
   typing (E & F & G) e T.
Proof.
  introv Typ. gen F. inductions Typ; introv Ok.
  - apply* typ_lit.
  - apply* typ_null.
  - apply* typ_var. 
    apply* binds_weaken.
  - apply* typ_app.
  - apply* typ_sub.
  - pick_fresh y.
    apply typ_abs with (L:=L \u fv_ee e
       \u dom E \u dom G \u dom F); auto.
    intros.
    forwards~: (H0 x).
    apply_ih_bind (H1 x); eauto.
  - pick_fresh y.
    apply typ_typeof with (L:=L \u fv_ee e 
       \u dom E \u dom G \u dom F); intros; autos*.
    + forwards* : H x. apply_ih_bind (H0 x); eauto.
    + forwards* : H1 x. apply_ih_bind (H2 x); eauto.
  - apply* typ_inter.
Qed.


(************************************************************************ *)
(** Preservation by Type Narrowing *)

(************************************************************************ *)
(** Preservation by Term Substitution (8) *)

Lemma typing_through_subst_ee : forall E F x T e u U,
   typing (E & x ~: U & F) e T ->
   typing E u U ->
   typing (E & F) (subst_ee x u e) T.
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
  + binds_get H0.
    (* apply ok_from_okt in H; auto. *)
    lets M: (typing_weakening E F empty u U).
    do 2 rewrite concat_empty_r in M.
    apply* M.
  + binds_cases H0; apply* typ_var.
(*case app*)
 - eapply typ_app; eauto.
(*case sub*)
 - forwards* : IHTypT E F TypU TypT.
(*case abs*)
 - pick_fresh y.
   apply typ_abs with (L:=L \u \{ x} \u fv_ee u 
     \u fv_ee e \u dom E \u dom F); intros; autos*.
   assert (x0 \notin L) by auto.
   specialize (H1 x0 H3 E (F & x0 ~: A)).
   rewrite* subst_ee_open_ee_var.
   lets : H1 x U.
   forwards* : H4.
   rewrite~ concat_assoc.
   rewrite~ concat_assoc.
   rewrite~ <- concat_assoc.
   apply typing_regular in TypU. destructs~ TypU.
(*case typeof*)
 - pick_fresh y.
   apply typ_typeof with (L:=L \u \{ x} \u fv_ee u 
     \u fv_ee e \u fv_ee e1 \u fv_ee e2 \u
      dom E \u dom F); intros; eauto.
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
- apply* typ_inter.
Qed.


Lemma UO_sub_union : forall B B1 B2,
  US B B1 B2 ->
  forall A, UO A ->
  sub A B ->
  sub A B1 \/ sub A B2.
Proof.
  induction 1;
  introv Ord Sub.
  induction Ord; inverts* Sub.
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

(* ********************************************************************** *)
(** Preservation Result (20) *)

Lemma inv_int : forall E A i5,
typing E (e_lit i5) A -> typing E (e_lit i5) t_int /\ sub t_int A.
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

Lemma abs_typ_arrow_sub : forall G e A,
typing G (e_abs e) A ->
exists A1 B1, sub (t_arrow A1 B1) A.
Proof.
    introv Typ.
    inductions Typ.
    - forwards* : IHTyp. destruct H0 as [x1[x2 H3]].
      exists x1 x2. eapply sub_transitivity; eauto.
    - exists* A B.
    - forwards* : IHTyp1.
      forwards* : IHTyp2.
      destruct H as [x1 [x2 H3]].
      destruct H0 as [x3 [x4 H4]].
      exists t_top t_bot.
      apply s_anda.
      assert (sub (t_arrow t_top t_bot) (t_arrow x1 x2)); eauto.
      eapply sub_transitivity; eauto.
      assert (sub (t_arrow t_top t_bot) (t_arrow x3 x4)); eauto.
      eapply sub_transitivity; eauto.
Qed.

Lemma inv_and_arrow : forall G e A1 A2 B1 B2,
  typing G (e_abs e) (t_and A1 A2) ->
  sub (t_and A1 A2) (t_arrow B1 B2) ->
  sub A1 (t_arrow B1 B2) \/ sub A2 (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inverts Sub; eauto.
Qed.

Lemma inv_abs_sub : forall G e A B1 B2,
    typing G (e_abs e) A ->
    sub A (t_arrow B1 B2) ->
         exists C1 C2,
           (exists L, forall x , x \notin  L -> typing (G & x ~: C1) (e open_ee_var x) C2)
           /\ sub (t_arrow C1 C2) (t_arrow B1 B2).
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - assert (HS: sub B (t_arrow B1 B2)) by applys sub_transitivity H Sub.
    forwards* (?&?&?&?): IHTyp HS.
  - forwards* [HS|HS]: inv_and_arrow Sub.
Qed.


Lemma inv_arrow : forall G e A1 A2,
    typing G (e_abs e) (t_arrow A1 A2) ->
    exists B1 B2, (exists L, forall x , x \notin  L -> typing (G & x ~: B1) (e open_ee_var x) B2)
                  /\ sub (t_arrow B1 B2) (t_arrow A1 A2).
Proof.
  introv Typ.
  inverts Typ.
  - forwards* : inv_abs_sub H.
  - exists A1 A2. split*.
Qed.


Lemma inv_abs_union : forall G e A A1 A2,
    typing G (e_abs e) A ->
    sub A (t_union A1 A2) ->
    typing G (e_abs e) A1 \/ typing G (e_abs e) A2.
Proof.
  introv Typ Sub.
  inductions Typ; eauto.
  - eapply sub_transitivity in Sub; eauto.
  - inverts* Sub.
  - inverts* Sub.
Qed.

Lemma inv_null : forall E A,
typing E e_null A -> typing E e_null t_unit /\ sub t_unit A.
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

Lemma check_or_typ : forall E e A B,
   value e ->
   typing E e (t_union A B) ->
   typing E e A \/ typing E e B.
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
Qed.

Lemma uord_sub_union : forall B B1 B2,
  US B B1 B2 ->
  forall A, Ord A ->
  sub A B ->
  sub A B1 \/ sub A B2.
Proof.
  induction 1;
  introv Ord Sub.
  inverts Ord; inverts* Sub.
  1,2: apply sub_and in Sub;
       forwards*: IHUS Ord.
Qed.

Lemma sub_ord_disjoint_types : forall A B,
  A *s B ->
  forall C, Ord C ->
  sub C A ->
  sub C B -> False.
Proof.
  introv Disj Ord SubA SubB.
  unfold DisjSpec in Disj.
  unfold not in Disj.
  forwards*: Disj C.
Qed.


(********************************************************)
(** A value cannot check against disjoint types **)

Lemma val_check_disjoint_types : forall E v A B,
  A *s B ->
  value v ->
  typing E v A ->
  typing E v B -> False.
Proof.
  introv Disj Val Typ1 Typ2.
  inverts Val.
  - apply inv_int in Typ1. destruct Typ1.
    apply inv_int in Typ2. destruct Typ2.
    forwards*: sub_ord_disjoint_types Disj H0 H2.
  - apply abs_typ_arrow_sub in Typ1.
    destruct Typ1 as [A1 [B1]].
    assert (sub (t_arrow t_top t_bot) (t_arrow A1 B1)); auto.
    apply abs_typ_arrow_sub in Typ2.
    destruct Typ2 as [A2 [B2]].
    assert (sub (t_arrow t_top t_bot) (t_arrow A2 B2)); auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A1 B1)) (C:=A) in H1; auto.
    eapply sub_transitivity with (A:=(t_arrow t_top t_bot)) (B:=(t_arrow A2 B2)) (C:=B) in H3; auto.
    forwards*: sub_ord_disjoint_types Disj H1 H3.
  - apply inv_null in Typ1. destruct Typ1.
    apply inv_null in Typ2. destruct Typ2.
    forwards*: sub_ord_disjoint_types Disj H0 H2.
Qed.

(*******************************************************)
(** findtype gives least type of an expressions **)

Lemma check_find_type : forall E e A B,
typing E e A ->
findtype e B ->
sub B A.
Proof.
  introv Typ Find.
  inductions Find.
  - apply inv_int in Typ.
    destruct~ Typ.
  - apply abs_typ_arrow_sub in Typ.
    destruct Typ as [A1 [B1]].
    assert (sub (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
    eapply sub_transitivity; eauto.
  - apply inv_null in Typ. destruct~ Typ.
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

Lemma preservation : forall E e e' T,
  typing E e T ->
  step e e' ->
  typing E e' T.
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
Qed.


(*******************************)
(******  Progress Lemma  *******)
(*******************************)

Lemma progress : forall e T,
typing empty e T -> (value e) \/ (exists e', step e e').
Proof.
introv Typ. gen_eq E: (@empty typ). lets Typ': Typ.
inductions Typ; intros EQ; subst.
(*case int*)
 - left*.
 (*case null*)
 - left*.
 (*case var*)
 - apply binds_empty_inv in H0. inversion H0.
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
      assert (sub (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
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
      assert (sub (t_arrow t_top t_bot) (t_arrow A1 B1)) by auto.
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
  + (*case typeof*)
    destruct H4.
    exists (e_typeof x A e1 B e2).
    apply step_typeof; auto.
    forwards* : typing_regular Typ'.
  - forwards* : IHTyp1.
Qed.

(*******************************)
(*****  Determinism Lemma  *****)
(*******************************)

Lemma inv_app : forall E e1 e2 A,
typing E (e_app e1 e2) A ->
exists A1 B1, typing E e1 (t_arrow A1 B1) /\ typing E e2 A1.
Proof.
  introv Typ.
  inductions Typ.
 - exists* A B.
 - specialize (IHTyp e1 e2).
  forwards* : IHTyp.
 - forwards* : IHTyp1.
Qed.

Lemma inv_typeof : forall E e e1 e2 A B C,
typing E (e_typeof e A e1 B e2) C ->
exists D, typing E e D /\ A *s B.
Proof.
  introv Typ.
  inductions Typ.
  - specialize (IHTyp e e1 e2 A B).
    forwards* : IHTyp.
  - exists* (t_union A B).
  - forwards* : IHTyp1.
Qed.

(********************************************)
(** Value is normal form **)

Lemma value_not_step : forall v e',
  value v ->
  step v e' -> False.
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

Lemma determinism : forall E e e1 e2 A, 
  typing E e A ->
  step e e1 -> step e e2 -> e1 = e2.
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
Qed.