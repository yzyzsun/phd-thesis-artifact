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

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.
(* Require Import Program.Equality. *)
(* Require Import Coq.Lists.ListSet. *)
(* From Coq Require Export Lists.List. *)
(* Export ListNotations. *)
(* Require Import Coq.Strings.String. *)
(* Require Import Lia. *)

(** syntax *)

Inductive typ : Set :=  (* types *)
 | t_top   : typ
 | t_null  : typ
 | t_int   : typ
 | t_bot   : typ
 | t_arrow : typ -> typ -> typ
 | t_rcd   : nat -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and   : typ -> typ -> typ.

Lemma eq_dec : forall x y:typ, {x = y} + {x <> y}.
Proof.
 decide equality.
 apply eq_nat_dec.
Defined.

(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80).
Inductive subtyping : typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall A, A <: t_top
 | s_null :
     t_null <: t_null
 | s_int :
     t_int <: t_int
 | s_arrow : forall (A1 A2 B1 B2:typ),
     B1 <: A1 ->
     A2 <: B2 ->
     (t_arrow A1 A2) <: (t_arrow B1 B2)
 | s_rcd : forall (l:nat) (A B:typ),
     A <: B ->
     (t_rcd l A) <: (t_rcd l B)
 | s_ora : forall (A1 A2 A:typ),
     A1 <: A ->
     A2 <: A ->
     (t_union A1 A2) <: A
 | s_orb : forall (A A1 A2:typ),
     A <: A1 ->
     A <: (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     A <: A2 ->
     A <: (t_union A1 A2)
 | s_anda : forall A A1 A2,
     A <: A1 ->
     A <: A2 ->
     A <: (t_and A1 A2)
 | s_andb : forall A1 A2 A,
     A1 <: A ->
     (t_and A1 A2) <: A
 | s_andc : forall A1 A2 A,
     A2 <: A ->
     (t_and A1 A2) <: A
 | s_bot : forall A,
     t_bot <: A
(* | s_disj : forall A B,
     FindSuptypes A = [] ->
     B <: A *)
where "A <: B" := (subtyping A B) : env_scope.

#[export]
Hint Constructors subtyping : core.

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
| o_int   : Ord t_int
| o_null  : Ord t_null
| o_rcd   : forall l t, Ord (t_rcd l t)
| o_arrow : forall t1 t2, Ord (t_arrow t1 t2).

#[export]
Hint Constructors Ord : core.


Lemma sub_or : forall A B C, (t_union A B) <: C -> A <: C /\ B <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
specialize (IHsubtyping A B).
forwards* : IHsubtyping.
specialize (IHsubtyping1 A B).
specialize (IHsubtyping2 A B).
forwards*: IHsubtyping1.
forwards*: IHsubtyping2.
Defined.


Lemma sub_and : forall A B C, A <: (t_and B C) -> A <: B /\ A <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsubtyping1 B C).
specialize (IHsubtyping2 B C).
forwards*: IHsubtyping1.
forwards*: IHsubtyping2.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
specialize (IHsubtyping B C).
forwards*: IHsubtyping.
Defined.

(**********************************)
(*****  Subtyping Properties  *****)
(**********************************)

Lemma sub_refl : forall A, A <: A.
  induction A; eauto.
Defined.

#[export]
Hint Resolve sub_refl : core.

Lemma sub_transitivity : forall B A C, A <: B -> B <: C -> A <: C.
Proof.
induction B; intros;
generalize H0 H; clear H0; clear H; generalize A; clear A.
- intros; inductions H0; eauto. 
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- intros; inductions H; eauto.
- induction C; intros; try solve [inverts* H0].
  induction A; try solve[inverts* H].
  inverts H0; inverts* H. 
- induction C; intros; try solve [inverts* H0].
  induction A; try solve[inverts* H].
  inverts H0; inverts* H. 
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros. apply sub_and in H. destruct H.
  inductions H0; eauto.
Defined.