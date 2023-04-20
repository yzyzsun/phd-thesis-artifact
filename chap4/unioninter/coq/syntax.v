(*

August 1, 2023:
---------------
-> Union + intersection + unit
-> Extended from section 4 of OOPSLA'22 draft
-> No nominal types
-> Sound and complete disjointness

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
Require Import Coq.Lists.ListSet.
From Coq Require Export Lists.List.
Export ListNotations.

Require Import Lia.

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ.

Inductive exp : Set :=  (*r expression *)
 | e_bvar  : nat -> exp
 | e_fvar  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp.

(** Opening up a term binder occuring in a term *)

Fixpoint open_ee_rec (k:nat) (e_5:exp) (e__6:exp) {struct e__6}: exp :=
  match e__6 with
  | (e_bvar nat) => If (k = nat) then e_5 else (e_bvar nat)
  | (e_fvar x) => e_fvar x
  | (e_lit i5) => e_lit i5
  | (e_abs e) => e_abs (open_ee_rec (S k) e_5 e)
  | (e_app e1 e2) => e_app (open_ee_rec k e_5 e1) (open_ee_rec k e_5 e2)
  | (e_typeof e A e1 B e2) => e_typeof (open_ee_rec k e_5 e) A (open_ee_rec (S k) e_5 e1) B (open_ee_rec (S k) e_5 e2)
  | e_null    => e_null
end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

(** Terms as locally closed pre-terms *)

(* defns LC_exp *)
Inductive lc_exp : exp -> Prop :=    (* defn lc_exp *)
 | lc_e_var_f : forall (x:var),
     lc_exp (e_fvar x)
 | lc_e_lit : forall i5,
     lc_exp (e_lit i5)
 | lc_e_abs : forall (L:vars) (e:exp),
      ( forall x , x \notin L -> lc_exp (open_ee e (e_fvar x)) )  ->
     lc_exp (e_abs e)
 | lc_e_app : forall (e1 e2:exp),
     lc_exp e1 ->
     lc_exp e2 ->
     lc_exp (e_app e1 e2)
 | lc_e_typeof : forall (L:vars) (e:exp) (A:typ) (e1:exp) (B:typ) (e2:exp),
     lc_exp e ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e1 (e_fvar x)) ) ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e2 (e_fvar x)) ) ->
     lc_exp (e_typeof e A e1 B e2)
 | lec_e_null :
     lc_exp e_null.

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_typ  : typ -> bind.

Notation "x ~: T" := (x ~ bind_typ T)
(at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. **)

Definition env := LibEnv.env bind.

  
Inductive okt : env -> Prop :=
  | okt_empty :
      okt empty
  | okt_typ : forall E x T,
      okt E ->
      x # E -> 
      okt (E & x ~: T).

#[export]
Hint Constructors okt : core.


(* defns Subtyping *)
Reserved Notation "A <: B" (at level 80, B at next level).
Inductive sub : typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall A,
     sub A t_top
 | s_int :
     sub t_int t_int
 | s_unit :
    sub t_unit t_unit
 | s_arrow : forall (A1 A2 B1 B2:typ),
     sub B1 A1 ->
     sub A2 B2 ->
     sub (t_arrow A1 A2) (t_arrow B1 B2)
 | s_ora : forall (A1 A2 A:typ),
     sub A1 A ->
     sub A2 A ->
     sub (t_union A1 A2) A
 | s_orb : forall (A A1 A2:typ),
     sub A A1 ->
     sub A (t_union A1 A2)
 | s_orc : forall (A A1 A2:typ),
     sub A A2 ->
     sub A (t_union A1 A2)
 | s_anda : forall A A1 A2,
     sub A A1 ->
     sub A A2 ->
     sub A (t_and A1 A2)
 | s_andb : forall A1 A2 A,
     sub A1 A ->
     sub (t_and A1 A2) A
 | s_andc : forall A1 A2 A,
     sub A2 A ->
     sub (t_and A1 A2) A
 | s_bot : forall A,
      sub t_bot A
where "A <: B" := (sub A B) : env_scope.


#[export]
Hint Constructors sub lc_exp ok okt : core.

Lemma sub_or : forall A B C, (t_union A B) <: C -> 
  A <: C /\ B <: C.
Proof.
  intros; inductions H; try solve [split*].
  specialize (IHsub A B).
  forwards* : IHsub.
  specialize (IHsub A B).
  forwards* : IHsub.
  specialize (IHsub1 A B).
  specialize (IHsub2 A B).
  forwards* : IHsub1.
Defined.

Lemma sub_and : forall A B C, A <: (t_and B C) -> 
  A <: B /\ A <: C.
Proof.
  intros; inductions H; try solve [split*].
  specialize (IHsub1 B C).
  specialize (IHsub2 B C).
  forwards* : IHsub1.
  specialize (IHsub B C).
  forwards* : IHsub.
  specialize (IHsub B C).
  forwards* : IHsub.
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
- induction C; intros; try solve [inverts* H0].
  induction A; try solve[inverts* H].
  inverts H0; inverts* H. 
- intros. apply sub_or in H0. destruct H0.
  inductions H; eauto.
- intros. apply sub_and in H. destruct H.
  inductions H0; eauto.
- intros; inductions H0; eauto.
Defined.

Fixpoint t_size (A:typ) : nat :=
  match A with
  | t_top => 1
  | t_int => 1
  | t_bot => 1
  | t_arrow A B => 1 + t_size A + t_size B
  | t_union A B => 1 + t_size A + t_size B
  | t_and A B => 1 + t_size A + t_size B
  | t_unit => 1
  end.

(* subtyping decideability *)

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
    right; introv Sub. inverts Sub.
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
    specialize (IHA1 t_unit).
    specialize (IHA2 t_unit).
    destruct IHA1; destruct IHA2; auto;
    try solve [lia].
    right; introv Sub. inverts* Sub.
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
    right. intros Sub. inverts* Sub.
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
    right. intros Sub. inverts* Sub.
  }
  1: { (*case unit*)
    induction B; eauto.
    right. intros Sub. inverts* Sub.
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

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
  | o_int   : Ord t_int
  | o_arrow : forall t1 t2, Ord (t_arrow t1 t2)
  | o_unit  : Ord t_unit.

Inductive UO : typ -> Prop :=
  | uo_int   : UO t_int
  | uo_arrow : forall t1 t2, UO (t_arrow t1 t2)
  | uo_unit  : UO t_unit
  | uo_and   : forall t1 t2, UO t1 -> UO t2 -> UO (t_and t1 t2)
  | uo_top   : UO t_top
  | uo_bot   : UO t_bot.


(* splittable types *)

Inductive US : typ -> typ -> typ -> Prop :=
  | us_or : forall A B,
      US (t_union A B) A B
  | us_and1 : forall A A1 A2 B,
      US A A1 A2 ->
      US (t_and A B) (t_and A1 B) (t_and A2 B)
   | us_and2 : forall A B B1 B2,
      UO A ->
      US B B1 B2 ->
      US (t_and A B) (t_and A B1) (t_and A B2).

#[export]
Hint Constructors Ord UO US : core.

(*
  Disjointness Specifications
*)

Definition DisjSpec A B := forall C, Ord C -> 
  not ((sub C A) /\ (sub C B)).
Notation "A *s B" := (DisjSpec A B) (at level 80, B at next level).

Lemma ord_sub_union : forall A B1 B2,
  UO A ->
  sub A (t_union B1 B2) ->
  sub A B1 \/ sub A B2.
Proof.
  introv Ord Sub.
  induction Ord; inverts* Sub.
Qed.

Lemma ord_ordu : forall A,
  Ord A -> UO A.
Proof.
  introv ord. inverts* ord.
Qed.

#[export]
Hint Resolve ord_ordu : core.

Lemma disj_inv_union : forall A B1 B2,
  DisjSpec A (t_union B1 B2) ->
  DisjSpec A B1 /\ DisjSpec A B2.
Proof.
    unfold DisjSpec; unfold not; introv Disj.
    split; introv ord [Sub1 Sub2].
    forwards*: Disj C.
    forwards*: Disj C.
Qed.


Lemma disj_inv_and_top : forall B1 B2,
  DisjSpec t_top (t_and B1 B2) ->
  DisjSpec B1 B2.
Proof.
    unfold DisjSpec; unfold not; introv Disj ord Sub.
    inverts ord.
    forwards*: Disj t_int.
    forwards*: Disj (t_arrow t1 t2).
    forwards*: Disj t_unit.
Qed.

Lemma disj_and_disj : forall A B C,
  DisjSpec A B ->
  DisjSpec (t_and A B) C.
Proof.
  unfold DisjSpec. unfold not.
  introv Disj ord [Sub1 Sub2].
  apply sub_and in Sub1. destruct Sub1.
  forwards*: Disj C0.
Qed.

Lemma disj_spec_sym : forall A B,
    DisjSpec A B -> DisjSpec B A.
Proof.
    unfold DisjSpec; unfold not; introv Disj ord [Sub1 Sub2].
    forwards*: Disj C.
Qed.


(**********************************)
(******* Disjointness Again *******)
(**********************************)

Inductive Disj2 : typ -> typ -> Prop :=
  | disj2_botl : forall A,
      Disj2 t_bot A
  | disj2_botr : forall A,
      Disj2 A t_bot
  | disj2_int_arrl : forall A B,
      Disj2 t_int (t_arrow A B)
  | disj2_int_arrr : forall A B,
      Disj2 (t_arrow A B) t_int
  | disj2_null_arrl : forall A B,
      Disj2 t_unit (t_arrow A B)
  | disj2_null_arrr : forall A B,
      Disj2 (t_arrow A B) t_unit
  | disj2_int_nulll :
      Disj2 t_int t_unit
  | disj2_int_nullr :
      Disj2 t_unit t_int
  | disj2_or1 : forall A B A1 A2,
      US A A1 A2 ->
      Disj2 A1 B ->
      Disj2 A2 B ->
      Disj2 A B
  | disj2_or2 : forall A B B1 B2,
      US B B1 B2 ->
      Disj2 A B1 ->
      Disj2 A B2 ->
      Disj2 A B
  | disj2_and1 : forall B A1 A2,
      UO B ->
      Disj2 A1 B ->
      Disj2 (t_and A1 A2) B
  | disj2_and2 : forall B A1 A2,
      UO B ->
      Disj2 A2 B ->
      Disj2 (t_and A1 A2) B
  | disj2_and3 : forall A B1 B2,
      UO A ->
      Disj2 A B1 ->
      Disj2 A (t_and B1 B2)
  | disj2_and4 : forall A B1 B2,
      UO A ->
      Disj2 A B2 ->
      Disj2 A (t_and B1 B2)
  | disj2_and5 : forall A B C,
      Disj2 A B ->
      Disj2 (t_and A B) C
  | disj2_and6 : forall A B C,
      Disj2 B C ->
      Disj2 A (t_and B C).

Notation "A *2a B" := (Disj2 A B) (at level 80, B at next level).


#[export]
Hint Constructors Disj2 : core.


Lemma ord_sub_union2 :
  forall B B1 B2, US B B1 B2 ->
  forall A, UO A ->
  A <: B ->
  sub A B1 \/ sub A B2.
Proof.
  induction 1; introv UO SUB.
  induction UO; eauto;
  try solve [inverts* SUB].
  apply sub_and in SUB.
  destruct SUB. forwards*: IHUS UO.
  apply sub_and in SUB.
  destruct SUB. forwards*: IHUS UO.
Qed.


Lemma Disj2_sound : forall A B,
  Disj2 A B -> DisjSpec A B.
Proof.
    unfold DisjSpec.
    induction 1; unfold not; introv ord Sub; 
      destruct Sub as [Sub1 Sub2]; unfold not in *.
    (*trivial cases*)
    all: try solve [inverts ord; inverts Sub1; inverts Sub2].
    (*union cases*)
    forwards: ord_sub_union2 H C; auto.
    destruct H2; eauto.
    forwards: ord_sub_union2 H C; auto.
    destruct H2; eauto.
    (*intersection cases*)
    1,2: apply sub_and in Sub1;
      destruct Sub1 as [Sub11 Sub12];
      forwards: IHDisj2 ord; auto.
    1,2: apply sub_and in Sub2;
      destruct Sub2 as [Sub11 Sub12];
      forwards: IHDisj2 ord; auto.
    (*and cases*)
    apply sub_and in Sub1.
    forwards*: IHDisj2 C0.
    apply sub_and in Sub2.
    forwards*: IHDisj2 C0.
Qed.


Lemma UO_or_US : forall A, UO A \/ exists A1 A2, US A A1 A2.
Proof.
  intro A. induction A; eauto.
  destruct IHA1. destruct IHA2; auto.
  destruct H0 as [B1 [B2 SPL1]]; eauto.
  destruct H as [B1 [B2 SPL1]]; eauto.
Qed.


(***************************************
  we need UO restriction on A1&A2 as in
  disj_spec_and_uo_inv1 below.
****************************************)

Lemma all_ord_not_sub : forall A B, DisjSpec A B ->
  not (t_int <: (t_and A B)) /\
  not (t_unit <: (t_and A B)) /\
  not ((t_arrow t_top t_bot) <: (t_and A B)).
Proof.
  introv Disj. unfold DisjSpec in Disj.
  unfold not in *.
  splits; introv Sub;
  apply sub_and in Sub; destruct Sub as [Sub1 Sub2]; eauto.
Qed.


Require Import Coq.Logic.Classical.

Lemma not_sub_and_inv : forall A B1 B2,
  not (A <: t_and B1 B2) -> not (sub A B1 /\ sub A B2).
Proof.
  introv NSUB. unfold not in *.
  introv [Sub1 Sub2]; auto.
Qed.

Lemma not_sub_and_inv2 : forall A B1 B2 C,
  not (A <: t_and B1 B2 /\ A <: C) -> not (sub A B1 /\ sub A B2 /\ A <: C).
Proof.
  introv NSUB. unfold not in *.
  introv [Sub1 [Sub2 Sub3]]; auto.
Qed.

Lemma int_sub_one_ord : forall A, UO A ->
  t_int <: A ->
  (not (t_unit <: A) /\ not (t_arrow t_top t_bot <: A)) \/
  t_top <: A.
Proof.
  introv UOA Sub. unfold not.
  induction UOA; eauto.
  1,2,3,5: left;
  split; introv Sub1;
  try solve [inverts Sub1; inverts Sub].
  apply sub_and in Sub.
  destruct Sub as [Sub11 Sub12].
  (* apply sub_and in Sub1.
  destruct Sub1 as [Sub21 Sub22]. *)
  forwards*: IHUOA1.
  destruct H. destruct H.
  forwards*: IHUOA2.
  destruct H1. destruct H1.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  left. split.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  forwards*: IHUOA2.
  destruct H0. destruct H0.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  right*.
Qed.

Lemma unit_sub_one_ord : forall A, UO A ->
  t_unit <: A ->
  (not (t_int <: A) /\ not (t_arrow t_top t_bot <: A)) \/
  t_top <: A.
Proof.
  introv UOA Sub. unfold not.
  induction UOA; eauto.
  1,2,3,5: left;
  split; introv Sub1;
  try solve [inverts Sub1; inverts Sub].
  apply sub_and in Sub.
  destruct Sub as [Sub11 Sub12].
  (* apply sub_and in Sub1.
  destruct Sub1 as [Sub21 Sub22]. *)
  forwards*: IHUOA1.
  destruct H. destruct H.
  forwards*: IHUOA2.
  destruct H1. destruct H1.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  left. split.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  forwards*: IHUOA2.
  destruct H0. destruct H0.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  right*.
Qed.

Lemma arrow_sub_one_ord : forall A, UO A ->
  (t_arrow t_top t_bot) <: A ->
  (not (t_int <: A) /\ not (t_unit <: A)) \/
  t_top <: A.
Proof.
  introv UOA Sub. unfold not.
  induction UOA; eauto.
  1,2,3,5: left;
  split; introv Sub1;
  try solve [inverts Sub1; inverts Sub].
  apply sub_and in Sub.
  destruct Sub as [Sub11 Sub12].
  (* apply sub_and in Sub1.
  destruct Sub1 as [Sub21 Sub22]. *)
  forwards*: IHUOA1.
  destruct H. destruct H.
  forwards*: IHUOA2.
  destruct H1. destruct H1.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  left. split.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  forwards*: IHUOA2.
  destruct H0. destruct H0.
  left. split*.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  introv Sub. apply sub_and in Sub.
  destruct Sub as [Sub1 Sub2]. contradiction.
  right*.
Qed.

Lemma UO_sub_int_unit_top : forall A, UO A ->
  t_int <: A -> t_unit <: A -> t_top <: A.
Proof.
  introv UOR Sub1 Sub2.
  induction UOR; auto;
  try solve [inverts Sub2];
  try solve [inverts Sub1].
  inverts* Sub1. inverts* Sub2.
Qed.

Lemma UO_sub_int_arrow_top : forall A, UO A ->
  t_int <: A -> (t_arrow t_top t_bot) <: A -> t_top <: A.
Proof.
  introv UOR Sub1 Sub2.
  induction UOR; auto;
  try solve [inverts Sub2];
  try solve [inverts Sub1].
  inverts* Sub1. inverts* Sub2.
Qed.

Lemma UO_sub_unit_arrow_top : forall A, UO A ->
  t_unit <: A -> (t_arrow t_top t_bot) <: A -> t_top <: A.
Proof.
  introv UOR Sub1 Sub2.
  induction UOR; auto;
  try solve [inverts Sub2];
  try solve [inverts Sub1].
  inverts* Sub1. inverts* Sub2.
Qed.

Lemma disj_spec_and_uo_inv1 : forall A1 A2,
  UO (t_and A1 A2) ->
  forall B, UO B ->
  DisjSpec (t_and A1 A2) B ->
  DisjSpec A1 B \/ DisjSpec A2 B \/ DisjSpec A1 A2.
Proof.
  introv UOR1. introv UOB Disj.
  apply all_ord_not_sub in Disj.
  destruct Disj as [Disj1 [Disj2 Disj3]].
  apply not_sub_and_inv in Disj1.
  apply not_sub_and_inv2 in Disj1.
  apply not_sub_and_inv in Disj2.
  apply not_sub_and_inv2 in Disj2.
  apply not_sub_and_inv in Disj3.
  apply not_sub_and_inv2 in Disj3.
  apply not_and_or in Disj1.
  apply not_and_or in Disj2.
  apply not_and_or in Disj3.
  unfold DisjSpec. unfold not.
  destruct Disj1 as [Disj1 | Disj1].
  (* case 1 *)
  destruct Disj2 as [Disj2 | Disj2].
  (* case 1.21 *)
  destruct Disj3 as [Disj3 | Disj3].
  (* case 1.3 *)
  right. right. introv ord Sub.
  destruct Sub as [Sub1 Sub2].
  inverts ord; auto.
  assert ((t_arrow t_top t_bot <: A1)); auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) Sub1.
  (* case 1.2 *)
  apply not_and_or in Disj3.
  destruct Disj3 as [Disj3 | Disj3].
  (* case 1.3 *)
  right. right. introv ord Sub.
  destruct Sub as [Sub1 Sub2].
  inverts ord; auto.
  assert ((t_arrow t_top t_bot <: A2)); auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) Sub2.
  (* case 1.32 *)
  left. introv ord Sub.
  destruct Sub as [Sub1 Sub2].
  inverts ord; auto.
  assert ((t_arrow t_top t_bot <: B)); auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) Sub2.
  (* case 1.2 *)
  apply not_and_or in Disj2.
  destruct Disj2 as [Disj2 | Disj2].
  (* case *)
  (* case 1.21 *)
  destruct Disj3 as [Disj3 | Disj3].
  (* case 1.3 *)
  right. right. introv ord Sub.
  destruct Sub as [Sub1 Sub2].
  inverts ord; auto.
  assert ((t_arrow t_top t_bot <: A1)); auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) Sub1.
  (* case 1.21 *)
  apply not_and_or in Disj3.
  destruct Disj3 as [Disj3 | Disj3].
  (* case 1.3 *)
  right. right. introv ord Sub.
  destruct Sub as [Sub1 Sub2].
  inverts ord; auto.
  assert ((t_arrow t_top t_bot <: A2)); auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) Sub2.
  (* case 1.3 *)
  assert (t_unit <: A1 \/ not (t_unit <: A1)).
  eapply sub_dec_size; eauto.
  assert (t_int <: A2 \/ not (t_int <: A2)).
  eapply sub_dec_size; eauto.
  assert ((t_arrow t_top t_bot) <: A2 \/ not ((t_arrow t_top t_bot) <: A2)).
  eapply sub_dec_size; eauto.
  destruct H. destruct H0. destruct H1.
  right. right.
  intros. destruct H3.
  inverts H2; auto.
  inverts UOR1.
  forwards*: arrow_sub_one_ord H1.
  destruct H2. destruct H2.
  contradiction.
  assert (t_unit <: A2); auto.
  forwards*: sub_transitivity t_top t_unit A2.
  assert ((t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
  eapply sub_dec_size; eauto.
  destruct H2.
  right. right.
  intros. destruct H4.
  inverts H3; auto.
  inverts UOR1.
  forwards*: arrow_sub_one_ord H2; auto.
  destruct H3. destruct H3.
  contradiction.
  forwards*: sub_transitivity t_top t_int A1.
  right. right.
  intros. destruct H4.
  inverts H3. contradiction.
  forwards*: sub_transitivity (t_arrow t_top t_bot) H5.
  contradiction.
  destruct H1.
  assert ((t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
  eapply sub_dec_size; eauto.
  destruct H2.
  right. right. intros.
  destruct H4.
  inverts H3.
  contradiction.
  inverts UOR1.
  forwards*: UO_sub_unit_arrow_top H H2; auto. 
  assert (t_int <: A1).
  forwards*: sub_transitivity t_top t_int A1.
  contradiction.
  contradiction.
  right. right. intros. destruct H4.
  inverts H3; auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) H4.
  right. right. intros.
  destruct H3.
  inverts H2; auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) H4.
  left. intros. destruct H3.
  inverts H2; auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) H4.
  destruct Disj3.
  left. intros. destruct H1. inverts H0; auto.
  forwards*: sub_transitivity (t_arrow t_top t_bot) H1.
  apply not_and_or in H.
  destruct H as [Disj3 | Disj3].
    (* case 1.3 *)
    assert (t_unit <: A1 \/ not (t_unit <: A1)).
    eapply sub_dec_size; eauto.
    assert (t_int <: A2 \/ not (t_int <: A2)).
    eapply sub_dec_size; eauto.
    assert ((t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
    eapply sub_dec_size; eauto.
    destruct H. destruct H0. destruct H1.
    inverts UOR1.
    forwards*: UO_sub_unit_arrow_top H H1.
    assert (t_int <: A1).
    forwards*: sub_transitivity t_top t_int A1.
    contradiction.
    left. intros. inverts H2. destruct H3.
    contradiction.
    destruct H3.
    forwards*: sub_transitivity (t_arrow t_top t_bot) H2.
    destruct H3. contradiction.
    destruct H1.
    inverts UOR1.
    forwards*: UO_sub_unit_arrow_top H H1.
    assert (t_int <: A1).
    forwards*: sub_transitivity t_top t_int A1.
    contradiction.
    right. left.
    intros. inverts H2. destruct H3.
    contradiction. destruct H3.
    forwards*: sub_transitivity (t_arrow t_top t_bot) H2.
    destruct H3. contradiction.
    right. right.
    intros. inverts H2. destruct H3. contradiction. 
    destruct H3. 
    forwards*: sub_transitivity (t_arrow t_top t_bot) H3.
    destruct H3. contradiction.
        (* case 1.3 *)
    assert (t_unit <: A1 \/ not (t_unit <: A1)).
    eapply sub_dec_size; eauto.
    assert (t_int <: A2 \/ not (t_int <: A2)).
    eapply sub_dec_size; eauto.
    assert ((t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
    eapply sub_dec_size; eauto.
    destruct H. destruct H0. destruct H1.
    inverts UOR1.
    forwards*: UO_sub_unit_arrow_top H H1.
    assert (t_int <: A1).
    forwards*: sub_transitivity t_top t_int A1.
    contradiction.
    left. intros. inverts H2. destruct H3.
    contradiction.
    destruct H3.
    forwards*: sub_transitivity (t_arrow t_top t_bot) H2.
    destruct H3. contradiction.
    destruct H1.
    inverts UOR1.
    forwards*: UO_sub_unit_arrow_top H H1.
    assert (t_int <: A1).
    forwards*: sub_transitivity t_top t_int A1.
    contradiction.
    right. left.
    intros. inverts H2. destruct H3.
    contradiction. destruct H3.
    forwards*: sub_transitivity (t_arrow t_top t_bot) H3.
    destruct H3. contradiction.
    left.
    intros. inverts H2. destruct H3. contradiction. 
    destruct H3. 
    forwards*: sub_transitivity (t_arrow t_top t_bot) H3.
    destruct H3. contradiction.
    (* this is proveable *)
    destruct Disj3 as [Disj3 | Disj3].
    destruct Disj2 as [Disj2 | Disj2].
    apply not_and_or in Disj1.
    destruct Disj1 as [Disj1 | Disj1].
    right. right. introv ord [Sub1 Sub2].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub1.
    left. introv ord [Sub1 Sub2].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub1.
    apply not_and_or in Disj1.
    apply not_and_or in Disj2.
    destruct Disj2 as [Disj2 | Disj2].
    destruct Disj1 as [Disj1 | Disj1].
    right. right. introv ord [Sub1 Sub2].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub1.
    (*here we go*)
    assert (Sub1: t_int <: A1 \/ not (t_int <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub1 as [Sub1 | Sub2].
    assert (Sub2: t_unit <: A1 \/ not (t_unit <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub2 as [Sub2 | Sub2].
    inverts UOR1.
    forwards*: UO_sub_int_unit_top Sub1 Sub2.
    forwards*: sub_transitivity t_top (t_arrow t_top t_bot) A1.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    right. right. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    destruct Disj1 as [Disj1 | Disj1].
    (*here we go*)
    assert (Sub1: t_int <: A1 \/ not (t_int <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub1 as [Sub1 | Sub2].
    assert (Sub2: t_unit <: A1 \/ not (t_unit <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub2 as [Sub2 | Sub2].
    inverts UOR1.
    forwards*: UO_sub_int_unit_top Sub1 Sub2.
    forwards*: sub_transitivity t_top (t_arrow t_top t_bot) A1.
    right. right. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    (*goal again*)
    apply not_and_or in Disj3.
    apply not_and_or in Disj1.
    destruct Disj3 as [Disj3 | Disj3].
    destruct Disj2 as [Disj2 | Disj2].
    destruct Disj1 as [Disj1 | Disj1].
    right. right.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
        (*here we go*)
    assert (Sub1: t_int <: A1 \/ not (t_int <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub1 as [Sub1 | Sub2].
    assert (Sub2: (t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub2 as [Sub2 | Sub2].
    inverts UOR1.
    forwards*: UO_sub_int_arrow_top Sub1 Sub2.
    forwards*: sub_transitivity t_top t_unit A1.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    right. right. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    (*goal again*)
    apply not_and_or in Disj2.
    destruct Disj2 as [Disj2 | Disj2].
    destruct Disj1 as [Disj1 | Disj1].
    right. left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    destruct Disj1 as [Disj1 | Disj1].
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    destruct Disj2 as [Disj2 | Disj2].
    destruct Disj1 as [Disj1 | Disj1].
        (*here we go*)
    assert (Sub1: t_int <: A1 \/ not (t_int <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub1 as [Sub1 | Sub2].
    assert (Sub2: (t_arrow t_top t_bot) <: A1 \/ not ((t_arrow t_top t_bot) <: A1)).
    eapply sub_dec_size; eauto.
    destruct Sub2 as [Sub2 | Sub2].
    inverts UOR1.
    forwards*: UO_sub_int_arrow_top Sub1 Sub2.
    forwards*: sub_transitivity t_top t_unit A1.
    right. right. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub8.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    left. introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    (*goal again*)
    apply not_and_or in Disj2.
    destruct Disj2 as [Disj2 | Disj2].
    destruct Disj1 as [Disj1 | Disj1].
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    destruct Disj1 as [Disj1 | Disj1].
    right. left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
    left.
    introv ord [Sub8 Sub9].
    inverts ord; auto.
    forwards*: sub_transitivity (t_arrow t_top t_bot) Sub9.
Qed.

Lemma US_sub : forall A A1 A2,
  US A A1 A2 ->
  sub A1 A /\ sub A2 A.
Proof.
  induction 1; auto.
  destruct IHUS. split*.
  destruct IHUS. split*.
Qed.

Lemma disj_spec_or_uo_inv : forall B B1 B2,
  US B B1 B2 ->
  forall A, DisjSpec A B ->
  DisjSpec A B1 /\ DisjSpec A B2.
Proof.
  introv US DisjS.
  unfold DisjSpec in *. unfold not in *.
  forwards* (SUB1&SUB2): US_sub US.
  split; introv ord [SUB3 SUB4].
  forwards*: sub_transitivity SUB4 SUB1.
  forwards*: sub_transitivity SUB4 SUB2.
Qed.


Lemma US_size_red : forall A A1 A2,
  US A A1 A2 -> t_size A1 < t_size A /\ t_size A2 < t_size A.
Proof.
  induction 1; intros; simpl. lia.
  destruct IHUS. split. lia. lia.
  destruct IHUS. split. lia. lia.
Defined.

Lemma Disj2_Complete_size : forall n A B,
  t_size (t_and A B) <= n ->
  DisjSpec A B -> Disj2 A B.
Proof.
    intros n.
    induction n; introv LESS.
    simpl in LESS. lia.
    introv Disj.
    simpl in *.
    induction A.
    1: { (*top case*)
      induction B; eauto.
      4: {
        apply disj_inv_union in Disj.
        destruct Disj as [Disj1 Disj2].
        simpl in LESS.
        forwards: IHB1 Disj1. lia.
        forwards: IHB2 Disj2. lia.
        eauto.
      }
      4: {
        simpl in LESS.
        apply disj_inv_and_top in Disj; auto.
        forwards*: IHn B1 B2. lia.
      }
      specialize (Disj t_int); unfold not in Disj;
      forwards*: Disj.
      specialize (Disj t_int); unfold not in Disj;
      forwards*: Disj.
      clear IHB1 IHB2.
      specialize (Disj (t_arrow t_top t_bot)); unfold not in Disj;
      forwards*: Disj.
      specialize (Disj t_unit); unfold not in Disj;
      forwards*: Disj.
    }
    5: { (*and case*)
        simpl in *.
        forwards TEMP1: UO_or_US B.
        destruct TEMP1 as [TEMP1 | TEMP1].
        (* case UO B *)
        (* this is proveable *)
        forwards TEMP2: UO_or_US (t_and A1 A2).
        destruct TEMP2 as [TEMP2 | TEMP2].
        (* UO A1&A2 *)
        apply disj_spec_and_uo_inv1 in Disj; auto.
        destruct Disj as [Disj | [Disj | Disj]].
        forwards*: IHA1 Disj. lia.
        forwards*: IHA2 Disj. lia.
        forwards*: IHn Disj. lia.
        (*US (A1&A2) A3 A4*)
        destruct TEMP2 as [A3 [A4 TEMP3]].
        apply disj_spec_sym in Disj.
        eapply disj_spec_or_uo_inv in Disj; eauto.
        destruct Disj as [Disj1 Disj2].
        apply disj_spec_sym in Disj1.
        apply disj_spec_sym in Disj2.
        forwards*: IHn Disj1.
        forwards* (LESS1&LESS2): US_size_red TEMP3. 
        simpl in *. lia.
        forwards*: IHn Disj2.
        forwards* (LESS1&LESS2): US_size_red TEMP3.
        simpl in *. lia.
        (*case US B*)
        destruct TEMP1 as [B1 [B2 TEMP1]].
        eapply disj_spec_or_uo_inv in Disj; eauto.
        destruct Disj as [Disj1 Disj2].
        forwards*: IHn Disj1. simpl.
        forwards* (LESS1&LESS2): US_size_red TEMP1. lia.
        forwards*: IHn Disj2. simpl.
        forwards* (LESS1&LESS2): US_size_red TEMP1. lia.
    }
    4: { (*union case*)
        apply disj_spec_sym in Disj.
        eapply disj_spec_or_uo_inv in Disj; eauto.
        destruct Disj as [Disj1 Disj2].
        apply disj_spec_sym in Disj1.
        apply disj_spec_sym in Disj2.
        forwards*: IHA1. simpl in *. lia.
        forwards*: IHA2. simpl in *. lia.
    }
    1: { (*int case*)
      induction B; eauto.
      specialize (Disj t_int).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
      specialize (Disj t_int).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
      simpl in *.
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHB1. lia.
      forwards*: IHB2. lia.
      simpl in *.
      apply disj_spec_sym in Disj.
      (* this is proveable *)
      forwards TEMP2: UO_or_US (t_and B1 B2).
      destruct TEMP2 as [TEMP2 | TEMP2].
      (* UO B11&B2 *)
      apply disj_spec_and_uo_inv1 in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      1,2: apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia.
      (*US (A1&A2) A3 A4*)
      destruct TEMP2 as [A3 [A4 TEMP3]].
      apply disj_spec_sym in Disj.
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHn Disj1.
      forwards* (LESS1&LESS2): US_size_red TEMP3. 
      simpl in *. lia.
      forwards*: IHn Disj2.
      forwards* (LESS1&LESS2): US_size_red TEMP3.
      simpl in *. lia.      
      (* apply disj_spec_and_uo_inv in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      apply disj_spec_sym in Disj.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia. *)
    }
    1: { (*bot case*)
      auto.
    }
    1: { (*arrow case*)
      clear IHA1 IHA2.
      induction B; eauto.
      specialize (Disj (t_arrow t_top t_bot)).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
      specialize (Disj (t_arrow t_top t_bot)).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
      simpl in *.
      (*arrow union case*)
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHB1. lia.
      forwards*: IHB2. lia.
      (*arrow and case*)
      simpl in *.
      (* this is proveable *)
      forwards TEMP2: UO_or_US (t_and B1 B2).
      destruct TEMP2 as [TEMP2 | TEMP2].
      (* UO B11&B2 *)
      apply disj_spec_sym in Disj.
      apply disj_spec_and_uo_inv1 in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      1,2: apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia.
      (*US (A1&A2) A3 A4*)
      destruct TEMP2 as [A3 [A4 TEMP3]].
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHn Disj1.
      forwards* (LESS1&LESS2): US_size_red TEMP3. 
      simpl in *. lia.
      forwards*: IHn Disj2.
      forwards* (LESS1&LESS2): US_size_red TEMP3.
      simpl in *. lia.
      (*
      apply disj_spec_and_uo_inv in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      apply disj_spec_sym in Disj.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia. *)
    }
    1: { (*unit case*)
      induction B; eauto.
      specialize (Disj t_unit).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
      simpl in *.
      (*unit union case*)
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHB1. lia.
      forwards*: IHB2. lia.
      (*unit and case*)
      simpl in *.
      (* this is proveable *)
      forwards TEMP2: UO_or_US (t_and B1 B2).
      destruct TEMP2 as [TEMP2 | TEMP2].
      (* UO B11&B2 *)
      apply disj_spec_sym in Disj.
      apply disj_spec_and_uo_inv1 in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      1,2: apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia.
      (*US (A1&A2) A3 A4*)
      destruct TEMP2 as [A3 [A4 TEMP3]].
      eapply disj_spec_or_uo_inv in Disj; eauto.
      destruct Disj as [Disj1 Disj2].
      forwards*: IHn Disj1.
      forwards* (LESS1&LESS2): US_size_red TEMP3. 
      simpl in *. lia.
      forwards*: IHn Disj2.
      forwards* (LESS1&LESS2): US_size_red TEMP3.
      simpl in *. lia.
      (* simpl in *.
      apply disj_spec_sym in Disj.
      apply disj_spec_and_uo_inv in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      apply disj_spec_sym in Disj.
      forwards*: IHB1 Disj. lia.
      apply disj_spec_sym in Disj.
      forwards*: IHB2 Disj. lia.
      forwards*: IHn Disj. lia. *)
      specialize (Disj t_unit).
      unfold not in Disj. forwards: Disj; eauto. inverts H.
    }
Qed.

Lemma disj_sub2 : forall A B C,
  DisjSpec A B ->
  sub C B ->
  DisjSpec A C.
Proof.
  introv disj sub.
  unfold DisjSpec in *.
  unfold not in *.
  intros.
  destruct H0.
  eapply sub_transitivity in sub; eauto.
Qed.

Lemma disj_dec : forall n A B,
  (t_size A + t_size B) < n ->
  A *2a B \/ not (A *2a B).
Proof.
  intros n.
  induction n.
  (*n=0*)
  intros. lia.
  (*n=Sn'*)
  intros A.
  induction A; introv LESS.
  1:{ (*top*)
    induction B; eauto;
    try solve [right; unfold not; 
      introv Disj; inverts Disj; inverts H; inverts H].
      destruct IHB1; destruct IHB2; simpl in *;
      try solve [lia].
      (*or case*)
      left*.
      right. unfold not. introv Disj.
      inverts Disj. inverts H1.
      inverts H1. contradiction.
      right. unfold not. introv Disj.
      inverts Disj. inverts H1.
      inverts H1. contradiction.
      right. unfold not. introv Disj.
      inverts Disj. inverts H1.
      inverts H1. contradiction.
      (*and case*)
      simpl in *.
      forwards* UOUS: UO_or_US (t_and B1 B2).
      destruct UOUS as [UOUS | UOUS]. 
      forwards* TEMP1: IHn B1 B2. lia.
      destruct TEMP1 as [TEMP1 | TEMP1].
      auto.
      destruct IHB1; destruct IHB2; try solve [lia].
      left*. left*. left*.
      right. unfold not. introv Disj.
      apply Disj2_sound in Disj.
      apply disj_spec_sym in Disj.
      apply disj_spec_and_uo_inv1 in Disj; auto.
      destruct Disj as [Disj | [Disj | Disj]].
      1,2: apply disj_spec_sym in Disj.
      1,2,3: eapply Disj2_Complete_size in Disj; eauto.
      (*case*)
      destruct UOUS as [A1 [A2 UOUS]].
      forwards* (LESS1&LESS2): US_size_red UOUS.
      forwards* Disj1: IHn t_top A1.
      simpl in *. lia.
      forwards* Disj2: IHn t_top A2.
      simpl in *. lia.
      destruct Disj1 as [Disj1 | Disj1];
      destruct Disj2 as [Disj2 | Disj2].
      left*.
      (*proveable*)
      right. unfold not. introv Disj.
      apply Disj2_sound in Disj.
      forwards* TEMP1: disj_spec_or_uo_inv Disj.
      destruct TEMP1 as [Disj4 Disj5].
      eapply Disj2_Complete_size in Disj5; eauto.
      (*case*)
      right. unfold not. introv Disj.
      apply Disj2_sound in Disj.
      forwards* TEMP1: disj_spec_or_uo_inv Disj.
      destruct TEMP1 as [Disj4 Disj5].
      eapply Disj2_Complete_size in Disj4; eauto.
      (*case*)
      right. unfold not. introv Disj.
      apply Disj2_sound in Disj.
      forwards* TEMP1: disj_spec_or_uo_inv Disj.
      destruct TEMP1 as [Disj4 Disj5].
      eapply Disj2_Complete_size in Disj5; eauto.
  }
  1:{ (*int*)
    induction B; eauto.
    (*top*)
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
    (*or case*)
    destruct IHB1; destruct IHB2; simpl in *;
    try solve [lia].
    left*.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    (*and case*)
    (*and case*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and B1 B2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn B1 B2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct IHB1; destruct IHB2; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2: apply disj_spec_sym in Disj.
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [A1 [A2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn t_int A1.
    simpl in *. lia.
    forwards* Disj2: IHn t_int A2.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
  }
  1:{ (*bot*)
    left*.
  }
  1:{ (*arrow*)
    clear IHA1 IHA2.
    induction B; eauto.
    (*top*)
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
    (*or case*)
    destruct IHB1; destruct IHB2; simpl in *;
    try solve [lia].
    left*.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    (*and case*)
    (*and case*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and B1 B2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn B1 B2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct IHB1; destruct IHB2; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2: apply disj_spec_sym in Disj.
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [D1 [D2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn (t_arrow A1 A2) D1.
    simpl in *. lia.
    forwards* Disj2: IHn (t_arrow A1 A2) D2.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
  }
  1:{ (*or*)
    simpl in *.
    destruct (IHA1 B); destruct (IHA2 B);
    try solve [lia].
    left*.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards*: disj_spec_or_uo_inv Disj.
    destruct H1 as [Disj2 Disj3];
    apply disj_spec_sym in Disj2;
    apply disj_spec_sym in Disj3.
    eapply Disj2_Complete_size in Disj3; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards*: disj_spec_or_uo_inv Disj.
    destruct H1 as [Disj2 Disj3];
    apply disj_spec_sym in Disj2;
    apply disj_spec_sym in Disj3.
    eapply Disj2_Complete_size in Disj2; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards*: disj_spec_or_uo_inv Disj.
    destruct H1 as [Disj2 Disj3];
    apply disj_spec_sym in Disj2;
    apply disj_spec_sym in Disj3.
    eapply Disj2_Complete_size in Disj2; eauto.
  }
  1: { (*and*)
    induction B; eauto.

    (*top*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and A1 A2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn A1 A2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct (IHA1 t_top); destruct (IHA2 t_top); 
    simpl in *; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [D1 [D2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn D1 t_top.
    simpl in *. lia.
    forwards* Disj2: IHn D2 t_top.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj4.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.

    (*int*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and A1 A2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn A1 A2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct (IHA1 t_int); destruct (IHA2 t_int); 
    simpl in *; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [D1 [D2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn D1 t_int.
    simpl in *. lia.
    forwards* Disj2: IHn D2 t_int.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj4.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.

    (*arrow*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and A1 A2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn A1 A2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct (IHA1 (t_arrow B1 B2)); destruct (IHA2 (t_arrow B1 B2)); 
    simpl in *; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [D1 [D2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn D1 (t_arrow B1 B2).
    simpl in *. lia.
    forwards* Disj2: IHn D2 (t_arrow B1 B2).
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj4.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.

    (*union*)
    simpl in *.
    destruct IHB1; destruct IHB2;
    try solve [lia].
    left*.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj2 Disj3].
    eapply Disj2_Complete_size in Disj3; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj2 Disj3].
    eapply Disj2_Complete_size in Disj2; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj2 Disj3].
    eapply Disj2_Complete_size in Disj2; eauto.

    (*and*)
    simpl in *.
    forwards* UOUS1: UO_or_US (t_and B1 B2).
    forwards* UOUS2: UO_or_US (t_and A1 A2).
    forwards* TEMP1: IHn A1 A2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1]; auto.
    forwards* TEMP2: IHn B1 B2. lia.
    destruct TEMP2 as [TEMP2 | TEMP2]; auto.

    destruct UOUS1 as [UOUS1 | UOUS1].
    destruct UOUS2 as [UOUS2 | UOUS2]. 
    forwards* TEMP3: IHB1. lia.
    forwards* TEMP4: IHB2. lia.
    destruct TEMP3 as [TEMP3 | TEMP3];
    destruct TEMP4 as [TEMP4 | TEMP4]; auto.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP6: disj_spec_and_uo_inv1 Disj.
    destruct TEMP6 as [Disj4 | [Disj4 | Disj4]].
    1,2: apply disj_spec_sym in Disj4;
         eapply Disj2_Complete_size in Disj4; eauto.
    eapply Disj2_Complete_size in Disj4; eauto.

    destruct UOUS2 as [D3 [D4 UOUS2]].
    forwards* (LESS1&LESS2): US_size_red UOUS2.
    forwards* TEMP3: IHn D3 (t_and B1 B2).
    simpl in *. lia.
    forwards* TEMP4: IHn D4 (t_and B1 B2).
    simpl in *. lia.
    destruct TEMP3 as [TEMP3 | TEMP3];
    destruct TEMP4 as [TEMP4 | TEMP4].
    left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    apply disj_spec_sym in Disj4.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.

    destruct UOUS1 as [D1 [D2 UOUS1]].
    forwards* (LESS1&LESS2): US_size_red UOUS1.
    forwards* TEMP3: IHn (t_and A1 A2) D1.
    simpl in *. lia.
    forwards* TEMP4: IHn (t_and A1 A2) D2.
    simpl in *. lia.
    destruct TEMP3 as [TEMP3 | TEMP3];
    destruct TEMP4 as [TEMP4 | TEMP4].
    left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* (Disj4&Disj5): disj_spec_or_uo_inv Disj.
    eapply Disj2_Complete_size in Disj5; eauto.

    (*unit*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and A1 A2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn A1 A2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct (IHA1 t_unit); destruct (IHA2 t_unit); 
    simpl in *; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [D1 [D2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn D1 t_unit.
    simpl in *. lia.
    forwards* Disj2: IHn D2 t_unit.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj4.
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    apply disj_spec_sym in Disj5.
    eapply Disj2_Complete_size in Disj5; eauto.
  }
  1:{ (*unit*)
    induction B; eauto.
    (*top*)
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
    (*or case*)
    destruct IHB1; destruct IHB2; simpl in *;
    try solve [lia].
    left*.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    right. introv Disj. inverts Disj.
    inverts H1. inverts H1. contradiction.
    (*and case*)
    (*and case*)
    simpl in *.
    forwards* UOUS: UO_or_US (t_and B1 B2).
    destruct UOUS as [UOUS | UOUS]. 
    forwards* TEMP1: IHn B1 B2. lia.
    destruct TEMP1 as [TEMP1 | TEMP1].
    auto.
    destruct IHB1; destruct IHB2; try solve [lia].
    left*. left*. left*.
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    apply disj_spec_sym in Disj.
    apply disj_spec_and_uo_inv1 in Disj; auto.
    destruct Disj as [Disj | [Disj | Disj]].
    1,2: apply disj_spec_sym in Disj.
    1,2,3: eapply Disj2_Complete_size in Disj; eauto.
    (*case*)
    destruct UOUS as [A1 [A2 UOUS]].
    forwards* (LESS1&LESS2): US_size_red UOUS.
    forwards* Disj1: IHn t_unit A1.
    simpl in *. lia.
    forwards* Disj2: IHn t_unit A2.
    simpl in *. lia.
    destruct Disj1 as [Disj1 | Disj1];
    destruct Disj2 as [Disj2 | Disj2].
    left*.
    (*proveable*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj4; eauto.
    (*case*)
    right. unfold not. introv Disj.
    apply Disj2_sound in Disj.
    forwards* TEMP1: disj_spec_or_uo_inv Disj.
    destruct TEMP1 as [Disj4 Disj5].
    eapply Disj2_Complete_size in Disj5; eauto.
    (*unit case*)
    right. unfold not. introv Disj.
    inverts Disj. inverts H. inverts H.
  }
Qed.