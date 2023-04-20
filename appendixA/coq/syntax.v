(*

This Coq formalization corresponds to
Appendix A in thesis.

March 15, 2023:
---------------
-> Union + intersection + unit
-> No nominal types
-> Sound and complete disjointness
-> Disjointness based on COST
-> Sound and complete COST

*)

Require Import TLC.LibLN.
Require Import Program.Equality.
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

Definition COSTS A B := exists C, Ord C /\ sub C A /\ sub C B.

Inductive COST : typ -> typ -> Prop :=
  | ctop1 : COST t_top t_top
  | ctop2 : forall A, Ord A -> 
      COST A t_top
  | ctop3 : forall A, Ord A -> 
      COST t_top A
  | cint : COST t_int t_int
  | cbool : COST t_unit t_unit
  | carrow : forall A1 A2 B1 B2,
      COST (t_arrow A1 B1) (t_arrow A2 B2)
  | cor1 : forall A A1 A2 B,
      US A A1 A2 -> 
      COST A1 B -> 
      COST A B
  | cor2 : forall A A1 A2 B, 
      US A A1 A2 -> 
      COST A2 B ->
      COST A B
  | cor3 : forall A B B1 B2,
      US B B1 B2 ->
      COST A B1 ->  
      COST A B
  | cor4 : forall A B B1 B2,
      US B B1 B2 ->
      COST A B2 ->
      COST A B
  | cand1 : forall A1 A2 B, 
      UO B -> 
      COST A1 B -> 
      COST A2 B ->
      COST A1 A2 -> 
      COST (t_and A1 A2) B
  | cand2 : forall A B1 B2, 
      UO A -> 
      COST A B1 -> 
      COST A B2 -> 
      COST B1 B2 ->
      COST A (t_and B1 B2).

#[export]      
Hint Constructors sub Ord COST UO US : core.


Lemma us_subl : forall A A1 A2 B, US A A1 A2 -> sub B A1 -> sub B A.
  induction 1; intros; eauto.
  - apply sub_and in H0.
    destruct H0; eauto.
  - apply sub_and in H1.
    destruct H1; eauto.
Defined.

Lemma us_subr : forall A A1 A2 B, US A A1 A2 -> sub B A2 -> sub B A.
  induction 1; intros; eauto.
  - apply sub_and in H0.
    destruct H0; eauto.
  - apply sub_and in H1.
    destruct H1; eauto.
Defined.

Require Import TLC.LibLN.


Lemma UO_sub_ord : forall A, 
  UO A ->
  forall C1, Ord C1 -> sub C1 A -> 
  forall C2, Ord C2 -> sub C2 A ->
  (exists D, Ord D /\ sub D C1 /\ sub D C2) \/ (sub t_top A).
Proof.
  introv UO1.
  induction UO1; introv Ord1 Sub1 Ord2 Sub2.
  1: {
    inverts Ord1; try solve [inverts Sub1].
    inverts Ord2; try solve [inverts Sub2].
    left. exists* t_int.
  }
  1: {
    inverts Ord1; try solve [inverts Sub1].
    inverts Ord2; try solve [inverts Sub2].
    left. exists* (t_arrow t_top t_bot).
  }
  1: {
    inverts Ord1; try solve [inverts Sub1].
    inverts Ord2; try solve [inverts Sub2].
    left. exists* t_unit.
  }
  1: {
    apply sub_and in Sub1.
    destruct Sub1 as [Sub11 Sub12].
    apply sub_and in Sub2.
    destruct Sub2 as [Sub21 Sub22].
    forwards*: IHUO1_1 Ord1 Sub11 Ord2 Sub21.
    forwards*: IHUO1_2 Ord1 Sub12 Ord2 Sub22.
  }
  1: { (*top*)
    right*.
  }
  1: {
    inverts Ord1; inverts Sub1.
  }
Qed.

Lemma cost_sound : forall A B, COST A B -> COSTS A B.
  induction 1; unfold COSTS in *; intros.
  - (*case top*)
    exists t_int; split; eauto.
  - (*case top*)
    exists A. split; eauto.
  - (*case top*)
    exists A. split; eauto.
  - (*case int*)
    exists t_int; intros; split; eauto.
  - (*case unit*)
    exists t_unit; intros; split; eauto.
  - (*case arrow*)
    exists (t_arrow t_top t_bot); split; auto.
  - (*case US*)
    destruct IHCOST.
    exists x. destruct H1. destruct H2.
    eapply us_subl in H; eauto.
  - (*case US*)
    destruct IHCOST.
    exists x. destruct H1. destruct H2.
    eapply us_subr in H; eauto.
  - (*case US*)
    destruct IHCOST.
    exists x. destruct H1. destruct H2.
    eapply us_subl in H; eauto.
  - (*case US*)
    destruct IHCOST.
    exists x. destruct H1. destruct H2.
    eapply us_subr in H; eauto.
  - (*and1*)
    destruct IHCOST1 as [T1 [Ord1 [Sub11 Sub12]]].
    destruct IHCOST2 as [T2 [Ord2 [Sub21 Sub22]]].
    forwards* : UO_sub_ord H Sub12 Sub22.
    destruct H3 as [[D[Ord3[Sub31 Sub32]]] | TEMP2].
    exists D. splits; auto.
    apply s_anda.
    forwards*: sub_transitivity Sub31 Sub11.
    forwards*: sub_transitivity Sub32 Sub21.
    forwards*: sub_transitivity Sub31 Sub12.
    destruct IHCOST3 as [T3 [Ord3 [Sub31 Sub32]]].
    exists T3. splits; auto.
    forwards*: sub_transitivity t_top T3 B.
  - (*and2*)
    destruct IHCOST1 as [T1 [Ord1 [Sub11 Sub12]]].
    destruct IHCOST2 as [T2 [Ord2 [Sub21 Sub22]]].
    forwards* : UO_sub_ord H Sub11 Sub21.
    destruct H3 as [[D[Ord3[Sub31 Sub32]]] | TEMP2].
    exists D. splits; auto.
    forwards*: sub_transitivity Sub31 Sub11.
    apply s_anda.
    forwards*: sub_transitivity Sub31 Sub12.
    forwards*: sub_transitivity Sub32 Sub22.
    destruct IHCOST3 as [T3 [Ord3 [Sub31 Sub32]]].
    exists T3. splits; auto.
    forwards*: sub_transitivity t_top T3 A.
Qed.

    
Lemma costs_and : forall A B1 B2, COSTS A (t_and B1 B2) -> COSTS A B1 /\ COSTS A B2 /\ COSTS B1 B2.
  intros; unfold COSTS in *.
  destruct H. destruct H. destruct H0.
  apply sub_and in H1.
  destruct H1.
  split. exists x; eauto.
  split; exists x; split; eauto.
Defined.

Lemma costs_or : forall A B1 B2, COSTS A (t_union B1 B2) -> COSTS A B1 \/ COSTS A B2.
  intros; unfold COSTS in *.
  destruct H. destruct H. destruct H0.
  dependent destruction H1; eauto.
  dependent destruction H.
  dependent destruction H.
  dependent destruction H.
Defined.

Lemma costs_sym : forall A B, COSTS A B -> COSTS B A.
  intros.
  unfold COSTS in *.
  destruct H.
  dependent destruction H.
  dependent destruction H0.
  exists x; eauto.
Defined.

Lemma sub_or_ord : forall A B C, sub A (t_union B C) -> Ord A -> sub A B \/ sub A C.
  intros. dependent induction H; eauto.
  all: try solve [inverts H0; inverts H1].
Defined.

Lemma gsub_or : forall A A1 A2, US A A1 A2 -> forall x, Ord x -> sub x A -> sub x A1 \/ sub x A2.
  induction 1; intros; eauto.
  - apply sub_or_ord in H0; eauto.
  - apply sub_and in H1. destruct H1.
    apply IHUS in H1; eauto.
    destruct H1; eauto.
  - apply sub_and in H2.
    destruct H2.
    apply IHUS in H3; eauto.
    destruct H3; eauto.
Defined.
    
Lemma costs_us : forall B B1 B2, US B B1 B2 -> forall A, COSTS A B -> COSTS A B1 \/ COSTS A B2.
  destruct 1; intros; eauto.
  - apply costs_or; eauto.
  - destruct H0. destruct H0. destruct H1.
    eapply gsub_or in H2; eauto.
    destruct H2. unfold COSTS.
    left.  exists x. eauto.
    right. exists x. eauto.
  - destruct H1. destruct H1. destruct H2.
    eapply gsub_or in H3 ; eauto.
    destruct H3. unfold COSTS.
    left.  exists x. eauto.
    right. exists x. eauto.
Defined.


Lemma UO_dec : forall A, UO A \/ not (UO A).
  induction A; eauto.
  - right. unfold not; intros.
    dependent destruction H.
  - destruct IHA1; destruct IHA2; eauto.
    all: try solve [right; unfold not; intros;
    inverts H1; contradiction].
Defined.


Lemma uo_not_split : forall A, UO A -> not (exists A1 A2, US A A1 A2).
  induction 1; unfold not; intros.
  - destruct H. destruct H. dependent destruction H.
  - destruct H. destruct H. dependent destruction H.
  - destruct H. destruct H. dependent destruction H.
  - destruct H1. destruct H1.
    dependent destruction H1.
    apply IHUO1.
    exists A1. exists A2. eauto.
    apply IHUO2.
    exists B1. exists B2. eauto.
  - destruct H. destruct H. dependent destruction H.
  - destruct H. destruct H. dependent destruction H.
Defined.


Lemma us_not_ord : forall A A1 A2, US A A1 A2 -> not (UO A).
  induction 1; unfold not; intros.
  - dependent destruction H.
  - dependent destruction H0.
    contradiction.
  - dependent destruction H1.
    contradiction.
Defined.

Lemma not_uo_and : forall A1 A2, not (UO (t_and A1 A2)) -> (not (UO A1)) \/ (UO A1 /\ (not (UO A2))).
  intros.
  destruct (UO_dec A1); destruct (UO_dec A2); eauto.
Defined.


Lemma US_det : forall A A1 A2, US A A1 A2 -> forall A3 A4, US A A3 A4 -> A1 = A3 /\ A2 = A4.
  induction 1; intros; eauto.
  - dependent destruction H; eauto.
  - dependent destruction H0.
    apply IHUS in H0. destruct H0. subst. eauto.
    apply us_not_ord in H. contradiction.
  - dependent destruction H1.
    apply us_not_ord in H1. contradiction.
    apply IHUS in H2. destruct H2. subst. eauto.
Defined.

Lemma ord_sub_int : forall A, Ord A -> sub A t_int -> A = t_int.
  intros.
  destruct H; eauto;
  dependent destruction H0.
Defined.

Lemma ord_sub_bool : forall A, Ord A -> sub A t_unit -> A = t_unit.
  intros.
  destruct H; eauto;
  dependent destruction H0.
Defined.

Lemma ord_sub_arrow : forall A A1 B1, Ord A -> sub A (t_arrow A1 B1) -> exists A2 B2, A = (t_arrow A2 B2).
  intros.
  destruct H; eauto;
  dependent destruction H0.
Defined.


Lemma ord_sub1 : forall B, sub t_int B -> forall C, sub t_int C -> UO B -> UO C -> sub B C \/ sub C B.
  intros B Sub.
  dependent induction Sub; intros; eauto.
  + dependent destruction H0.
  + dependent destruction H0.
  + dependent destruction H0.
    assert (EQ: t_int = t_int); auto.
    specialize (IHSub1 EQ C H H0_ H1).
    specialize (IHSub2 EQ C H H0_0 H1).
    destruct IHSub1; destruct IHSub2; auto.
Qed.

Lemma ord_sub2 : forall B, sub t_unit B -> forall C, sub t_unit C -> UO B -> UO C -> sub B C \/ sub C B.
  intros B Sub.
  dependent induction Sub; intros; eauto.
  + dependent destruction H0.
  + dependent destruction H0.
  + dependent destruction H0.
    assert (EQ: t_unit = t_unit); auto.
    specialize (IHSub1 EQ C H H0_ H1).
    specialize (IHSub2 EQ C H H0_0 H1).
    destruct IHSub1; destruct IHSub2; auto.
Qed.


Lemma UO_OR_US : forall A, UO A \/ (exists A1 A2, US A A1 A2).
Proof.
  intros A.
  induction A; eauto.
  destruct IHA1; destruct IHA2; auto.
  destruct H0 as [B1 [B2 SPL1]]. right*.
  destruct H as [B1 [B2 SPL1]]. right*.
  destruct H as [B1 [B2 SPL1]]. right*.
Qed.

Lemma US_size_red : forall A A1 A2,
  US A A1 A2 -> t_size A1 < t_size A /\ t_size A2 < t_size A.
Proof.
  induction 1; intros; simpl. lia.
  destruct IHUS. split. lia. lia.
  destruct IHUS. split. lia. lia.
Defined.


(* COST completeness *)

Lemma cost_complete : forall n A B, 
  (t_size A + t_size B) < n -> COSTS A B -> COST A B.
  intro n. induction n.
  1: { (*n=0*)
      intros. lia.
      }
  (*n=Sn'*)
  intros A.
  induction A.
  1:{ (*top*)
     intros B. induction B; introv LESS CST; auto.
    + destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2.
    + (*and*)
      eapply costs_us in CST; eauto.
      destruct CST as [CST | CST].
      forwards*: IHB1 CST. simpl in *. lia.
      forwards*: IHB2 CST. simpl in *. lia.
    + (*union*)
      apply costs_and in CST.
      destruct CST as [CST1 [CST2 CST3]].
      (* induction on size? *)
      apply cand2; auto.
      forwards*: IHB1 CST1. simpl in *. lia.
      forwards*: IHB2 CST2. simpl in *. lia.
      forwards*: IHn B1 B2. simpl in *. lia.
   }
  1:{ (*int*)
      introv LESS CST.
      simpl in *.
      induction B; eauto.
      (*bot*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2.
      (*arrow*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
      (*union*)
      eapply costs_us in CST; eauto.
      destruct CST as [CST | CST].
      forwards*: IHB1 CST. simpl in *. lia.
      forwards*: IHB2 CST. simpl in *. lia.
      (* induction on size? *)
      (*and*)
      apply costs_and in CST.
      destruct CST as [CST1 [CST2 CST3]].
      simpl in *.
      apply cand2; auto.
      forwards*: IHB1 CST1. simpl in *. lia.
      forwards*: IHB2 CST2. simpl in *. lia.
      forwards*: IHn CST3. simpl in *. lia.
      (*unit*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
  }
  1: { (*bot*)
   intros B LESS CST.
    destruct CST. destruct H. destruct H0.
    inverts H; inverts H0.
  }
    1:{ (*arrow*)
      introv LESS CST.
      simpl in *.
      induction B; eauto.
      (*int*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
      (*bot*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2.
      (*union*)
      eapply costs_us in CST; eauto.
      destruct CST as [CST | CST].
      forwards*: IHB1 CST. simpl in *. lia.
      forwards*: IHB2 CST. simpl in *. lia.
      (*and*)
      apply costs_and in CST.
      destruct CST as [CST1 [CST2 CST3]].
      (* induction on size? *)
      simpl in *.
      apply cand2; auto.
      forwards*: IHB1 CST1. simpl in *. lia.
      forwards*: IHB2 CST2. simpl in *. lia.
      forwards*: IHn CST3. simpl in *. lia.
      (*unit*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
    }
  1: { (*union*)
    introv LESS CST.
    apply costs_sym in CST.
    eapply costs_us in CST; eauto.
    destruct CST as [CST | CST]; 
      apply costs_sym in CST.
    simpl in *.
    forwards*: IHA1. lia.
    simpl in *.
    forwards*: IHA2. lia.
  }
  1: { (*intersection*)
    introv LESS CST.
    forwards* TEMP1: UO_OR_US B.
    destruct TEMP1 as [UOR | [B1 [B2 SPL]]].
    (*case UO B*)
    apply costs_sym in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    apply costs_sym in CST1.
    apply costs_sym in CST2.
    simpl in *.
    forwards* CST11: IHA1 CST1. lia.
    forwards* CST21: IHA2 CST2. lia.
    forwards* CST31: IHn CST3. lia.
    (*case US B*)
    eapply costs_us in CST; eauto.
    destruct CST as [CST | CST].
    forwards*: IHn CST. simpl in *.
    forwards* (LESS1&LESS2): US_size_red SPL.
    lia.
    forwards*: IHn CST. simpl in *.
    forwards* (LESS1&LESS2): US_size_red SPL.
    lia.
  }
    1:{ (*unit*)
      introv LESS CST.
      simpl in *.
      induction B; eauto.
      (*int*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
      (*bot*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2.
      (*arrow*)
      destruct CST as [D [OrdD [SubD1 SubD2]]].
      inverts OrdD; inverts SubD2. inverts SubD1.
      (*union*)
      eapply costs_us in CST; eauto.
      destruct CST as [CST | CST].
      forwards*: IHB1 CST. simpl in *. lia.
      forwards*: IHB2 CST. simpl in *. lia.
      (*and*)
      apply costs_and in CST.
      destruct CST as [CST1 [CST2 CST3]].
      (* induction on size? *)
      simpl in *.
      apply cand2; auto.
      forwards*: IHB1 CST1. simpl in *. lia.
      forwards*: IHB2 CST2. simpl in *. lia.
      forwards*: IHn CST3. simpl in *. lia.
    }
Qed.

(* COST decidebility *)

Lemma cost_dec : forall n A B,
  (t_size A + t_size B < n) -> COST A B \/ ~ COST A B.
Proof.
  induction n; introv LESS.
  (*n=0*)
  lia.
  (*n=Sn'*)
  induction A; auto.
  1:{ (*top*)
    induction B; auto; simpl in *.
    (*bot*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD2.
    inverts SubD2.
    (*union*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_or in CST.
    destruct CST.
    eapply cost_complete in H1; eauto.
    eapply cost_complete in H1; eauto.
    (*and*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    forwards*: IHn B1 B2. lia.
    destruct H1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST3; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST2; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
  }
  1: { (*int*)
    induction B; auto; simpl in *.
    (*bot*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD2.
    inverts SubD2.
    (*arrow*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD1.
    inverts SubD2.
    (*union*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_or in CST.
    destruct CST.
    eapply cost_complete in H1; eauto.
    eapply cost_complete in H1; eauto.
    (*and*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    forwards*: IHn B1 B2. lia.
    destruct H1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST3; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST2; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
    (*unit*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD1.
    inverts SubD1.
  }
  1:{ (*bot*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD1. inverts SubD1.
    inverts SubD1.
  }
  1: { (*arrow*)
    induction B; auto; simpl in *.
    (*int*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD1. inverts SubD2.
    inverts SubD2.
    (*bot*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD2.
    inverts SubD2.
    simpl in *.
    (*union*)
    clear IHA1 IHA2 IHB1 IHB2.
    forwards* CST1: IHn (t_arrow A1 A2) B1.
    simpl. lia.
    forwards* CST2: IHn (t_arrow A1 A2) B2.
    simpl. lia.
    destruct CST1 as [CST11 | CST12];
    destruct CST2 as [CST21 | CST22]; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_or in CST.
    destruct CST as [CST | CST].
    eapply cost_complete in CST; eauto.
    eapply cost_complete in CST; eauto.
    (*and*)
    clear IHA1 IHA2 IHB1 IHB2.
    forwards* CST1: IHn (t_arrow A1 A2) B1.
    simpl. lia.
    forwards* CST2: IHn (t_arrow A1 A2) B2.
    simpl. lia.
    forwards* CST3: IHn B1 B2.
    simpl. lia.
    destruct CST1 as [CST11 | CST12];
    destruct CST2 as [CST21 | CST22];
    destruct CST3 as [CST31 | CST32]; eauto.
    (*repetitive goals*)
      (*1*)
   1-7: right; unfold not; introv CST;
        apply cost_sound in CST;
        apply costs_and in CST;
        destruct CST as [CST1 [CST2 CST3]];
        try solve [eapply cost_complete in CST1; eauto];
        try solve [eapply cost_complete in CST2; eauto];
        try solve [eapply cost_complete in CST3; eauto].
    (*unit*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD2.
    inverts SubD1.
  }
  1:{ (*union*)
    simpl in *.
    forwards* OR1: IHA1. simpl in *. lia.
    forwards* OR2: IHA2. simpl in *. lia.
    destruct OR1 as [OR11 | OR12];
    destruct OR2 as [OR21 | OR22]; eauto. 
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_sym in CST.
    apply costs_or in CST.
    destruct CST as [CST | CST]; apply costs_sym in CST.
    eapply cost_complete in CST; eauto.
    eapply cost_complete in CST; eauto.
  }
  1:{ (*and*)
    simpl in *.
    forwards* OR1: IHA1. simpl in *. lia.
    forwards* OR2: IHA2. simpl in *. lia.
    destruct OR1 as [OR11 | OR12];
    destruct OR2 as [OR21 | OR22].
    forwards* CST: IHn A1 A2. lia.
    destruct CST as [CST | NCST]; eauto.
    (*B is either UO or US*)
    forwards* USUO: UO_OR_US B.
    destruct USUO as [UOR | [C1 [C2 USP]]]; eauto.
    (*when B is US*)
    forwards* [RED1 RED2]: US_size_red USP.
    forwards* CST1: IHn (t_and A1 A2) C1. simpl. lia.
    forwards* CST2: IHn (t_and A1 A2) C2. simpl. lia.
    destruct CST1 as [CST1 | CST1];
    destruct CST2 as [CST2 | CST2]; eauto.
    right. unfold not. introv CST3.
    apply cost_sound in CST3.
    eapply costs_us in CST3; eauto.
    destruct CST3 as [CST3 | CST3];
    eapply cost_complete in CST3; eauto.
    (*contradictory goals*)
    1-4: right; unfold not; introv CST;
    apply cost_sound in CST;
    apply costs_sym in CST;
    apply costs_and in CST;
    destruct CST as [CST1 [CST2 CST3]].
    try solve [eapply cost_complete in CST3; eauto].
    try solve [apply costs_sym in CST2;
      eapply cost_complete in CST2; eauto].
    try solve [apply costs_sym in CST1;
      eapply cost_complete in CST1; eauto].
    try solve [apply costs_sym in CST1;
      eapply cost_complete in CST1; eauto].
  }
  1: { (*unit*)
    induction B; auto; simpl in *.
    (*unit*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD1. inverts SubD1.
    inverts SubD2.
    (*bot*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD2.
    inverts SubD2.
    (*arrow*)
    right. unfold not. introv CST.
    apply cost_sound in CST.
    destruct CST as [D [OrdD [SubD1 SubD2]]].
    inverts OrdD. inverts SubD2. inverts SubD1.
    inverts SubD2.
    (*union*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_or in CST.
    destruct CST.
    eapply cost_complete in H1; eauto.
    eapply cost_complete in H1; eauto.
    (*and*)
    simpl in *.
    destruct IHB1; destruct IHB2; try solve [lia]; eauto.
    forwards*: IHn B1 B2. lia.
    destruct H1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST3; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST2; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
    right. unfold not. introv CST.
    apply cost_sound in CST.
    apply costs_and in CST.
    destruct CST as [CST1 [CST2 CST3]].
    eapply cost_complete in CST1; eauto.
  }
Qed.

(********************************)
(*** Disjointness Equivalence ***)
(********************************)

Definition disjSpec A B := forall C, Ord C -> not ((sub C A) /\ (sub C B)).

Lemma disj_sound : forall A B, disjSpec A B -> not (COSTS A B).
Proof.
    introv DSpec. unfold disjSpec in DSpec.
    unfold not in DSpec.
    unfold COSTS. unfold not.
    introv CST.
    destruct CST as [D [Ord [Sub1 Sub2]]].
    specialize (DSpec D Ord).
    apply* DSpec.
Qed.

Lemma disj_complete : forall A B, not (COSTS A B) -> disjSpec A B.
Proof.
    introv CST. unfold COSTS in CST.
    unfold not in CST.
    unfold disjSpec. unfold not.
    introv DSpec [Sub1 Sub2].
    apply* CST.
Qed.