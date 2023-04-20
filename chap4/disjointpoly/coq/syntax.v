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

(** syntax *)

Inductive typ : Set :=  (*r type *)
 | t_top : typ
 | t_int : typ
 | t_bot : typ
 | t_arrow : typ -> typ -> typ
 | t_union : typ -> typ -> typ
 | t_and : typ -> typ -> typ
 | t_unit : typ
 | t_bvar  : nat -> typ
 | t_fvar  : var -> typ
 | t_all   : typ -> typ -> typ
 | t_prim  : nat -> typ.

Inductive exp : Set :=  (*r expression *)
 | e_bvar  : nat -> exp
 | e_fvar  : var -> exp
 | e_lit    : nat -> exp
 | e_abs    : exp -> exp
 | e_app    : exp -> exp -> exp
 | e_typeof : exp -> typ -> exp -> typ -> exp -> exp
 | e_null   : exp
 | e_tabs   : typ -> exp -> exp
 | e_tapp   : exp -> typ -> exp
 | e_new    : nat -> exp.


(** Opening up a type binder occuring in a type *)

Fixpoint open_tt_rec (K : nat) (U : typ) (T : typ) {struct T} : typ :=
  match T with
  | t_top         => t_top
  | t_int         => t_int
  | t_bot         => t_bot
  | t_arrow T1 T2 => t_arrow (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_union T1 T2 => t_union (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_and T1 T2   => t_and (open_tt_rec K U T1) (open_tt_rec K U T2)
  | t_unit        => t_unit
  | t_bvar J      => If K = J then U else (t_bvar J)
  | t_fvar X      => t_fvar X
  | t_all T1 T2   => t_all (open_tt_rec K U T1) (open_tt_rec (S K) U T2)
  | t_prim i      => t_prim i
  end.

Definition open_tt T U := open_tt_rec 0 U T.

(** Opening up a type binder occuring in a term *)

Fixpoint open_te_rec (K : nat) (U : typ) (e : exp) {struct e} : exp :=
  match e with
  | e_bvar i    => e_bvar i
  | e_fvar x    => e_fvar x
  | e_lit i     => e_lit i
  | e_abs e1    => e_abs (open_te_rec K U e1)
  | e_app e1 e2 => e_app  (open_te_rec K U e1) (open_te_rec K U e2)
  | e_typeof e1 T1 e2 T2 e3 => e_typeof (open_te_rec K U e1) (open_tt_rec K U T1) (open_te_rec K U e2) (open_tt_rec K U T2) (open_te_rec K U e3)
  | e_null      => e_null
  | e_tabs V e1 => e_tabs (open_tt_rec K U V)  (open_te_rec (S K) U e1)
  | e_tapp e1 V => e_tapp (open_te_rec K U e1) (open_tt_rec K U V)
  | e_new i     => e_new i
  end.

Definition open_te t U := open_te_rec 0 U t.

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
  | e_tabs A e => e_tabs A (open_ee_rec k e_5 e)
  | e_tapp e A => e_tapp (open_ee_rec k e_5 e) A
  | e_new i    => e_new i
end.

Definition open_ee t u := open_ee_rec 0 u t.

(** Notation for opening up binders with type or term variables *)

Notation "T 'open_tt_var' X" := (open_tt T (t_fvar X)) (at level 67).
Notation "t 'open_te_var' X" := (open_te t (t_fvar X)) (at level 67).
Notation "t 'open_ee_var' x" := (open_ee t (e_fvar x)) (at level 67).

(** Types as locally closed pre-types *)

Inductive type : typ -> Prop :=
  | type_top :
      type t_top
  | type_int :
      type t_int
  | type_bot :
      type t_bot
  | type_arrow : forall T1 T2,
      type T1 -> 
      type T2 -> 
      type (t_arrow T1 T2)
  | type_union : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_union T1 T2)
  | type_and : forall T1 T2,
      type T1 ->
      type T2 ->
      type (t_and T1 T2)
  | type_var : forall X,
      type (t_fvar X)
  | type_all : forall L T1 T2,
      type T1 ->
      (forall X, X \notin L -> type (T2 open_tt_var X)) ->
      type (t_all T1 T2)
  | type_unit : type t_unit
  | type_prim : forall i, 
      type (t_prim i).

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
     type A ->
     type B ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e1 (e_fvar x)) ) ->
     ( forall x , x \notin  L -> lc_exp ( open_ee e2 (e_fvar x)) ) ->
     lc_exp (e_typeof e A e1 B e2)
 | lec_e_null :
     lc_exp e_null
 | lc_e_tabs : forall L V e1,
      type V ->
      (forall X, X \notin L -> lc_exp (e1 open_te_var X)) ->
      lc_exp (e_tabs V e1)
 | lc_e_tapp : forall e1 V,
      lc_exp e1 ->
      type V ->
      lc_exp (e_tapp e1 V)
 | lc_e_new : forall i,
       lc_exp (e_new i).

(** Binding are mapping to term variables.
 [x ~: T] is a typing assumption *)

 Inductive bind : Set :=
 | bind_disj : typ -> bind
 | bind_typ  : typ -> bind.

Notation "X ~*: T" := (X ~ bind_disj T)
 (at level 23, left associativity) : env_scope.

Notation "x ~: T" := (x ~ bind_typ T)
(at level 23, left associativity) : env_scope.

(** Environment is an associative list of bindings. **)

Definition env := LibEnv.env bind.

(***************************
 *** Equality for types ****
 ***************************)

Lemma eq_dec_nat : forall (n1 n2 : nat), {n1 = n2} + {n1 <> n2}.
Proof.
  decide equality.
Defined.

Lemma eq_dec_var : forall (x y : var), {x = y} + {x <> y}.
Proof.
  intros.
  case_if_eq x y; auto.
Defined.

Lemma eq_dec : forall (x y:typ), {x = y} + {x <> y}.
Proof.
 decide equality; auto.
 apply eq_dec_nat.
 apply eq_dec_var.
 apply eq_dec_nat.
Defined.

Notation "l1 `union` l2" := (set_union eq_dec l1 l2) (at level 80).
Notation "l1 `inter` l2" := (set_inter eq_dec_nat l1 l2) (at level 80).
Notation "l1 `dif` l2" := (set_diff eq_dec l1 l2) (at level 80).

(*******************************)
(*** Environment for P types ***)
(*******************************)


Definition envp := list (nat * typ).

(* Definition PG : envp. *)

Definition domain_envp (l : envp) : list nat := map fst l.

Definition range_envp (l : envp) : list typ := map snd l.

Require Import FunInd.

(*
issupertype returns true if A <: B
and false otherwise

It works for the transitive closure
It works for supertypes having multiple unrelated subtypes
*)

Function issupertype (l: envp) (A:typ) (B:typ) {struct l} : bool :=
    match l with
    | [] => false
    | (i, t) :: xs => match eq_dec A (t_prim i) with
                     | left _ => match eq_dec B t with
                                 | left _ => true
                                 | right _ => issupertype xs t B
                                 end
                     | right _ => issupertype xs A B
                    end
    end.

Function get_all_subtypes (l : envp) (A: typ) {struct l} : list nat :=
  match l with
  | [] => []
  | (i, t) :: xs => let flag := (issupertype l (t_prim i) A) in
                    match flag with
                      | true  => i :: (get_all_subtypes xs A)
                      | false => get_all_subtypes xs A
                      end
  end.

(* Eval compute in (issupertype [(3, (t_prim 2)); (2, (t_prim 1))]) (t_prim 1) (t_prim 2). *)

Fixpoint nats_to_types (l : list nat) {struct l} : (list typ) :=
  match l with
  | [] => []
  | a :: xs => [t_prim a] ++ (nats_to_types xs)
  end.


 (** Well-formedness of a pre-type T in an environment E:
  all the type variables of T must be bound via a
  disjointness relation in E. This predicates implies
  that T is a type *)

Inductive wft (PG:envp) : env -> typ -> Prop :=
  | wft_top : forall E, 
      wft PG E t_top
  | wft_int : forall E,
      wft PG E t_int
  | wft_bot : forall E,
      wft PG E t_bot
  | wft_arrow : forall E T1 T2,
      wft PG E T1 -> 
      wft PG E T2 -> 
      wft PG E (t_arrow T1 T2)
  | wft_union : forall E T1 T2,
      wft PG E T1 ->
      wft PG E T2 ->
      wft PG E (t_union T1 T2)
  | wft_and : forall E T1 T2,
      wft PG E T1 ->
      wft PG E T2 ->
      wft PG E (t_and T1 T2)
  | wft_var : forall U E X,
      (* groundtype U -> *)
      binds X (bind_disj U) E ->
      wft PG E (t_fvar X) 
  | wft_all : forall L E T1 T2,
      wft PG E T1 ->
      (* groundtype T1 -> *)
      (forall X, X \notin L -> 
        wft PG (E & X ~*: T1) (T2 open_tt_var X)) ->
      wft PG E (t_all T1 T2)
  | wft_unit : forall E,
      wft PG E t_unit
  | wft_prim : forall (i : nat) E,
      set_In i (domain_envp PG) ->
      wft PG E (t_prim i).
  
  (** A environment E is well-formed if it contains no duplicate bindings
    and if each type in it is well-formed with respect to the environment
    it is pushed on to. *)

Inductive okenvp : envp -> Prop :=
  | okenvp_empty :
      okenvp []
  | okenvp_sub : forall (PG:envp) (A:typ) (i:nat) E,
     okenvp PG ->
     wft PG E A ->
     ~( set_In i (domain_envp PG)) ->
     okenvp ((i, A) :: PG).
  
Inductive okt (PG : envp) : env -> Prop :=
  | okt_empty :
      okt PG empty
  | okt_typ : forall E x T,
      okt PG E ->
      wft PG E T -> 
      x # E -> 
      okt PG (E & x ~: T)
  | okt_disj : forall E X T,
      okt PG E ->
      wft PG E T ->
      X # E -> 
      (* groundtype T -> *)
      okt PG (E & X ~*: T).

#[export]
Hint Constructors type wft okenvp : core.

(*************************)
(***** Ordinary Types ****)
(*************************)

Inductive Ord : typ -> Prop :=
  | o_int   : Ord t_int
  | o_arrow : forall t1 t2, Ord (t_arrow t1 t2)
  | o_unit  : Ord t_unit
  | o_all   : forall t1 t2, Ord (t_all t1 t2)
  | o_prim  : forall i, Ord (t_prim i).

#[export]
Hint Constructors Ord : core.


(* defns Subtyping *)
Reserved Notation "PG ; G |= A <: B" (at level 80, A at next level, B at next level).
Inductive sub (PG: envp) : env -> typ -> typ -> Prop :=    (* defn subtyping *)
 | s_top : forall G A,
     okenvp PG ->
     okt PG G ->
     wft PG G A ->
     sub PG G A t_top
 | s_int : forall G,
     okenvp PG ->
     okt PG G ->
     sub PG G t_int t_int
 | s_unit : forall G,
    okenvp PG ->
    okt PG G ->
    sub PG G t_unit t_unit
 | s_arrow : forall G (A1 A2 B1 B2:typ),
     sub PG G B1 A1 ->
     sub PG G A2 B2 ->
     sub PG G (t_arrow A1 A2) (t_arrow B1 B2)
 | s_ora : forall G (A1 A2 A:typ),
     sub PG G A1 A ->
     sub PG G A2 A ->
     sub PG G (t_union A1 A2) A
 | s_orb : forall G (A A1 A2:typ),
     wft PG G A2 ->
     sub PG G A A1 ->
     sub PG G A (t_union A1 A2)
 | s_orc : forall G (A A1 A2:typ),
     wft PG G A1 ->
     sub PG G A A2 ->
     sub PG G A (t_union A1 A2)
 | s_anda : forall G A A1 A2,
     sub PG G A A1 ->
     sub PG G A A2 ->
     sub PG G A (t_and A1 A2)
 | s_andb : forall G A1 A2 A,
     wft PG G A2 ->
     sub PG G A1 A ->
     sub PG G (t_and A1 A2) A
 | s_andc : forall G A1 A2 A,
     wft PG G A1 ->
     sub PG G A2 A ->
     sub PG G (t_and A1 A2) A
 | s_bot : forall G A,
      okenvp PG ->
      okt PG G ->
      wft PG G A ->
      sub PG G t_bot A
 | s_tvar : forall G X,
     okenvp PG ->
     okt PG G ->
     wft PG G (t_fvar X) ->
     sub PG G (t_fvar X) (t_fvar X)
 | s_all : forall L G S1 S2 T1 T2,
      sub PG G S1 T1 ->
      (* groundtype S1 -> *)
      (forall X, X \notin L ->
          PG ; (G & X ~*: T1) |=  (S2 open_tt_var X) <: (T2 open_tt_var X)) ->
      PG ; G |= (t_all S1 S2) <: (t_all T1 T2)
 | s_p_refl : forall i E,
     okenvp PG ->
     okt PG E ->
     wft PG E (t_prim i) ->
     PG ; E |= (t_prim i) <: (t_prim i)
 | s_p_sub : forall n1 n2 E,
     okenvp PG ->
     okt PG E ->
     wft PG E (t_prim n1) -> 
     wft PG E (t_prim n2) ->
     set_In (t_prim n1) (nats_to_types (get_all_subtypes PG (t_prim n2))) ->
     PG ; E |= (t_prim n1) <: (t_prim n2)
where "PG ; G |= A <: B" := (sub PG G A B) : env_scope.


#[export]
Hint Constructors sub lc_exp ok okt : core.


(***********************************)
(****  FindSubtypes Properties  ****)
(***********************************)

Lemma list_empty_decide : forall (A : Type) (l : list A), (l = []) \/ (l <> []).
Proof.
  intros. induction l. auto.
  destruct IHl. right. 
  unfold not. intros. inversion H0.
  unfold not in *.
  right. intros.
  inversion H0.
Defined.

Lemma elem_append_in_list : forall (a : typ) (l : list typ), set_In a (a :: l).
Proof.
  intros. simpl. auto.
Defined.

Lemma elem_append_in_union1 : forall (a1 a2 : typ) (l1 l2 : list typ), 
set_In a1 (a1 :: l1 `union` a2 :: l2).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro1. auto.
Defined.

Lemma elem_append_in_union2 : forall (a1 : typ) (l1 : list typ), 
set_In a1 ([] `union` a1 :: l1).
Proof.
  intros.
  lets: elem_append_in_list a1 l1.
  apply set_union_intro2. auto.
Defined.

Lemma sub_or (PG:envp) : forall G A B C, PG ; G |= (t_union A B) <: C -> 
  PG ; G |= A <: C /\ PG ; G |= B <: C.
Proof.
intros; inductions H; try solve [split*].
inverts* H1.
specialize (IHsub A B).
forwards* : IHsub.
specialize (IHsub A B).
forwards* : IHsub.
specialize (IHsub1 A B).
specialize (IHsub2 A B).
forwards* : IHsub1.
Defined.

Lemma sub_and (PG:envp) : forall G A B C, PG ; G |= A <: (t_and B C) -> 
  PG ; G |= A <: B /\ PG ; G |= A <: C.
Proof.
intros; inductions H; try solve [split*].
specialize (IHsub1 B C).
specialize (IHsub2 B C).
forwards* : IHsub1.
specialize (IHsub B C).
forwards* : IHsub.
specialize (IHsub B C).
forwards* : IHsub.
inverts* H1.
Defined.

(*  
  Nominal Type Properties
*)

Lemma prim_type_in_nats_to_types : forall (A : typ) (l : list nat), 
  set_In A (nats_to_types l) ->
  exists (i : nat), A = t_prim i.
Proof.
  induction l; intros. simpl in H. inverts H.
  simpl in H. destruct H. exists a. auto. auto.
Defined.

Lemma prim_in_domain : forall PG (j:nat),
  set_In j (domain_envp PG) ->
  exists (i:nat), t_prim j = t_prim i.
Proof.
  intros PG j IN. exists*.
Qed.

Lemma i_in_nat_to_types : forall i PG,
  set_In i (domain_envp PG) ->
  set_In (t_prim i) (nats_to_types (domain_envp PG)).
Proof.
  introv IN.
  induction (domain_envp PG). inverts IN.
  simpl in IN. destruct IN.
  simpl. left. subst~.
  simpl. right. apply* IHl.
Qed.

Lemma prim_in_nat_to_types : forall i PG,
  set_In (t_prim i) (nats_to_types (domain_envp PG)) ->
  set_In i (domain_envp PG).
Proof.
  introv IN.
  induction (domain_envp PG). inverts IN.
  simpl in IN. destruct IN. inverts H.
  simpl. left. subst~.
  simpl. right. apply* IHl.
Qed.

Lemma allsubtypes_in_to_domain_nat : forall PG A,
  forall i, set_In i (get_all_subtypes PG A) ->
  set_In i (domain_envp PG).
Proof.
  induction PG; introv IN1.
  - inverts IN1.
  - destruct a as [C D].
    simpl in *. destruct (eq_dec_nat C C).
    destruct (eq_dec A D).
    + simpl in IN1.
      destruct IN1.
      * auto.
      * specialize (IHPG A i).
        forwards: IHPG H.
        auto.
    + simpl in IN1.
      destruct (issupertype PG D A).
      simpl in IN1. destruct IN1.
      auto.
      apply IHPG in H; auto.
      apply IHPG in IN1; auto.
    + contradiction.
Qed.

Lemma nat_to_types_iff : forall l1 l2,
  (nats_to_types (l1 ++ l2)) = (nats_to_types l1) ++ (nats_to_types l2).
Proof.
  induction l1; intros. 
  - simpl. auto.
  - simpl. specialize (IHl1 l2).
    rewrite IHl1. auto.
Qed.

Lemma allsubtypes_in_to_domain : forall PG A,
  forall B, set_In B (nats_to_types (get_all_subtypes PG A)) ->
  set_In B (nats_to_types (domain_envp PG)).
Proof.
  induction PG; introv IN1.
  - inverts IN1.
  - simpl in *. destruct a as [C D].
    destruct (eq_dec_nat C C).
    destruct (eq_dec A D); simpl in IN1.
    + destruct IN1.
      * rewrite <- H. simpl. auto.
      * apply IHPG in H. auto.
    + destruct (issupertype PG D A).
      * simpl in IN1. destruct IN1.
        simpl. auto.
        apply IHPG in H. auto.
      * apply IHPG in IN1. auto.
    + contradiction. 
Qed.

Lemma bot_sub_all : forall PG G A,
  okenvp PG ->
  okt PG G ->
  wft PG G A -> 
  PG ; G |= t_bot <: A.
Proof.
  intros.
  dependent induction A; eauto.
Qed.

(****************************************)
(**********  Dijoint Algo    ************)
(****************************************)

(* splittable types *)

(* Union ordinary types *)

Inductive UO : typ -> Prop :=
  | uo_int   : UO t_int
  | uo_arrow : forall t1 t2, UO (t_arrow t1 t2)
  | uo_unit  : UO t_unit
  | uo_and   : forall t1 t2, UO t1 -> UO t2 -> UO (t_and t1 t2)
  | uo_top   : UO t_top
  | uo_bot   : UO t_bot
  | uo_all   : forall t1 t2, UO (t_all t1 t2)
  | uo_fvar  : forall X, UO (t_fvar X)
  | uo_prim  : forall i, UO (t_prim i).
  (*
  Type varibale cannot be UO.
  Otherwise it breaks disj_subst.

  disj_subst requires to UO to be UO after subst.
  If we type variable in UO, then this property breaks.
  *)

#[export]
Hint Constructors UO : core.
  
  (* splittable types *)
  
  Inductive US : typ -> typ -> typ -> Prop :=
    | us_or : forall A B,
        US (t_union A B) A B
    | us_and1 : forall A A1 A2 B,
        US A A1 A2 ->
        US (t_and A B) (t_and A1 B) (t_and A2 B)
     | us_and2 : forall A B B1 B2,
        (* UO A -> *)
        US B B1 B2 ->
        US (t_and A B) (t_and A B1) (t_and A B2).
  
  #[export]
  Hint Constructors US : core.

(* Disjointness *)

Inductive Disj (PG:envp) (E:env) : typ -> typ -> Prop :=
  | disj_botl : forall A,
      okenvp PG ->
      okt PG E ->
      wft PG E A ->
      Disj PG E t_bot A
  | disj_botr : forall A,
      okenvp PG ->
      okt PG E ->
      wft PG E A ->
      Disj PG E A t_bot
  | disj_int_arrl : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_arrow A B) ->
      Disj PG E t_int (t_arrow A B)
  | disj_int_arrr : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_arrow A B) ->
      Disj PG E (t_arrow A B) t_int
  | disj_null_arrl : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_arrow A B) ->
      Disj PG E t_unit (t_arrow A B)
  | disj_null_arrr : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_arrow A B) ->
      Disj PG E (t_arrow A B) t_unit
  | disj_int_nulll :
      okenvp PG ->
      okt PG E ->
      Disj PG E t_int t_unit
  | disj_int_nullr :
      okenvp PG ->
      okt PG E ->
      Disj PG E t_unit t_int
  | disj_or1 : forall A B A1 A2,
      wft PG E A ->
      US A A1 A2 ->
      Disj PG E A1 B ->
      Disj PG E A2 B ->
      Disj PG E A B
  | disj_or2 : forall A B B1 B2,
      wft PG E B ->
      US B B1 B2 ->
      Disj PG E A B1 ->
      Disj PG E A B2 ->
      Disj PG E A B
  | disj_and1 : forall B A1 A2,
      wft PG E A2 ->
      (* UO B -> *)
      Disj PG E A1 B ->
      Disj PG E (t_and A1 A2) B
  | disj_and2 : forall B A1 A2,
      wft PG E A1 ->
      (* UO B -> *)
      Disj PG E A2 B ->
      Disj PG E (t_and A1 A2) B
  | disj_and3 : forall A B1 B2,
      wft PG E B2 ->
      (* UO A -> *)
      Disj PG E A B1 ->
      Disj PG E A (t_and B1 B2)
  | disj_and4 : forall A B1 B2,
      wft PG E B1 -> 
      (* UO A -> *)
      Disj PG E A B2 ->
      Disj PG E A (t_and B1 B2)
  (* | disj_and5 : forall A B C,
      wft E C ->
      Disj E A B ->
      Disj E (t_and A B) C
  | disj_and6 : forall A B C,
      wft E A ->
      Disj E B C ->
      Disj E A (t_and B C) *)
  | disj_all_intl : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_all A B) ->
      Disj PG E (t_all A B) t_int
  | disj_all_intr : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_all A B) ->
      Disj PG E t_int (t_all A B)
  | disj_all_arrl : forall A1 B1 A2 B2,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_all A1 B1) ->
      wft PG E (t_arrow A2 B2) ->
      Disj PG E (t_all A1 B1) (t_arrow A2 B2)
  | disj_all_arrr : forall A1 B1 A2 B2,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_arrow A1 B1) ->
      wft PG E (t_all A2 B2) ->
      Disj PG E (t_arrow A1 B1) (t_all A2 B2)
  | disj_all_nulll : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_all A B) ->
      Disj PG E (t_all A B) t_unit
  | disj_all_nullr : forall A B,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_all A B) ->
      Disj PG E t_unit (t_all A B)
 | disj_fvarl : forall X T,
      binds X (bind_disj T) E ->
      forall A,
      sub PG E A T ->
      Disj PG E (t_fvar X) A
  | disj_fvarr : forall X T,
      binds X (bind_disj T) E ->
      forall A,
      sub PG E A T ->
      Disj PG E A (t_fvar X)
  | disj_prim : forall i j,
      okenvp PG ->
      okt PG E ->
      wft PG E (t_prim i) ->
      wft PG E (t_prim j) ->
      set_inter eq_dec_nat (i::(get_all_subtypes PG (t_prim i))) (j::(get_all_subtypes PG (t_prim j))) = nil ->
      Disj PG E (t_prim i) (t_prim j).

#[export]
Hint Constructors Disj : core.

(* Eval simpl in (get_all_subtypes [(1, t_top)] (t_prim 1)). *)

Definition PG1 : envp := (1, t_top)::(2, t_top)::nil.


Notation "PG ; E |= A *a B" := (Disj PG E A B) (at level 80, E at next level, A at next level).

Fixpoint t_size (A:typ) : nat :=
  match A with
  | t_top => 1
  | t_int => 1
  | t_bot => 1
  | t_unit => 1
  | t_arrow t1 t2 => 1 + (t_size t1) + (t_size t2)
  | t_union t1 t2 => 1 + (t_size t1) + (t_size t2)
  | t_and t1 t2 => 1 + (t_size t1) + (t_size t2)
  | t_all t1 t2 => 1 + (t_size t1) + (t_size t2)
  | t_prim i    => 1
  | t_fvar X    => 1
  | t_bvar i     => 1
  end.

Lemma not_empty_in_exist : forall (A : Type) (l : list A),
 l <> [] ->
 exists A, set_In A l.
Proof.
  intros. destruct l. contradiction.
  exists a. simpl. auto.
Defined.

(* lemma for section 5.4 *)

Lemma test : forall l1 l2 l3,
(l1 `inter` l2) = [] ->
((l1 `inter` l2) `inter` l3) = [].
Proof.
  intros.
  rewrite H. simpl. auto.
Qed.

Lemma inter_empty : forall l,
  (l `inter` []) = [].
Proof.
  induction l.
  simpl. auto.
  simpl in *. rewrite~ IHl.
Qed.


Lemma and_disj_either : forall PG E A B C, 
  wft PG E (t_and A B) ->
  (PG; E |= A *a C) \/ (PG; E |= B *a C) -> (PG; E |= (t_and A B) *a C).
Proof.
  introv WFAB Disj.
  destruct Disj as [Disj | Disj].
  apply disj_and1 with (A1:=A) (A2:=B); eauto.
  inverts* WFAB.
  apply disj_and2 with (A1:=A) (A2:=B); eauto.
  inverts* WFAB.
Qed.