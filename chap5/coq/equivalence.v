(*

-> Soundness of our system with Dunfield's system
-> no disjointness and no determinism
-> Dunfield's system with cleanup
-> Fix point operator
-> With switch expression

*)

Require Import Metalib.Metatheory.
Require Import LibTactics.

Require Import syntax.
Require Import typing.


(******************************)
(*** Dunfield System ***)
(******************************)


Inductive dexp : Set :=  (*dunfield expression *)
 | de_var_b  : nat -> dexp
 | de_var_f  : var -> dexp
 | de_lit    : nat -> dexp
 | de_abs    : dexp -> dexp
 | de_app    : dexp -> dexp -> dexp
 | de_merg   : dexp -> dexp -> dexp
 | de_top    : dexp
 | de_fix    : dexp -> dexp.

Fixpoint dopen_exp_wrt_exp_rec (k:nat) (e_5:dexp) (e__6:dexp) {struct e__6}: dexp :=
  match e__6 with
  | (de_var_b nat)  => if (k == nat) then e_5 else (de_var_b nat)
  | (de_var_f x)    => de_var_f x
  | (de_lit i5)     => de_lit i5
  | (de_abs e)      => de_abs (dopen_exp_wrt_exp_rec (S k) e_5 e)
  | (de_app e1 e2)  => de_app (dopen_exp_wrt_exp_rec k e_5 e1) (dopen_exp_wrt_exp_rec k e_5 e2)
  | (de_merg e1 e2) => de_merg (dopen_exp_wrt_exp_rec k e_5 e1) (dopen_exp_wrt_exp_rec k e_5 e2)
  | (de_top)          => de_top
  | (de_fix e)      => de_fix (dopen_exp_wrt_exp_rec (S k) e_5 e)
end.

Definition dopen_exp_wrt_exp e_5 e__6 := dopen_exp_wrt_exp_rec 0 e__6 e_5.

(** Notation for opening up binders with type or term variables *)

Notation "t 'dopen_ee_var' x" := (dopen_exp_wrt_exp t (de_var_f x)) (at level 67).


(** terms are locally-closed pre-terms *)
(** definitions *)

(* defns LC_exp *)
Inductive dlc_exp : dexp -> Prop :=    (* defn lc_exp *)
 | dlc_e_var_f : forall (x:var),
     (dlc_exp (de_var_f x))
 | dlc_e_lit : forall i5,
     (dlc_exp (de_lit i5))
 | dlc_e_abs : forall (L:vars) (e:dexp),
      ( forall x , x \notin  L  -> dlc_exp  (dopen_exp_wrt_exp e (de_var_f x)))  ->
     (dlc_exp (de_abs e))
 | dlc_e_app : forall (e1 e2:dexp),
     (dlc_exp e1) ->
     (dlc_exp e2) ->
     (dlc_exp (de_app e1 e2))
 | dlc_e_merg : forall (e1:dexp) (e2:dexp),
     (dlc_exp e1) ->
     (dlc_exp e2) ->
     (dlc_exp (de_merg e1 e2))
 | dlc_e_top :
      dlc_exp de_top
 | dlc_fix : forall (L:vars) (e:dexp),
      (forall x , x \notin L -> dlc_exp (dopen_exp_wrt_exp e (de_var_f x)) )  ->
      dlc_exp (de_fix e).

#[export]
Hint Constructors dlc_exp : core.

(** free variables *)
Fixpoint dfv_exp (e_5:dexp) : vars :=
  match e_5 with
  | (de_var_b nat) => {}
  | (de_var_f x) => {{x}}
  | (de_lit i5) => {}
  | (de_abs e) => (dfv_exp e)
  | (de_app e1 e2) => (dfv_exp e1) \u (dfv_exp e2)
  | (de_merg e1 e2) => (dfv_exp e1) \u (dfv_exp e2)
  | (de_top)       => {}
  | (de_fix e) => dfv_exp e
end.

(** substitutions *)
Fixpoint dsubst_exp (e_5:dexp) (x5:var) (e__6:dexp) {struct e__6} : dexp :=
  match e__6 with
  | (de_var_b nat) => de_var_b nat
  | (de_var_f x) => (if x == x5 then e_5 else (de_var_f x))
  | (de_lit i5) => de_lit i5
  | (de_abs e) => de_abs (dsubst_exp e_5 x5 e)
  | (de_app e1 e2) => de_app (dsubst_exp e_5 x5 e1) (dsubst_exp e_5 x5 e2)
  | (de_merg e1 e2) => de_merg (dsubst_exp e_5 x5 e1) (dsubst_exp e_5 x5 e2)
  | (de_top)    => de_top
  | (de_fix e) => de_fix (dsubst_exp e_5 x5 e)
end.


Inductive dvalue : dexp -> Prop :=    (* defn pexpr *)
 | dval_var : forall x,
     dvalue (de_var_f x)
 | dval_int : forall i5,
     dvalue (de_lit i5)
 | dval_abs : forall (e:dexp) (A B:typ),
     dlc_exp (de_abs e) ->
     dvalue (de_abs e)
 | dval_top :
     dvalue de_top
 | dval_merg : forall v1 v2,
    dvalue v1 ->
    dvalue v2 ->
    dvalue (de_merg v1 v2).

#[export]
Hint Constructors dvalue : core.

(* Dunfield's semantics *)

(* defns Reduction *)
Inductive dstep : dexp -> dexp -> Prop :=    (* defn step *)
 | dstep_appl : forall (e1 e2 e1':dexp),
     dlc_exp e2 ->
     dstep e1 e1' ->
     dstep (de_app e1 e2) (de_app e1' e2)
 | dstep_appr : forall (v e e':dexp),
     dvalue v ->
     dstep e e' ->
     dstep (de_app v e) (de_app v e')
 | dstep_beta : forall (e:dexp) (A A1 B1 A2 B2:typ) v,
     dlc_exp (de_abs e) ->
     dvalue v ->
     dstep (de_app (de_abs e) v) (dopen_exp_wrt_exp e v)
 | dstep_mergl : forall (e1 e2 e1':dexp),
     dlc_exp e2 ->
     dstep e1 e1' ->
     dstep (de_merg e1 e2) (de_merg e1' e2)
 | dstep_mergr : forall (v e e':dexp),
     dvalue v ->
     dstep e e' ->
     dstep (de_merg v e)  (de_merg v e')
 | dstep_unmergl : forall (e1 e2:dexp),
     dlc_exp e1 ->
     dlc_exp e2 ->
     dstep (de_merg e1 e2)  e1
 | dstep_unmergr : forall (e1 e2:dexp),
     dlc_exp e1 ->
     dlc_exp e2 ->
     dstep (de_merg e1 e2)  e2
 | dstep_split : forall (e:dexp),
     dlc_exp e ->
     dstep e (de_merg e e).


(* Dunfield's type system and
   elaboration to our type system.
*)

Inductive dtyping : ctx -> dexp -> typ -> exp -> Prop :=
 | dtyp_lit : forall (G:ctx) i5,
      uniq G ->
      dtyping G (de_lit i5) t_int (e_lit i5)
 | dtyp_var : forall (G:ctx) (x:var) (A:typ),
      uniq  G  ->
      binds  x A G  ->
      dtyping G (de_var_f x) A (e_var_f x)
 | dtyp_merg1 : forall (G:ctx) (e1 e2:dexp) e3 (A:typ),
     dtyping G e1 A e3 ->
     dtyping G (de_merg e1 e2) A e3
 | dtyp_merg2 : forall (G:ctx) (e1 e2:dexp) e4 (A:typ),
     dtyping G e2 A e4 ->
     dtyping G (de_merg e1 e2) A e4
 | dtyp_abs : forall (L:vars) (G:ctx) (e:dexp) e' A B,
     (forall x , x \notin L -> dtyping ([(x, A)] ++ G) (dopen_exp_wrt_exp e (de_var_f x)) B (open_exp_wrt_exp e' (e_var_f x)))  ->
     dtyping G (de_abs e) (t_arrow A B) (e_abs e' A B)
 | dtyp_app : forall (G:ctx) (e1 e2:dexp) e3 e4 (B A:typ),
     dtyping G e1 (t_arrow A B) e3 ->
     dtyping G e2 A e4 ->
     dtyping G (de_app e1 e2) B (e_app e3 e4)
 | dtyp_and: forall G e A B e1 e2,
     dtyping G e A e1 ->
     dtyping G e B e2 ->
     dtyping G e (t_and A B) (e_merg e1 e2)
 | dtyp_andl: forall G e A B e',
     dtyping G e (t_and A B) e' ->
     dtyping G e A e'
 | dtyp_andr: forall G e A B e',
     dtyping G e (t_and A B) e' ->
     dtyping G e B e'
 | dtyp_orl : forall G e A B e',
     dtyping G e A e' ->
     dtyping G e (t_union A B) e'
 | dtyp_orr : forall G e A B e',
     dtyping G e B e' ->
     dtyping G e (t_union A B) e'
 | dtyp_sub : forall (G:ctx) (e:dexp) (A B:typ) e',
     dtyping G e B e' ->
     B <: A ->
     dtyping G e A e'
 | dtyp_top2: forall (G:ctx),
     uniq G ->
     dtyping G de_top t_top e_top
 | dtyp_fix : forall L e G A e',
     (forall x, x \notin L -> dtyping ([(x, A)] ++ G) (dopen_exp_wrt_exp e (de_var_f x)) A (open_exp_wrt_exp e' (e_var_f x))) ->
     dtyping G (de_fix e) A (e_fix e' A)
 | (*encoding switch expression in Dunfield's system*)
   dtyp_typeof : forall (L:vars) (G:ctx) (e:dexp) (A:typ) (e1:dexp) (B:typ) (e2:dexp) (C:typ) e' e1' e2',
     dtyping G e (t_union A B) e' ->
     (forall x , x \notin  L  -> dtyping ([(x, A)] ++ G) (dopen_exp_wrt_exp e1 (de_var_f x)) C (open_exp_wrt_exp e1' (e_var_f x))) ->
     (forall x , x \notin  L  -> dtyping ([(x, B)] ++ G) (dopen_exp_wrt_exp e2 (de_var_f x)) C (open_exp_wrt_exp e2' (e_var_f x))) ->
     dtyping G (de_app (de_merg (de_abs e1) (de_abs e2)) e) C (e_typeof e' A e1' B e2').

#[export]
Hint Constructors dtyping : core.

(* soundness w.r.t Dunfield's type system *)

Lemma dt_sound : forall G e1 e2 A,
    dtyping G e1 A e2 -> 
    typing G e2 A.
Proof.
    induction 1; intros; eauto.
Qed.

Lemma val_checks_top : forall G dv A e',
    dvalue dv ->
    dtyping G dv A e' ->
    dtyping G dv t_top e'.
Proof.
    induction 1; intros; eauto.
Qed.

Lemma val_checks_typ : forall G dv e',
    dtyping G dv t_top e' ->
    typing G e' t_top.
Proof.
    induction 1; intros; eauto.
Qed.