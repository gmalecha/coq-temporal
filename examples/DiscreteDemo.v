Require Import ExtLib.Structures.Applicative.
Require Import Temporal.DiscreteLogic.
Require Import ChargeCore.Tactics.Tactics.

Set Implicit Arguments.
Set Strict Implicit.

Definition lift1 {T U : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U) (x : F T) : F U :=
  Applicative.ap (Applicative.pure f) x.

Definition lift2 {T U V : Type} {F : Type -> Type}
           {Ap : Applicative.Applicative F}
(f : T -> U -> V) (x : F T) (y : F U) : F V :=
  Applicative.ap (lift1 (F:=F) f x) y.

(*
Class Arith (T : Type) : Type :=
{ plus  : T -> T -> T
; minus : T -> T -> T
; mult  : T -> T -> T
}.

Instance Arith_nat : Arith nat :=
{ plus := Nat.add
; minus := Nat.sub
; mult := Nat.mul
}.

Instance Arith_lift {T U} {A : Arith T} : Arith (U -> T) :=
{ plus := fun a b x => plus (a x) (b x)
; minus := fun a b x => minus (a x) (b x)
; mult := fun a b x => mult (a x) (b x)
}.
*)

Record State : Type :=
{ x : nat }.

Definition Sys : TraceProp State :=
       now (lift2 eq x (pure 1))
  //\\ always (starts (lift2 eq (pre x) (post x))).

(** TODO: Move **)
Definition beforeProp (P : StateProp State) (Q : ActionProp State) : Prop :=
  before State P -|- Q.
Definition beforeVal {T} (P : StateVal State T) (Q : ActionVal State T)
: Prop :=
  forall st st', P st = Q st st'.
Theorem beforeProp_lift2 {T U} (f : T -> U -> Prop) x y x' y'
: beforeVal x x' -> beforeVal y y' ->
  beforeProp (lift2 f x y) (lift2 f x' y').
Proof.
  unfold beforeVal, beforeProp.
  simpl. intros.
  unfold before.
  split.
  Transparent ILInsts.ILFun_Ops.
  { do 3 red. simpl. destruct t0.
    rewrite <- H. rewrite <- H0. auto. }
  { do 3 red. simpl. destruct t0.
    rewrite <- H. rewrite <- H0. auto. }
Qed.

Theorem beforeVal_pre {T} (get : State -> T) :
  beforeVal get (pre get).
Proof. red. reflexivity. Qed.

Theorem beforeVal_pure {T} (x : T) :
  beforeVal (pure x) (pure x).
Proof. red. reflexivity. Qed.

Require Import Coq.Classes.Morphisms.

Notation "[] e" := (always e) (at level 30).

Goal |-- Sys -->> [] (now (lift2 eq x (pure 1))).
Proof.
  unfold Sys.
  charge_intros.
  eapply hybrid_induction.
  { charge_assumption. }
  { charge_assumption. }
  { apply always_tauto.
    rewrite <- curry.
    rewrite now_starts_discretely_and.
    rewrite next_now.
    rewrite starts_impl.
    eapply starts_tauto.
    unfold before, after, pre, post. simpl.
    destruct 2; congruence. }
Qed.
