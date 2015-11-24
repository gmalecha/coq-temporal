Require Import Coq.Classes.RelationClasses.
Require Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.
  Variable ST_eq : ST -> ST -> Prop.

  (* A trace is an infinite stream of states.
   *)
  CoInductive trace : Type :=
  | Continue : ST -> trace -> trace.

  Definition hd (tr : trace) : ST :=
    match tr with
    | Continue hd _ => hd
    end.

  Definition tl (tr : trace) : trace :=
    match tr with
    | Continue _ tl => tl
    end.

  CoInductive trace_eq : trace -> trace -> Prop :=
  | Discr_eq : forall a b,
      ST_eq (hd a) (hd b) ->
      trace_eq (tl a) (tl b) ->
      trace_eq a b.

  Inductive skips_to (s : trace) : trace -> Prop :=
  | Now : skips_to s s
  | Later : forall t, skips_to s (tl t) -> skips_to s t.

  Lemma skips_to_next
  : forall s s',
      skips_to s s' ->
      skips_to (tl s) s'.
  Proof.
    induction 1.
    { apply Later. apply Now. }
    { apply Later. assumption. }
  Qed.

  Global Instance Transitive_skips_to : Transitive skips_to.
  Proof.
    red.
    intros x y z H.
    induction H using skips_to_ind; eauto using skips_to_next.
  Qed.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. eapply Now.
  Qed.

End with_state.

(* Functorial *)
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Section functorial.
  Context {state1 state2 : Type}.
  Variable morphism : state2 -> state1.

  CoFixpoint fmap_trace (tr : @trace state2)
  : @trace state1 :=
    match tr with
    | Continue s c => Continue (morphism s) (fmap_trace c)
    end.
End functorial.

Theorem fmap_continue_compose : forall A B C (f : B -> C) (g : A -> B) (tr : trace _),
    trace_eq eq(fmap_trace f (fmap_trace g tr)) (fmap_trace (fun x => f (g x)) tr).
Proof.
  intros A B C f g.
  cofix cih.
  intros.
  constructor.
  - destruct tr; reflexivity.
  - destruct tr. simpl. eapply cih.
Qed.

Instance Functor_trace : Functor trace :=
{ fmap := fun _ _ mor tr =>
            match tr with
            | Continue st c => Continue (mor st) (fmap_trace mor c)
            end
}.

CoFixpoint forever {T} (v : T) : trace T :=
  Continue v (forever v).

CoFixpoint trace_ap {T U : Type} (f : trace (T -> U)) (x : trace T) : trace U :=
  Continue ((hd f) (hd x)) (trace_ap (tl f) (tl x)).

Instance Applicative_trace : Applicative trace :=
{ pure := @forever
; ap := @trace_ap
}.

Definition trace_zip {T U V : Type} (f : T -> U -> V) (a : trace T) (b : trace U) : trace V :=
  ap (ap (pure f) a) b.

Arguments skips_to {ST} _ _.
Arguments hd {ST} _.
Arguments tl {ST} _.
Arguments Transitive_skips_to {ST} _ _ _ _ _.
Arguments Reflexive_skips_to {ST} _.
