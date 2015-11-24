Require Import Coq.Classes.RelationClasses.
Require Coq.Lists.List.

Set Implicit Arguments.
Set Strict Implict.

Section with_state.

  Variable ST : Type.

  Definition time : Type := nat.
  Definition time_now : time := 0.

  (* A behavior is an infinite stream of states.
   *)
  CoInductive continue (from : ST) :=
  | Discr : forall s : ST, continue s -> continue from.

  Definition as_discr s (c : continue s) : option { s' : _ & continue s' } :=
    match c with
      | @Discr _ x y => Some (@existT _ _ x y)
    end.

  CoInductive continue_eq (from : ST) : continue from -> continue from -> Prop :=
  | Discr_eq : forall a b d,
      @continue_eq _ b d ->
      @continue_eq from (@Discr _ a b) (@Discr _ a d).

  Inductive trace :=
  | Trace : forall start : ST, continue start -> trace.

  Inductive trace_eq : trace -> trace -> Prop :=
  | Trace_eq : forall s c1 c2,
      @continue_eq s c1 c2 ->
      trace_eq (Trace c1) (Trace c2).

  Inductive Step :=
  | DiscreteTo : ST -> Step.

  (* The head of a trace *)
  Definition hd (s:trace) : ST :=
    match s with
    | @Trace now _ => now
    end.

  Definition traceK (s : trace) : continue (hd s) :=
    match s as s return continue (hd s) with
    | @Trace _ x => x
    end.

  Definition tl (t : trace) : trace :=
    match traceK t with
    | @Discr _ x s => Trace s
    end.

  Inductive after_time : time -> trace -> trace -> Prop :=
  | Now     : forall s, after_time time_now s s
  | WithinD : forall n st st' (s : continue st') s',
      after_time n (Trace s) s' ->
      after_time (S n) (@Trace st (@Discr st st' s)) s'.

  Lemma after_time_now : forall s s',
      after_time 0 s s' ->
      s = s'.
  Proof.
    inversion 1; auto.
  Qed.

  Definition skips_to (a b : trace) : Prop :=
    exists t : time, after_time t a b.

  Theorem skips_to_ind
  : forall P : trace -> trace -> Prop,
       (forall s : trace, P s s) ->
       (forall (st st' : ST) (s : continue st') (s' : trace),
        skips_to (Trace s) s' -> P (Trace s) s' -> P (Trace (Discr st s)) s') ->
       forall t t0 : trace, skips_to t t0 -> P t t0.
  Proof.
    unfold skips_to. intros. destruct H1.
    induction H1; eauto.
  Qed.

  Lemma skips_to_next
  : forall st st' (s : continue st') s',
      skips_to (Trace s) s' ->
      skips_to (@Trace st (@Discr st st' s)) s'.
  Proof.
    intros. destruct H.
    exists (S x).
    constructor. eauto.
  Qed.

  Definition firstStep (s : trace)
  : Step :=
    match traceK s with
    | @Discr _ x k => DiscreteTo x
    end.

  Global Instance Transitive_skips_to : Transitive skips_to.
  Proof.
    red.
    intros x y z H.
    induction H using skips_to_ind; eauto using skips_to_next.
  Qed.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. exists 0. constructor.
  Qed.

End with_state.

(* Functorial *)
Require Import ExtLib.Structures.Functor.

Section functorial.
  Context {state1 state2 : Type}.
  Variable morphism : state2 -> state1.

  CoFixpoint fmap_continue x (tr : @continue state2 x)
  : @continue state1 (morphism x) :=
    match tr in @continue _ _ return @continue state1 (morphism x) with
    | @Discr _ _ s c => @Discr _ (morphism x) (morphism s) (fmap_continue c)
    end.
End functorial.

Theorem fmap_continue_compose : forall A B C (f : B -> C) (g : A -> B) x (tr : continue x),
    continue_eq (fmap_continue f (fmap_continue g tr)) (fmap_continue (fun x => f (g x)) tr).
Proof.
  intros A B C f g.
  cofix cih.
  intros.
Admitted.

Instance Functor_trace : Functor trace :=
{ fmap := fun _ _ mor tr =>
            match tr with
            | @Trace _ st c => @Trace _ (mor st) (fmap_continue mor c)
            end
}.

Arguments after_time {ST} _ _ _.
Arguments skips_to {ST} _ _.
Arguments hd {ST} _.
Arguments tl {ST} _.
Arguments firstStep {ST} _.
Arguments Transitive_skips_to {ST} _ _ _ _ _.
Arguments Reflexive_skips_to {ST} _.
