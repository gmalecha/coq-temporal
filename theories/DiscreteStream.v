Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
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

  Global Instance Proper_hd : Proper (trace_eq ==> ST_eq) hd.
  Proof. do 2 red. destruct 1; auto. Qed.

  Global Instance Proper_tl : Proper (trace_eq ==> trace_eq) tl.
  Proof. do 2 red. destruct 1; auto. Qed.

  Global Instance Reflexive_trace_eq {Refl_r : Reflexive ST_eq} : Reflexive trace_eq.
  Proof.
    red. cofix.
    constructor. reflexivity. eapply Reflexive_trace_eq.
  Qed.

  Global Instance Symmetric_trace_eq {Sym_r : Symmetric ST_eq} : Symmetric trace_eq.
  Proof.
    red. cofix.
    constructor.
    { destruct H. symmetry. eassumption. }
    { destruct H. eapply Symmetric_trace_eq. eassumption. }
  Qed.

  Global Instance Transitive_trace_eq {Trans_r : Transitive ST_eq} : Transitive trace_eq.
  Proof.
    red. cofix.
    constructor.
    { destruct H; destruct H0; etransitivity; eauto. }
    { destruct H; destruct H0. eapply Transitive_trace_eq; eauto. }
  Qed.

  Global Instance PreOrder_trace_eq (PO : PreOrder ST_eq)
  : PreOrder trace_eq.
  Proof.
    destruct PO.
    constructor.
    { eapply Reflexive_trace_eq. }
    { eapply Transitive_trace_eq. }
  Qed.

End with_state.

Section skips_to.
  Context {T : Type}.

  Inductive skips_to (s : trace T) : trace T -> Prop :=
  | Now : forall t, trace_eq eq s t -> skips_to s t
  | Later : forall t, skips_to s (tl t) -> skips_to s t.

  Lemma skips_to_next
  : forall s s',
      skips_to s s' ->
      skips_to (tl s) s'.
  Proof.
    induction 1.
    { apply Later. apply Now. eapply Proper_tl. assumption. }
    { apply Later. assumption. }
  Qed.

  Global Instance Proper_skips_to_impl
  : Proper (trace_eq eq ==> trace_eq eq ==> Basics.impl) skips_to.
  Proof.
    do 4 red.
    intros.
    generalize dependent y. generalize dependent y0.
    induction H1; intros.
    { eapply Now.
      etransitivity; try eassumption.
      etransitivity; try eassumption.
      symmetry; eauto. }
    { eapply Later.
      eapply IHskips_to; eauto.
      destruct H0; auto. }
  Qed.

  Global Instance Proper_skips_to_iff
  : Proper (trace_eq eq ==> trace_eq eq ==> iff) skips_to.
  Proof.
    do 4 red. split.
    - rewrite H. rewrite H0. tauto.
    - rewrite H. rewrite H0. tauto.
  Qed.

  Global Instance Transitive_skips_to : Transitive skips_to.
  Proof.
    red.
    intros x y z H.
    induction H using skips_to_ind; eauto using skips_to_next.
    rewrite H. auto.
  Qed.

  Global Instance Reflexive_skips_to : Reflexive skips_to.
  Proof.
    red. intros. eapply Now. reflexivity.
  Qed.
End skips_to.

(* Functorial *)
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Structures.Applicative.

Section functorial.
  Context {state1 state2 : Type}.
  Variable morphism : state1 -> state2.

  CoFixpoint fmap_trace (tr : @trace state1)
  : @trace state2 :=
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
{ fmap := @fmap_trace }.

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

Arguments skips_to {ST} _ _ : rename.
Arguments hd {ST} _.
Arguments tl {ST} _.
Arguments Transitive_skips_to {ST} _ _ _ _ _ : rename.
Arguments Reflexive_skips_to {ST} _ : rename.

Section extra_trace_properties.
  Context {T U V : Type} (Rt : T -> T -> Prop) (Ru : U -> U -> Prop) (Rv : V -> V -> Prop).

  CoFixpoint prefixes {T} (acc : list T) (tr : trace T) : trace (list T) :=
    match tr with
    | Continue t tr => Continue acc (prefixes (t :: acc) tr)
    end.

  Lemma trace_zip_snd : forall {T U} (a : trace T) (b : trace U),
      trace_eq eq (trace_zip (fun _ x => x) a b) b.
  Proof using.
    do 2 intro.
    cofix.
    destruct a; destruct b.
    constructor.
    - reflexivity.
    - simpl.  simpl. eapply trace_zip_snd.
  Qed.

  Lemma trace_zip_fst : forall {T U} (a : trace T) (b : trace U),
      trace_eq eq (trace_zip (fun x _ => x) a b) a.
  Proof using.
    do 2 intro.
    cofix.
    destruct a; destruct b.
    constructor.
    - reflexivity.
    - simpl.  simpl. eapply trace_zip_fst.
  Qed.

  Lemma trace_eq_equiv : forall (a b c d : trace T),
      trace_eq Rt b c ->
      trace_eq eq a b ->
      trace_eq eq c d ->
      trace_eq Rt a d.
  Proof.
    cofix.
    intros.
    destruct H; destruct H0; destruct H1.
    constructor.
    { rewrite H0. rewrite <- H1. assumption. }
    { eapply trace_eq_equiv; eassumption. }
  Qed.

  Global Instance Proper_trace_eq : Proper (trace_eq eq ==> trace_eq eq ==> iff) (trace_eq Rt).
  Proof.
    do 3 red. split; intros.
    - eapply trace_eq_equiv; eauto. symmetry; eauto.
    - eapply trace_eq_equiv; eauto. symmetry; eauto.
  Qed.

  Lemma fmap_trace_eq : forall f g,
      (Rt ==> Ru)%signature f g ->
      forall (a d : trace U) (b c : trace T),
        trace_eq Rt b c ->
        trace_eq eq a (fmap f b) ->
        trace_eq eq (fmap g c) d ->
        trace_eq Ru a d.
  Proof.
    intros f g Hf.
    cofix.
    intros.
    inversion H; inversion H0; inversion H1; subst.
    constructor.
    { simpl. eapply Hf in H2. rewrite H6. rewrite <- H10.
      clear - H2.
      destruct b; destruct c. eapply H2. }
    { eapply (@fmap_trace_eq _ _ _ _ H3).
      - etransitivity; [ eassumption | clear ].
        constructor; destruct b; reflexivity.
      - etransitivity; [ clear | eassumption ].
        constructor; destruct c; reflexivity. }
  Qed.

  Global Instance Proper_fmap_trace_eq :
    Proper ((Rt ==> Ru) ==> trace_eq Rt ==> trace_eq Ru) fmap.
  Proof.
    do 3 red. intros.
    eapply fmap_trace_eq; solve [ eassumption | reflexivity ].
  Qed.

  Lemma trace_eq_trace_zip (f g : T -> U -> V) :
    (Rt ==> Ru ==> Rv)%signature f g ->
    forall a b c d X Y,
      trace_eq Rt a b ->
      trace_eq Ru c d ->
      trace_eq eq X (trace_zip f a c) ->
      trace_eq eq (trace_zip g b d) Y ->
      trace_eq Rv X Y.
  Proof.
    intro Hfg.
    cofix.
    do 4 inversion 1; subst.
    constructor.
    { rewrite H10. rewrite <- H15.
      destruct c; destruct d; simpl in *. eapply Hfg; eassumption. }
    { eapply (@trace_eq_trace_zip _ _ _ _ _ _ H1 H6).
      - etransitivity; [ eassumption | clear ].
        destruct a; destruct c; constructor; try reflexivity.
      - etransitivity; [ clear | eassumption ].
        destruct a; destruct c; constructor; try reflexivity. }
  Qed.

  Global Instance Proper_trace_zip :
    Proper ((Rt ==> Ru ==> Rv) ==> trace_eq Rt ==> trace_eq Ru ==> trace_eq Rv) trace_zip.
  Proof.
    do 4 red. intros.
    eapply trace_eq_trace_zip; solve [ eassumption | reflexivity ].
  Qed.

  Lemma fmap_trace_trace_zip_compose' {W} (Rw : W -> W -> Prop) (f f' : T -> U -> V) (g g' : V -> W) :
    (Rt ==> Ru ==> Rv)%signature f f' ->
    (Rv ==> Rw)%signature g g' ->
    forall a b c d X Y,
      trace_eq Rt a b ->
      trace_eq Ru c d ->
      trace_eq eq X (fmap_trace g (trace_zip f a c)) ->
      trace_eq eq (trace_zip (fun a b => g' (f' a b)) b d) Y ->
      trace_eq Rw X Y.
  Proof.
    intros Hf Hg.
    cofix.
    do 4 inversion 1; subst.
    constructor.
    { rewrite H10. rewrite <- H15.
      destruct a; destruct b; destruct c; destruct d; simpl in *.
      eapply Hg. eapply Hf; eauto. }
    { eapply fmap_trace_trace_zip_compose'; try eassumption. }
  Qed.

  Global Instance Proper_Continue : Proper (Rt ==> trace_eq Rt ==> trace_eq Rt) (@Continue T).
  Proof.
    compute; intros.
    constructor; eauto.
  Qed.

  Theorem trace_eq_eta (x : trace T) : trace_eq eq x (Continue (hd x) (tl x)).
  Proof.
    constructor; reflexivity.
  Qed.

End extra_trace_properties.

Theorem fmap_trace_trace_zip_compose {T U V W} (f : T -> U -> V) (g : V -> W) :
  forall a b,
    trace_eq eq (fmap_trace g (trace_zip f a b)) (trace_zip (fun a b => g (f a b)) a b).
Proof.
  intros. eapply fmap_trace_trace_zip_compose' with (Rt := eq) (Ru := eq) (Rv :=eq);
          try solve [ eassumption | reflexivity ].
Qed.
