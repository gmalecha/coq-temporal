Require Import Coq.Classes.RelationClasses.
Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Tactics.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require ChargeCore.Logics.ILInsts.
Require Import ChargeCore.Tactics.Tactics.

Require Import Temporal.DiscreteStream.

Section parametric.
  Variable tlaState : Type.

  Definition Var (T : Type) : Type := tlaState -> T.

  Local Existing Instance Applicative_Fun.
  Local Existing Instance Functor_Fun.

  Definition StateVal (T : Type) : Type :=
    tlaState -> T.
  Definition ActionVal (T : Type) : Type :=
    tlaState -> tlaState -> T.
  Definition TraceVal (T : Type) :=
    trace tlaState -> T.

  Definition StateProp := StateVal Prop.

  Definition ActionProp := ActionVal Prop.

  Definition TraceProp := TraceVal Prop.

  Global Instance ILogicOps_StateProp : ILogicOps StateProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ActionProp : ILogicOps ActionProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_TraceProp : ILogicOps TraceProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogic_StateProp : ILogic StateProp := _.
  Global Instance ILogic_ActionProp : ILogic ActionProp := _.
  Global Instance ILogic_TraceProp : ILogic TraceProp := _.

  Local Transparent ILInsts.ILFun_Ops.

  Global Instance EmbedOp_Prop_StateProp : EmbedOp Prop StateProp :=
  { embed := fun P _ => P }.
  Global Instance Embed_Prop_StateProp : Embed Prop StateProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_Prop_ActionProp : EmbedOp Prop ActionProp :=
  { embed := fun P _ _ => P }.
  Global Instance Embed_Prop_ActionProp : Embed Prop ActionProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_Prop_TraceProp : EmbedOp Prop TraceProp :=
  { embed := fun P _ => P }.
  Global Instance Embed_Prop_TraceProp : Embed Prop TraceProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_StateVal_StateProp : EmbedOp (StateVal Prop) StateProp :=
  { embed := fun P => P }.
  Global Instance Embed_StateVal_StateProp : Embed (StateVal Prop) StateProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_ActionVal_ActionProp : EmbedOp (ActionVal Prop) ActionProp :=
  { embed := fun P => P }.
  Global Instance Embed_ActionVal_ActionProp : Embed (ActionVal Prop) ActionProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  Global Instance EmbedOp_TraceVal_TraceProp : EmbedOp (TraceVal Prop) TraceProp :=
  { embed := fun P => P }.
  Global Instance Embed_TraceVal_TraceProp : Embed (TraceVal Prop) TraceProp.
  Proof.
    constructor; simpl; intuition.
  Qed.

  (* These are the "obvious" definitions, needed to help Coq *)
  Global Instance Applicative_Action
  : Applicative ActionVal :=
  { pure := fun _ x => fun _ _ => x
  ; ap := fun _ _ f x => fun st st' => (f st st') (x st st')
  }.

  Global Instance Functor_Action
  : Functor ActionVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Global Instance Applicative_State
  : Applicative StateVal :=
  { pure := fun _ x => fun _ => x
  ; ap := fun _ _ f x => fun st => (f st) (x st)
  }.

  Global Instance Functor_State
  : Functor StateVal :=
  { fmap := fun _ _ f x => ap (pure f) x }.

  Definition now : StateProp -> TraceProp :=
    fun P tr => P (hd tr).

(* This does not make sense
  Definition next : StateProp -> TraceProp :=
    fun P tr => P (hd (tl tr)).
*)

  Definition always (P : TraceProp) : TraceProp :=
    fun s =>
      forall s', skips_to s' s -> P s'. (* NOTE: This is a bit backwards **)

  Definition eventually (P : TraceProp) : TraceProp :=
    fun s =>
      exists s', skips_to s s' /\ P s'.

  Definition starts (P : ActionProp) : TraceProp :=
    fun tr => P (hd tr) (hd (tl tr)).

  Definition pre {T} (f : tlaState -> T) : ActionVal T :=
    fun st _ => f st.

  Definition post {T} (f : tlaState -> T) : ActionVal T :=
    fun _ st' => f st'.

  (** This is not part of TLA **)
  Definition next (P : TraceProp) : TraceProp :=
    fun tr => P (tl tr).

(*
  Definition continuously (P : CActionProp) : ActionProp :=
    fun start step =>
      match step with
      | ContinuousBy r f => P r (fun x => hybrid_join (f x) (snd (hybrid_split start)))
      | _ => False
      end.
*)

  Definition stutter {T} (f : tlaState -> T) : ActionProp :=
    fun st st' => f st = f st'.

  Lemma always_skips_to : forall P t1 t2,
      skips_to t2 t1 ->
      always P t1 -> always P t2.
  Proof.
    unfold always. intros.
    eapply H0. etransitivity; eauto.
  Qed.

  (** Always Facts **)
  Lemma always_and : forall P Q,
      always P //\\ always Q -|- always (P //\\ Q).
  Proof.
    intros. split.
    { red. red. simpl. unfold always. intuition. }
    { red. red. simpl. unfold always.
      intuition; edestruct H; eauto. }
  Qed.

  Lemma always_or : forall P Q,
      always P \\// always Q |-- always (P \\// Q).
  Proof.
    red. red. simpl. unfold always. intuition.
  Qed.

  Lemma always_impl : forall P Q,
      always (P -->> Q) |-- always P -->> always Q.
  Proof.
    red. red. simpl. unfold always. intuition.
  Qed.

  Lemma always_tauto
    : forall G P, |-- P -> G |-- always P.
  Proof. compute; intuition. Qed.


  (** Generic logic lemma **)
  Lemma uncurry : forall P Q R,
      (P //\\ Q) -->> R -|- P -->> Q -->> R.
  Proof. compute. tauto. Qed.

  Lemma and_forall : forall {T} (F G : T -> Prop),
      ((forall x, F x) /\ (forall x, G x)) <->
      (forall x, F x /\ G x).
  Proof. firstorder. Qed.


  Lemma now_entails : forall (A B : StateProp),
      now (A -->> B) |-- now A -->> now B.
  Proof. unfold now. simpl. auto. Qed.


  Definition before (P : StateProp) : ActionProp :=
    fun st _ => P st.

  Definition after (P : StateProp) : ActionProp :=
    fun _ st' => P st'.


(*
  Coercion starts : ActionProp >-> TraceProp.
  Coercion discretely : DActionProp >-> ActionProp.
*)

  Lemma now_starts_discretely_and : forall P Q,
      now P //\\ starts Q -|- starts (before P //\\ Q).
  Proof.
    intros. split.
    { red; simpl. destruct t.
      unfold starts; destruct t0; simpl; tauto. }
    { red; simpl. destruct t.
      unfold starts; destruct t0; simpl; tauto. }
  Qed.

(*
  Lemma starts_next_impl : forall (P : DActionProp) (Q : StateProp),
      starts (discretely (fun st st' => P st st' -> Q st')) |-- starts (discretely P) -->> through (now Q).
  Proof.
    intros.
    { red; simpl. destruct t.
      unfold starts, discretely; destruct c; simpl. tauto.
      tauto. }
  Qed.
*)

  Lemma starts_after : forall (P : ActionProp) (Q : StateProp),
      (forall st, P st |-- Q) ->
      |-- starts P -->> starts (after Q).
  Proof.
    intros. unfold starts.
    red. simpl. intros.
    forward_reason.
    destruct t. destruct t0. simpl in *.
    unfold tl. simpl. red. simpl. eauto.
  Qed.

  Definition enabled (ap : ActionProp) : StateProp :=
    Exists st', fun st => ap st st'.

  (** Reasoning about [through] **)
  Lemma starts_and : forall P Q, starts P //\\ starts Q -|- starts (P //\\ Q).
  Proof.
    intros. apply and_forall. intros.
    unfold starts.
    simpl. destruct x. destruct x. intuition.
  Qed.

  Lemma starts_or : forall P Q, starts P \\// starts Q -|- starts (P \\// Q).
  Proof.
    intros. red. simpl.
    unfold starts. split; destruct t; destruct t0; intuition.
  Qed.

  Lemma starts_impl : forall P Q, starts P -->> starts Q -|- starts (P -->> Q).
  Proof.
    intros. red. simpl.
    unfold starts. split; destruct t; destruct t0; intuition.
  Qed.

  Lemma starts_ex : forall T (P : T -> _),
      Exists x : T, starts (P x) -|- starts (lexists P).
  Proof.
    intros; red; simpl.
    unfold starts. split; destruct t; destruct t0; intuition.
  Qed.

  Lemma starts_all : forall T (P : T -> _),
      Forall x : T, starts (P x) -|- starts (lforall P).
  Proof.
    intros; red; simpl.
    unfold starts. split; destruct t; destruct t0; intuition.
  Qed.

  Lemma next_now : forall (P : StateProp),
      next (now P) -|- starts (after P).
  Proof.
    intros. unfold next, starts, after.
    split. compute; auto. compute; auto.
  Qed.

  Lemma starts_tauto : forall (P : ActionProp),
      |-- P ->
      |-- starts P.
  Proof.
    compute. auto.
  Qed.

(*
  Definition startsD (P : StateProp) : DActionProp :=
    fun _ fin => P fin.
*)

  (** This is induction over the phase changes **)
  Lemma dind_lem : forall (P : TraceProp),
      |-- P -->> always (P -->> next P) -->> always P.
  Proof.
    intros. do 3 red.
    intros. red. simpl. red.
    intros. clear H. revert H0 H1.
    induction H2 using skips_to_ind; simpl.
    { (* Now *)
      intros. assumption. }
    { (* Later *)
      intros.
      eapply IHskips_to.
      { red in H1.
        eapply H1 in H0; try reflexivity.
        eapply H0. }
      { eapply always_skips_to. 2: eapply H1.
        eapply skips_to_next. reflexivity. } }
  Qed.

  Theorem hybrid_induction
    : forall G P T,
      G |-- always T ->
      G |-- P ->
      G |-- always (P -->> T -->> next P) ->
      G |-- always P.
  Proof.
    intros G P T. intros.
    generalize (dind_lem P).
    intros.
    charge_apply H2. eauto.
    apply Lemmas.lcut with (R:=G).
    charge_assumption.
    rewrite H at 1. rewrite H1.
    rewrite  <- always_impl.
    charge_revert.
    rewrite <- always_impl.
    apply always_tauto.
    charge_tauto.
  Qed.

End parametric.

Arguments pre {_ _} _ _ _.
Arguments post {_ _} _ _ _.
Arguments always {_} _ _.
Arguments eventually {_} _ _.
Arguments starts {_} _ _.
Arguments now {_} _ _.
Arguments stutter {_ _} _ _ _.
Arguments starts {_} _ _.

Export ChargeCore.Logics.ILogic.