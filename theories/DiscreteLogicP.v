Require Import Coq.Classes.RelationClasses.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Reals.Rdefinitions.
Require Import ExtLib.Structures.Applicative.
Require Import ExtLib.Structures.Functor.
Require Import ExtLib.Data.Fun.
Require Import ExtLib.Data.Prop.
Require Import ExtLib.Tactics.
Require Import ChargeCore.Logics.ILogic.
Require Import ChargeCore.Logics.ILEmbed.
Require ChargeCore.Logics.ILInsts.
Require Import ChargeCore.Tactics.Tactics.

Require Import Temporal.DiscreteStreamP.

Section parametric.
  Variable tlaState : Type.

  Definition Var (T : Type) : Type := tlaState -> T.

  Local Existing Instance Applicative_Fun.
  Local Existing Instance Functor_Fun.

  Definition StateVal (T : Type) : Type :=
    tlaState -> T.
  Definition ActionVal (T : Type) : Type :=
    tlaState -> tlaState -> T.
  Definition RawTraceVal (T : Type) :=
    trace tlaState -> T.
  Definition TraceVal (T : Type) :=
    { P : RawTraceVal T | Proper (trace_eq eq ==> eq) P }.

  Definition StateProp := StateVal Prop.

  Definition ActionProp := ActionVal Prop.

  Record TraceProp := mkTraceProp
  { tpred :> RawTraceVal Prop
  ; _ : Proper (trace_eq eq ==> iff) tpred }.

  Global Instance ILogicOps_StateProp : ILogicOps StateProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ActionProp : ILogicOps ActionProp :=
    @ILInsts.ILFun_Ops _ _ _.

  Local Transparent ILInsts.ILFun_Ops.
  Global Instance ILogicOps_TraceProp : ILogicOps TraceProp :=
  { lentails := fun P Q => forall x, tpred P x |-- tpred Q x
  ; ltrue    := mkTraceProp ltrue _
  ; lfalse   := mkTraceProp lfalse _
  ; land     := fun P Q => mkTraceProp (land (tpred P) (tpred Q)) _
  ; lor      := fun P Q => mkTraceProp (lor (tpred P) (tpred Q)) _
  ; limpl    := fun P Q => mkTraceProp (limpl (tpred P) (tpred Q)) _
  ; lforall  := fun T P => mkTraceProp (lforall (fun x => (tpred (P x)))) _
  ; lexists  := fun T P => mkTraceProp (lexists (fun x => (tpred (P x)))) _
  }.
  Proof.
    all: try solve [ compute; auto ].
    { compute; intros. destruct P; destruct Q; simpl in *.
      split; eauto.
      intros. eapply p0. Require Import Setoid.
      symmetry. eassumption. eapply H0.
      eapply p. eauto. eauto.
      intros. eapply p0; [ | eapply H0 ].
      eauto. eapply p; eauto. symmetry; eauto. }
    { compute; destruct P; destruct Q; split.
      { destruct 1; split.
        - eapply p; [ symmetry | ]; eauto.
        - eapply p0; [ symmetry | ]; eauto. }
      { destruct 1; split.
        - eapply p; [ | ]; eauto.
        - eapply p0; [ | ]; eauto. } }
    { compute; split; intros.
      { destruct H0; [ left; destruct P | right; destruct Q ].
        - eapply p; [ symmetry | ]; eauto.
        - eapply p; [ symmetry | ]; eauto. }
      { destruct H0; [ left; destruct P | right; destruct Q ].
        - eapply p; eauto.
        - eapply p; eauto. } }
    { compute. intros. split; intros.
      { specialize (H0 x0).
        destruct (P x0).
        eapply p; [ symmetry; eassumption | eauto ]. }
      { specialize (H0 x0).
        destruct (P x0).
        eapply p; [ eassumption | eauto ]. } }
    { compute. intros. split; intros.
      { destruct H0; exists x0.
        destruct (P x0).
        eapply p; [ symmetry; eassumption | eauto ]. }
      { destruct H0; exists x0.
        destruct (P x0).
        eapply p; [ eassumption | eauto ]. } }
  Defined.

  Global Instance ILogic_StateProp : ILogic StateProp := _.
  Global Instance ILogic_ActionProp : ILogic ActionProp := _.
  Global Instance ILogic_TraceProp : ILogic TraceProp.
  Proof.
    constructor.
    { constructor.
      { compute. destruct x; auto. }
      { compute. destruct x; destruct y; destruct z; auto. } }
    { compute; auto. }
    { compute; intros; tauto. }
    { compute; intros.
      specialize (H0 x).
      destruct (P x); destruct C; eauto. }
    { compute; intros.
      specialize (H x0).
      destruct (P x0); destruct C; eauto. }
    { compute; intros.
      destruct H0.
      specialize (H x0).
      destruct (P x0); destruct C; eauto. }
    { compute; intros.
      exists x.
      specialize (H x0).
      destruct (P x); destruct C; eauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C.
      eapply H. tauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C.
      eapply H. tauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto.
      destruct H1; eauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto.
      eapply H; tauto. }
    { compute; intros.
      destruct P; destruct Q; destruct C; eauto. }
  Qed.

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
  { embed := fun P => mkTraceProp (fun _ => P) _ }.
  Proof.
    compute. auto.
  Defined.

  Global Instance Embed_Prop_TraceProp : Embed Prop TraceProp.
  Proof.
    constructor; simpl; intuition.
    { red. simpl. eauto. }
    { red. simpl. eauto. }
    { red. simpl. eauto. }
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

(*
  Global Instance EmbedOp_TraceVal_TraceProp : EmbedOp (TraceVal Prop) TraceProp :=
  { embed := fun P => P }.
  Global Instance Embed_TraceVal_TraceProp : Embed (TraceVal Prop) TraceProp.
  Proof.
    constructor; simpl; intuition.
  Qed.
*)

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

  Definition now : StateProp -> TraceProp.
  Proof.
    refine (fun P => mkTraceProp (fun tr => P (hd tr)) _).
    compute. intros.
    destruct x; destruct y.
    inversion H.
    simpl in *. subst. auto.
  Defined.

  Definition always (P : TraceProp) : TraceProp.
  refine (
    mkTraceProp (fun s =>
                   forall s', skips_to s' s -> tpred P s') _).
  Proof.
      abstract (do 2 red; intros; setoid_rewrite H; reflexivity).
  Defined.

  Definition eventually (P : TraceProp) : TraceProp.
  refine (
    mkTraceProp (fun s =>
                  exists s', skips_to s s' /\ tpred P s') _).
  Proof.
    abstract (do 2 red; intros; setoid_rewrite H; reflexivity).
  Defined.

  Definition starts (P : ActionProp) : TraceProp.
  refine (
    mkTraceProp (fun tr => P (hd tr) (hd (tl tr))) _).
  Proof.
    abstract (do 2 red; intros; rewrite H; reflexivity).
  Defined.

  Definition pre {T} (f : tlaState -> T) : ActionVal T :=
    fun st _ => f st.

  Definition post {T} (f : tlaState -> T) : ActionVal T :=
    fun _ st' => f st'.

  Instance Proper_tpred : Proper (lequiv ==> trace_eq eq ==> iff) tpred.
  Proof.
    do 3 red. destruct x; destruct y; simpl.
    intros. rewrite H0.
    destruct H; split.
    { eapply H. }
    { eapply H1. }
  Qed.

  (** This is not part of TLA **)
  Definition next (P : TraceProp) : TraceProp.
  refine (mkTraceProp (fun tr => tpred P (tl tr)) _).
  Proof.
    abstract (do 2 red; intros; rewrite H; reflexivity).
  Defined.

  Definition stutter {T} (f : tlaState -> T) : ActionProp :=
    fun st st' => f st = f st'.

  Lemma always_skips_to : forall P t1 t2,
      skips_to t2 t1 ->
      tpred (always P) t1 -> tpred (always P) t2.
  Proof.
    unfold always. intros.
    compute in *. intros.
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
  Proof.
    compute; intuition.
    destruct P; destruct G; eauto.
  Qed.

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
    unfold now, starts, before; red; simpl; split; eauto.
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
    unfold starts, after. simpl; intros; eauto.
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
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma starts_impl : forall P Q, starts P -->> starts Q -|- starts (P -->> Q).
  Proof.
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma starts_ex : forall T (P : T -> _),
      Exists x : T, starts (P x) -|- starts (lexists P).
  Proof.
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma starts_all : forall T (P : T -> _),
      Forall x : T, starts (P x) -|- starts (lforall P).
  Proof.
    unfold starts; simpl; intros; split; simpl; eauto.
  Qed.

  Lemma next_now : forall (P : StateProp),
      next (now P) -|- starts (after P).
  Proof.
    unfold starts, next; simpl; intros; split; simpl; eauto.
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
    intros. red. simpl.
    intros. clear H. revert H0 H1.
    induction H2; simpl.
    { (* Now *)
      intros. rewrite H. assumption. }
    { (* Later *)
      intros.
      eapply IHskips_to.
      { red in H1.
        eapply H1 in H0; try reflexivity.
        eapply H0. }
      { intros.
        eapply H1; eauto using Later. } }
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
Arguments always {_} _.
Arguments eventually {_} _.
Arguments starts {_} _.
Arguments now {_} _.
Arguments stutter {_ _} _ _ _.
Arguments mkTraceProp {_} _ _.
Arguments tpred {_} _ _.


Lemma TraceProp_trace_eq {T} : forall (P : TraceProp T) x y,
    trace_eq eq x y -> tpred P x -> tpred P y.
Proof.
  destruct P; simpl; intros.
  eapply p; eauto. symmetry; eauto.
Qed.

Require Import Coq.Classes.Morphisms.

(** TODO: These should be generalized to [TraceVal], [ActionVal], and [StateVal] **)
Section simulations.
  Context {T U : Type}.
  Local Transparent ILInsts.ILFun_Ops.

  Variable f : U -> T.

  Definition focusT (P : TraceProp T) : TraceProp U.
  refine (
    mkTraceProp (fun tu => (tpred P) (fmap f tu)) _).
  eauto with typeclass_instances.
  { red. red. intros.
    destruct P. eapply p. eapply Proper_fmap_trace_eq; [ | eassumption ].
    reflexivity. }
  Defined.

  Definition focusS (P : StateProp T) : StateProp U :=
    fun tu => P (f tu).

  Definition focusA (P : ActionProp T) : ActionProp U :=
    fun st st' => P (f st) (f st').

  Theorem focusT_now : forall P, focusT (now P) -|- now (focusS P).
  Proof.
    compute; split; destruct x; auto.
  Qed.

  Theorem focusT_starts : forall P, focusT (starts P) -|- starts (focusA P).
  Proof.
    compute; split; destruct x; destruct x; auto.
  Qed.

End simulations.

(* Temporal Existential Quantification *)
Section temporal_exists.

  Context {T U : Type}.
  Local Transparent ILInsts.ILFun_Ops.

  Definition texists (P : TraceProp (T * U)) : TraceProp U.
  refine (
      mkTraceProp (fun tr : trace U => exists tr' : trace T,
                       tpred P (trace_zip pair tr' tr)) _).
  { red. red. intros.
    eapply exists_iff. intros.
    destruct P; simpl.
    eapply p.
    eapply Proper_trace_zip; solve [ reflexivity | assumption ]. }
  Defined.

  Global Instance Proper_texists_lentails
  : Proper (lentails ==> lentails) texists.
  Proof.
    unfold texists. repeat red.
    intros. destruct H0. eexists. eapply H. eassumption.
  Qed.

  Global Instance Proper_texists_lequiv
  : Proper (lequiv ==> lequiv) texists.
  Proof.
    unfold texists. split; repeat red; destruct 1; eexists; eapply H; eauto.
  Qed.

  Theorem texistsL : forall (P : TraceProp U) (Q : TraceProp (T * U)),
      Q |-- focusT snd P ->
      texists Q |-- P.
  Proof.
    intros. unfold texists.
    simpl. intros.
    destruct H0.
    eapply H in H0.
    clear - H0.
    destruct P; simpl in *.
    revert H0. eapply p.
    clear.
    etransitivity.
    2: eapply Proper_Continue; [ reflexivity | ].
    2: symmetry; etransitivity; [ eapply fmap_trace_trace_zip_compose | simpl ].
    eapply trace_eq_eta.
    generalize dependent (tl x).
    generalize dependent (tl x0).
    clear.
    cofix.
    constructor.
    { destruct t; destruct t0; reflexivity. }
    { destruct t; destruct t0; simpl. eapply texistsL. }
  Qed.

  Definition exactTrace (tr : trace T) : TraceProp T := mkTraceProp (trace_eq eq tr) _.

  Lemma exactTrace_exact : forall tr tr',
      trace_eq eq tr tr' ->
      tpred (exactTrace tr) tr'.
  Proof. compute; auto. Qed.
  Opaque exactTrace.

  Theorem texistsR : forall (P : TraceProp U) (Q : TraceProp (T * U)),
      (exists tr' : trace T, focusT snd P //\\ focusT fst (exactTrace tr') |-- Q) ->
      P |-- texists Q.
  Proof.
    intros. unfold texists.
    simpl. intros.
    destruct H.
    exists x0. eapply H.
    split.
    { unfold focusT.
      simpl.
      eapply TraceProp_trace_eq; [ | eassumption ].
      clear.
      etransitivity.
      2: eapply Proper_Continue; [ reflexivity | ].
      2: symmetry; etransitivity; [ eapply fmap_trace_trace_zip_compose | simpl ].
      eapply trace_eq_eta.
      generalize dependent (tl x).
      generalize dependent (tl x0).
      clear.
      cofix.
      constructor.
      { destruct t; destruct t0; reflexivity. }
      { destruct t; destruct t0; simpl. eapply texistsR. } }
    { simpl.
      eapply exactTrace_exact.
      clear.
      etransitivity.
      2: eapply Proper_Continue; [ reflexivity | ].
      2: symmetry; etransitivity; [ eapply fmap_trace_trace_zip_compose | simpl ].
      eapply trace_eq_eta.
      generalize dependent (tl x).
      generalize dependent (tl x0).
      clear.
      cofix.
      constructor.
      { destruct t; destruct t0; reflexivity. }
      { destruct t; destruct t0; simpl. eapply texistsR. } }
  Qed.

End temporal_exists.


Export ChargeCore.Logics.ILogic.