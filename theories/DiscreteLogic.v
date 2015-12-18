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

Require Import Temporal.Lifting.
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
  Definition RawTraceVal (T : Type) :=
    trace tlaState -> T.
  Definition TraceVal (T : Type) :=
    { P : RawTraceVal T | Proper (trace_eq eq ==> eq) P }.

  Definition StateProp := StateVal Prop.

  Definition ActionProp := ActionVal Prop.

  Definition TraceProp :=
    @ILInsts.ILPreFrm (trace tlaState) (trace_eq eq) Prop _.
  Definition tpred (T : TraceProp) : trace tlaState -> Prop :=
    ILInsts.ILPreFrm_pred T.
  Definition mkTraceProp_iff (P : trace tlaState -> Prop)
             (Pr : Proper (trace_eq eq ==> iff) P)
  : TraceProp.
      eapply (@ILInsts.mkILPreFrm _ _ _ _ P).
      intros; simpl; eapply Pr; symmetry; assumption.
  Defined.
  Definition mkTraceProp (P : trace tlaState -> Prop)
             (Pr : Proper (trace_eq eq ==> Basics.impl) P)
  : TraceProp.
      eapply (@ILInsts.mkILPreFrm _ _ _ _ P).
      eapply Pr.
  Defined.

  Global Instance ILogicOps_StateProp : ILogicOps StateProp :=
    @ILInsts.ILFun_Ops _ _ _.
  Global Instance ILogicOps_ActionProp : ILogicOps ActionProp :=
    @ILInsts.ILFun_Ops _ _ _.

  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Global Instance ILogicOps_TraceProp : ILogicOps TraceProp :=
    ILInsts.ILPre_Ops.

  Global Instance ILogic_StateProp : ILogic StateProp := _.
  Global Instance ILogic_ActionProp : ILogic ActionProp := _.
  Global Instance ILogic_TraceProp : ILogic TraceProp := _.

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
    { red. simpl. split.
      - intros; eapply H; eauto; reflexivity.
      - intros; eapply H; eauto; reflexivity. }
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

  Definition pre {T} (f : StateVal T) : ActionVal T :=
    fun st _ => f st.

  Definition post {T} (f : StateVal T) : ActionVal T :=
    fun _ st' => f st'.

  Instance Proper_tpred : Proper (lequiv ==> trace_eq eq ==> iff) tpred.
  Proof.
    do 3 red. destruct x; destruct y; simpl.
    intros. split.
    { intros. eapply ILPreFrm_closed0. 2: eapply H.
      2: simpl; eapply ILPreFrm_closed; [ | eassumption ].
      eassumption. reflexivity. }
    { intros. eapply ILPreFrm_closed.
      2: eapply H; simpl. 2: eapply ILPreFrm_closed0; [ | eassumption ].
      symmetry. eassumption. reflexivity. }
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
    { red. red. simpl. unfold always. unfold tpred. intuition. }
    { red. red. simpl. unfold always.
      intuition; edestruct H; eauto. }
  Qed.

  Lemma always_or : forall P Q,
      always P \\// always Q |-- always (P \\// Q).
  Proof.
    red. red. simpl. unfold always, tpred. intuition.
  Qed.

  Lemma always_impl : forall P Q,
      always (P -->> Q) |-- always P -->> always Q.
  Proof.
    red. red. simpl. unfold always, tpred. intuition.
    rewrite <- x0 in H1.
    eapply H. eassumption. reflexivity. eapply H0.
    rewrite <- x0. assumption.
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
  Proof.
    unfold now. simpl. intros. revert H0.
    rewrite <- x0. assumption.
  Qed.


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
    unfold starts; simpl; intros; split; simpl; intros.
    { eapply H; eauto. reflexivity. }
    { rewrite x0 in H. eauto. }
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

  Global Instance Proper_starts_lentails
  : Proper (lentails ==> lentails) starts.
  Proof.
    red. red. intros.
    unfold starts. red. simpl.
    red in H. red in H. red in H.
    intros.
    eapply H. eassumption.
  Qed.

  Global Instance Proper_starts_lequiv
  : Proper (lequiv ==> lequiv) starts.
  Proof.
    red. red. intros.
    unfold starts. red. simpl.
    split; intros; eapply H; eauto.
  Qed.

  (** This is standard discrete induction over time **)
  Lemma dind_lem : forall (P : TraceProp),
      |-- P -->> always (P -->> next P) -->> always P.
  Proof.
    intros. do 3 red.
    intros. red. simpl.
    intros. clear H.
    change ILInsts.ILPreFrm_pred with tpred in *.
    specialize (fun s' H => H1 s' H s' (Reflexive_trace_eq _)).
    rewrite <- x0 in *; clear x0.
    rewrite x2 in *; clear x2.
    clear - H2 H0 H1.
    induction H2; simpl.
    { (* Now *)
      intros. rewrite H. assumption. }
    { (* Later *)
      intros.
      eapply IHskips_to.
      { eapply H1; eauto. reflexivity. }
      { intros. eapply H1; eauto using Later. } }
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
  eapply ILPreFrm_closed; eauto.
Qed.

Lemma TraceProp_trace_eq_iff {T} : forall (P : TraceProp T) x y,
    trace_eq eq x y -> tpred P x <-> tpred P y.
Proof.
  intros. split; eapply TraceProp_trace_eq; eauto. symmetry; eauto.
Qed.

Require Import Coq.Classes.Morphisms.

(** TODO: These should be generalized to [TraceVal], [ActionVal], and [StateVal] **)
Section simulations.
  Context {T U : Type}.
  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Variable f : U -> T.

  Definition focusT (P : TraceProp T) : TraceProp U.
  refine (
    mkTraceProp (fun tu => (tpred P) (fmap f tu)) _).
  eauto with typeclass_instances.
  { red. red. intros.
    destruct P. red.
    eapply TraceProp_trace_eq.
    eapply Proper_fmap_trace_eq; [ | eassumption ].
    reflexivity. }
  Defined.

  Definition focusS (P : StateProp T) : StateProp U :=
    fun tu => P (f tu).

  Definition focusA (P : ActionProp T) : ActionProp U :=
    fun st st' => P (f st) (f st').

  Theorem focusT_now : forall P, focusT (now P) -|- now (focusS P).
  Proof.
    compute; intros; split; destruct t; auto.
  Qed.

  Theorem focusT_starts : forall P, focusT (starts P) -|- starts (focusA P).
  Proof.
    compute; split; destruct t; destruct t; auto.
  Qed.

End simulations.

(* Temporal Existential Quantification *)
Section temporal_exists.

  Context {T U : Type}.
  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Definition texists (P : TraceProp (T * U)) : TraceProp U.
  refine (
      mkTraceProp (fun tr : trace U => exists tr' : trace T,
                       tpred P (trace_zip pair tr' tr)) _).
  { red. red. intros. red. intros.
    destruct H0. exists x0.
    eapply TraceProp_trace_eq. 2: eassumption.
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
    revert H0.
    destruct P; simpl in *.
    eapply ILPreFrm_closed.
    clear.
    rewrite fmap_trace_trace_zip_compose.
    simpl.
    revert x t.
    cofix.
    destruct x. destruct t0.
    constructor.
    - reflexivity.
    - eapply texistsL.
  Qed.

  Definition exactTrace (tr : trace T) : TraceProp T :=
    mkTraceProp (trace_eq eq tr) _.

  Lemma exactTrace_exact : forall tr tr',
      trace_eq eq tr tr' ->
      tpred (exactTrace tr) tr'.
  Proof. compute; auto. Qed.
  Opaque exactTrace.
End temporal_exists.

Arguments texists _ {_} _.

(* Notation for fields *)
Notation "x # y" := (PreFun.compose y x) (at level 0).

Section temporal_history.
  Local Transparent ILInsts.ILFun_Ops.
  Local Transparent ILInsts.ILPre_Ops.

  Local Opaque trace_zip.
  Local Opaque fmap_trace.

  Context {T U : Type}.
  Theorem texists_history
  : forall (P : TraceProp U) (x : StateVal U T),
      P -|- texists (list T)
               (     focusT snd P
                //\\ now (lift2 eq fst (pure nil))
                //\\ always (starts (lift2 eq (post fst)
                                           (lift2 cons (pre snd#x)
                                                  (pre fst))))).
  Proof.
    intros. simpl. unfold texists.
    split.
    { simpl. intros.
      exists (fmap (List.map x) (prefixes nil t)).
      split; [ | split ].
      - eapply Proper_tpred; [ reflexivity | | eassumption ].
        rewrite fmap_trace_trace_zip_compose.
        simpl.
        clear. rewrite trace_zip_snd. reflexivity.
      - simpl. destruct t. reflexivity.
      - simpl. intros.
        unfold pre, post.
        assert (exists rst pre,
                   skips_to rst t /\
                   trace_eq eq s' (trace_zip pair (fmap_trace (List.map x) (prefixes pre rst)) rst)).
        { clear - H0.
          remember (trace_zip pair (fmap_trace (List.map x) (prefixes nil t)) t).
          generalize dependent (@nil U). generalize dependent t.
          induction H0.
          { intros. subst. exists t0. exists l. split; eauto.
            reflexivity. }
          { intros. subst.
            destruct (IHskips_to (tl t0) (List.cons (hd t0) l)).
            { destruct t0. reflexivity. }
            { destruct H. destruct H.
              exists x0. eexists. split; eauto.
              constructor 2. eassumption. } } }
        { clear H0. destruct H1. destruct H0. destruct H0.
          rewrite H1.
          destruct x0. destruct x0. reflexivity. } }
    { simpl. intros.
      destruct H. destruct H.
      clear H0.
      eapply Proper_tpred; [ reflexivity | | eassumption ].
      rewrite fmap_trace_trace_zip_compose. simpl.
      rewrite trace_zip_snd. reflexivity. }
  Qed.

End temporal_history.


Export ChargeCore.Logics.ILogic.