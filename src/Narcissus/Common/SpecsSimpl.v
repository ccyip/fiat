Require Export
        Coq.Lists.List
        Fiat.Common
        Fiat.Computation.Core
        Fiat.Computation.Notations
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Monoid.

Set Implicit Arguments.

Notation "a ∋ b" := (@computes_to _ a b) (at level 65) : format_scope.
Notation "a ∌ b" := (~ @computes_to _ a b) (at level 65) : format_scope.

Open Scope format_scope.

Section Specifications.

  Variable S : Type. (* Source Type. (in-memory data) *)
  Variable T : Type. (* Target Type. (usually ByteStrings) *)

  (* Formats are a binary relation on an source value and target value. *)
  Definition FormatM : Type :=
    S -> Comp T.

  (* Decoders consume a target value and produce either
     - a source value
     - or an error value, i.e. None. *)
  Definition DecodeM : Type :=
    T -> option S.

  (* Encoders take a source value and produce either a
     - target value
     - or an error value, i.e. None. *)
  Definition EncodeM : Type :=
    S -> option T.

  Definition CorrectDecoder_simpl
             (format : FormatM)
             (decode : DecodeM) :=
    (forall s t,
        format s ∋ t ->
        decode t = Some s) /\
    (forall s t,
        decode t = Some s ->
        format s ∋ t).

  Definition CorrectEncoder
             (format : FormatM)
             (encode : EncodeM) :=
    (forall s t,
        encode s = Some t ->
        format s ∋ t) /\
    (forall s,
        encode s = None ->
        forall t, ~ (format s ∋ t)).

  Definition EquivFormat (format1 format2 : FormatM) :=
    forall s, refineEquiv (format1 s) (format2 s).

  Global Instance EquivFormat_Equivalence : Equivalence EquivFormat.
  Proof.
    apply Equivalence.pointwise_equivalence.
    auto with typeclass_instances.
  Qed.

  Definition DisjointFormat (format1 format2 : FormatM) :=
    forall s1 t1, format1 s1 ∋ t1 ->
             forall s2 t2, format2 s2 ∋ t2 ->
                      t1 <> t2.

  Lemma CorrectDecoder_CorrectEncoder_inverse
    : forall (format : FormatM)
        (encode : EncodeM)
        (decode : DecodeM),
      CorrectDecoder_simpl format decode ->
      CorrectEncoder format encode ->
      forall s t,
        encode s = Some t ->
        decode t = Some s.
  Proof.
    intros. apply H. apply H0. assumption.
  Qed.

  Lemma CorrectEncoder_CorrectDecoder_inverse
    : forall (format : FormatM)
        (encode : EncodeM)
        (decode : DecodeM),
      CorrectDecoder_simpl format decode ->
      CorrectEncoder format encode ->
      forall s t,
        decode t = Some s ->
        exists t', encode s = Some t'.
  Proof.
    intros. apply H in H1. destruct (encode s) eqn:?; eauto.
    exfalso. eapply H0; eauto.
  Qed.

  Add Parametric Morphism
      (decode : DecodeM)
    : (fun format =>
         CorrectDecoder_simpl format decode)
      with signature (EquivFormat ==> impl)
        as CorrectDecoder_simpl_equiv_format.
  Proof.
    unfold EquivFormat, impl, CorrectDecoder_simpl;
      intuition eauto; intros.
    - eapply H1; eauto; apply H; eauto.
    - apply H. eauto.
  Qed.

  Lemma CorrectDecoder_simpl_equiv_decode
    : forall (format : FormatM)
        (decode decode' : DecodeM),
      (forall t, decode t = decode' t) ->
      CorrectDecoder_simpl format decode ->
      CorrectDecoder_simpl format decode'.
  Proof.
    unfold CorrectDecoder_simpl; intros; split_and; split; intros.
    - rewrite <- H. eauto.
    - eapply H2; eauto. congruence.
  Qed.

  Add Parametric Morphism
      (encode : EncodeM)
    : (fun format =>
         CorrectEncoder format encode)
      with signature (EquivFormat ==> impl)
        as CorrectEncoder_equiv_format.
  Proof.
    unfold EquivFormat, impl, CorrectEncoder;
      intuition eauto; intros.
    - eapply H; eauto.
    - eapply H2; eauto. apply H. eauto.
  Qed.

  Lemma CorrectEncoder_equiv_encode
    : forall (format : FormatM)
        (encode encode' : EncodeM),
      (forall s, encode s = encode' s) ->
      CorrectEncoder format encode ->
      CorrectEncoder format encode'.
  Proof.
    unfold CorrectEncoder; intros; split_and; split; intros.
    - eapply H1; eauto. congruence.
    - apply H2. congruence.
  Qed.

End Specifications.

Definition CorrectDecoder_partial
           {S T A}
           (format : FormatM S T)
           (decode : DecodeM A T)
           (R : FormatM S A) :=
  (forall s t,
      format s ∋ t ->
      exists a, decode t = Some a /\ R s ∋ a) /\
  (forall a t,
      decode t = Some a ->
      exists s, format s ∋ t /\ R s ∋ a).

Definition IdentityFormat {S} : FormatM S S := eq.

Lemma CorrectDecoder_partial_lift {S T}
      (format : FormatM S T) (decode : DecodeM S T)
  : CorrectDecoder_partial format decode IdentityFormat <->
    CorrectDecoder_simpl format decode.
Proof.
  split; intros H; destruct H as [H1 H2]; split; intros; unfold IdentityFormat in *.
  - destruct (H1 _ _ H) as [? [? ?]].
    rewrite unfold_computes in H3. subst. auto.
  - destruct (H2 _ _ H) as [? [? ?]].
    rewrite unfold_computes in H3. subst. auto.
  - eexists; split; eauto. congruence.
  - eexists; split; eauto. congruence.
Qed.

(* Option monad. *)
Definition BindOpt {A B}
           (a_opt : option A)
           (k : A -> option B) :=
  Ifopt a_opt as a Then k a Else None.

Notation "a <- c ; k" :=
  (BindOpt c%format (fun a => k%format)) : format_scope.

Lemma BindOpt_inv {A B}
      (a_opt : option A)
      (b : B)
      (k : A -> option B)
  : BindOpt a_opt k = Some b ->
    exists a',
      a_opt = Some a' /\ k a' = Some b.
Proof.
  intros. destruct a_opt.
  simpl in H.
  eexists; intuition eauto.
  easy.
Qed.
