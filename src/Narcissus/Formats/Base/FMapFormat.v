Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.SpecsSimpl.

Section ComposeFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Compose_Format
             (format1 : FormatM S' T)
             (format2 : FormatM S S') (* Transformation Relation *)
    : FormatM S T :=
    fun s t =>
      exists s', format1 s' ∋ t /\ format2 s ∋ s'.

  (* Equivalent definition. *)
  Definition Compose_Format'
             (format1 : FormatM S' T)
             (format2 : FormatM S S')
    : FormatM S T :=
    (fun s => s' <- format2 s; format1 s')%comp.

  Lemma Compose_Format_equiv format1 format2
    : EquivFormat (Compose_Format format1 format2) (Compose_Format' format1 format2).
  Proof.
    unfold Compose_Format, Compose_Format'.
    split; intros ? ?.
    - computes_to_inv. rewrite unfold_computes. eauto.
    - rewrite unfold_computes in H. destruct_ex.
      computes_to_econstructor; intuition eauto.
  Qed.

  Global Add Parametric Morphism
    : Compose_Format
      with signature ((@EquivFormat S' T) ==> (@EquivFormat S S') ==> (@EquivFormat S T))
        as Compose_Format_Equiv_congr.
  Proof.
    intros. rewrite !Compose_Format_equiv. unfold Compose_Format'.
    intro. setoid_rewrite H. setoid_rewrite H0. reflexivity.
  Qed.

  Definition Compose_Decode
             (decode1 : DecodeM S' T)
             (decode2 : DecodeM S S') (* Transformation Function *)
    : DecodeM S T :=
    fun t => s <- decode1 t; decode2 s.

  Definition Compose_Encode
             (encode1 : EncodeM S' T)
             (encode2 : EncodeM S S')
    : EncodeM S T :=
    fun s => s' <- encode2 s; encode1 s'.

  Lemma CorrectDecoder_Compose
        (format1 : FormatM S' T)
        (decode1 : DecodeM S' T)
        (format2 : FormatM S S') (* Transformation Relation *)
        (decode2 : DecodeM S S') (* Transformation Function *)
        (* TODO: The following two assumptions could be weakened in more than
           one way. Observe that S' is actually restricted to the intersection
           of the range of format2 and the domain of format1. *)
        (decode1_correct : CorrectDecoder_simpl format1 decode1)
        (decode2_correct : CorrectDecoder_simpl format2 decode2)
    : CorrectDecoder_simpl (Compose_Format format1 format2) (Compose_Decode decode1 decode2).
  Proof.
    unfold Compose_Decode, Compose_Format in *; split; intros.
    - rewrite unfold_computes in H.
      destruct_ex; intuition.
      apply decode1_correct in H0.
      apply decode2_correct in H1.
      rewrite H0. simpl. assumption.
    - rewrite unfold_computes.
      apply BindOpt_inv in H. destruct_ex. intuition.
      apply decode1_correct in H0. apply decode2_correct in H1.
      eexists. intuition eauto.
  Qed.

  Lemma CorrectEncoder_Compose
        (format1 : FormatM S' T)
        (encode1 : EncodeM S' T)
        (format2 : FormatM S S')
        (encode2 : EncodeM S S')
        (encode1_correct : CorrectEncoder format1 encode1)
        (encode2_correct : CorrectEncoder format2 encode2)
        (encode2_sound_choice :
           forall s s',
             encode2 s = Some s' ->
             forall x t,
               format1 x ∋ t ->
               format2 s ∋ x ->
               format1 s' ∋ t)
    : CorrectEncoder (Compose_Format format1 format2) (Compose_Encode encode1 encode2).
  Proof.
    unfold Compose_Encode, Compose_Format in *; split; intros.
    - apply unfold_computes.
      apply BindOpt_inv in H. destruct_ex. intuition.
      apply encode1_correct in H1.
      apply encode2_correct in H0.
      eexists. intuition eauto.
    - rewrite unfold_computes; intro; destruct_ex; split_and.
      destruct (encode2 s) eqn:?; simpl in *.
      eapply encode1_correct; eauto.
      eapply encode2_correct; eauto.
  Qed.

End ComposeFormat.

Section ComposeSpecializations.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Restrict_Format
             (P : S -> Prop)
             (format : FormatM S T)
    : FormatM S T
    := Compose_Format format (fun s s' => s = s' /\ P s').

  Lemma Restrict_Format_equiv P format
    : EquivFormat (Restrict_Format P format)
                  (fun s t => format s ∋ t /\ P s).
  Proof.
    unfold Restrict_Format, Compose_Format.
    split; intros ? ?; rewrite unfold_computes in *.
    - intuition. eexists. intuition eauto.
      rewrite unfold_computes. intuition eauto.
    - destruct_ex. intuition; rewrite @unfold_computes in *; intuition congruence.
  Qed.

  Global Add Parametric Morphism
    : Restrict_Format
      with signature ((pointwise_relation _ iff) ==> (@EquivFormat S T) ==> (@EquivFormat S T))
        as Restrict_Format_Equiv_congr.
  Proof.
    intros. unfold Restrict_Format.
    f_equiv; eauto.
    intro. split; intro; rewrite !unfold_computes; rewrite H; intuition eauto.
  Qed.

  Corollary CorrectEncoder_Restrict_Format
            (format : FormatM S T)
            (encode : EncodeM S T)
            (P : S -> Prop)
            (decideable_P : DecideableEnsemble P)
    : CorrectEncoder format encode ->
      CorrectEncoder (Restrict_Format P format)
                     (fun s => if (DecideableEnsembles.dec s) then encode s else None).
  Proof.
    intros.
    eapply CorrectEncoder_equiv_encode
      with (Compose_Encode encode (fun s => if DecideableEnsembles.dec s then Some s else None)).
    intros; unfold Compose_Encode. find_if_inside; reflexivity.
    eapply CorrectEncoder_Compose; intros; eauto; try split; intros;
      rewrite @unfold_computes in *;
      destruct (DecideableEnsembles.dec s) eqn:?; discriminate || injections;
      intuition eauto.
    - eapply dec_decides_P; eauto.
    - eapply Decides_false; subst; eauto.
    - congruence.
  Qed.

  Corollary CorrectDecoder_Restrict_Format
        (format : FormatM S T)
        (decode : DecodeM S T)
        (P : S -> Prop)
        (decideable_P : DecideableEnsemble P)
        (format_decode_corect : CorrectDecoder_simpl format decode)
    : CorrectDecoder_simpl (Restrict_Format P format)
                           (Compose_Decode decode (fun s => if (DecideableEnsembles.dec s) then Some s else None)).
  Proof.
    apply CorrectDecoder_Compose; eauto.
    split; intuition;
      rewrite @unfold_computes in *;
      destruct (DecideableEnsembles.dec t) eqn: ?; intuition; try first [congruence | easy].
    - exfalso. eapply Decides_false; eauto.
    - eapply dec_decides_P; eauto.
  Qed.

  Definition Projection_Format
             (format : FormatM S' T)
             (f : S -> S')
    : FormatM S T :=
    Compose_Format format (fun s s' => f s = s').

  Lemma Projection_Format_equiv
        (format : FormatM S' T)
        (f : S -> S')
    : EquivFormat (Projection_Format format f)
                  (fun s => format (f s)).
  Proof.
    unfold EquivFormat, Projection_Format, Compose_Format; split; intros ? ?.
    apply unfold_computes.
    eexists. intuition eauto. apply unfold_computes. reflexivity.
    rewrite unfold_computes in H; destruct_ex; intuition.
    rewrite unfold_computes in H1. subst; eauto.
  Qed.

  Global Add Parametric Morphism
    : Projection_Format
      with signature ((@EquivFormat S' T) ==> (pointwise_relation _ eq) ==> (@EquivFormat S T))
        as Projection_Format_Equiv_congr.
  Proof.
    intros.
    unfold Projection_Format.
    f_equiv; eauto.
    intro. rewrite H0. reflexivity.
  Qed.

  Corollary CorrectEncoder_Projection_Format
            (format : FormatM S' T)
            (encode : EncodeM S' T)
            (g : S -> S')
    : CorrectEncoder format encode ->
      CorrectEncoder (Projection_Format format g) (compose encode g).
  Proof.
    intros.
    eapply CorrectEncoder_equiv_encode
      with (Compose_Encode encode (fun s => Some (g s))). reflexivity.
    eapply CorrectEncoder_Compose; intros; eauto; try split; intros;
      rewrite @unfold_computes in *; discriminate || injections; auto.
  Qed.

End ComposeSpecializations.

Notation "format ◦ f" := (Projection_Format format f) (at level 55) : format_scope.
Notation "P ∩ format" := (Restrict_Format P format) (at level 55) : format_scope.
Notation "format2 <$> format1" := (Compose_Format format1 format2) (at level 55) : format_scope.
