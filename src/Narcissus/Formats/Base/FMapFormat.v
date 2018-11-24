Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Common.DecideableEnsembles
        Fiat.Computation
        Fiat.Narcissus.Common.Specs.

Section ComposeFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Compose_Format
    (format : FormatM S' T)
      (f : S -> S' -> Prop) (* Transformation Relation *)
    : FormatM S T :=
    fun s env benv' =>
      exists s', format s' env ∋ benv' /\ f s s'.

  Definition Compose_Decode {S' : Type}
             (decode : DecodeM S' T)
             (g : S' -> option S) (* Transformation Function *)
    : DecodeM S T  :=
    fun b env => `(s, env') <- decode b env; match g s with | Some s => Some (s, env') | None => None end.

  Definition Compose_Encode
             {S' : Type}
             (encode : EncodeM S' T)
             (f' : S -> option S')
    : EncodeM S T :=
    fun s => Ifopt f' s as s' Then encode s' Else fun _ => None.

  Lemma CorrectDecoder_Compose
        (format : FormatM S' T)
        (decode : DecodeM S' T)
        (f : S -> S' -> Prop) (* Transformation Relation *)
        (g : S' -> option S) (* Transformation Function *)
        (format_decode_corect : CorrectDecoder_simpl format decode)
        (g_inverts_f : forall s s' env benv,
            format s' env benv -> f s s' -> g s' = Some s)
        (g_OK : forall s s', g s' = Some s -> f s s')
    : CorrectDecoder_simpl (Compose_Format format f) (Compose_Decode decode g).
  Proof.
    unfold CorrectDecoder_simpl, Compose_Decode, Compose_Format in *; split; intros.
    { rewrite @unfold_computes in H0.
      destruct_ex; intuition.
      rewrite @unfold_computes in H3.
      pose proof (g_inverts_f  _ _ _ _ H3 H4).
      rewrite <- unfold_computes in H3.
      eapply H1 in H3; destruct_ex; intuition eauto.
      eexists; rewrite H5; simpl; intuition eauto.
      rewrite H0.
      subst; eauto.
    }
    { apply_in_hyp DecodeBindOpt_inv; destruct_ex; intuition.
      destruct (g x) eqn:?; [inversion_clear H4 | easy].
      eapply H2 in H3; eauto; injections.
      destruct_ex; eexists; intuition eauto.
      apply unfold_computes.
      eexists; intuition eauto.
    }
  Qed.

  Lemma CorrectEncoder_Compose
        (format : FormatM S' T)
        (encode : EncodeM S' T)
        (f : S -> S' -> Prop)
        (f' : S -> option S')
        (f'_refines_f_1 :
           forall s s',
             f' s = Some s' ->
             f s s')
        (f'_refines_f_2 :
           forall s,
             f' s = None ->
             forall s', ~ f s s')
        (f'_sound_choice :
           forall s s',
             f' s = Some s' ->
             forall x env benv,
               format x env ∋ benv
               -> f s x
               -> format s' env ∋ benv)
    : CorrectEncoder format encode
      -> CorrectEncoder (Compose_Format format f) (Compose_Encode encode f').
  Proof.
    unfold CorrectEncoder, Compose_Encode, Compose_Format in *; split; intros.
    - apply unfold_computes.
      destruct (f' a) eqn: ?; simpl in *; try discriminate.
      eapply H in H0; eexists; intuition eauto.
    - rewrite unfold_computes; intro;  destruct_ex; split_and.
      destruct (f' a) eqn: ?; simpl in *; try discriminate.
      eapply H4; eauto.
      eapply f'_refines_f_2; eauto.
  Qed.

End ComposeFormat.

Section ComposeSpecializations.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {cache : Cache}. (* State Type *)
  Context {S' : Type}. (* Transformed Type *)

  Definition Restrict_Format
             (P : S -> Prop)
             (format : FormatM S T)
    : FormatM S T
    := Compose_Format format (fun s s' => s = s' /\ P s').

  Lemma Restrict_Format_simpl P format
    : EquivFormat (Restrict_Format P format)
                  (fun s env benv => format s env ∋ benv /\ P s).
  Proof.
    unfold Restrict_Format, Compose_Format.
    split; intros ? ?; rewrite unfold_computes in *.
    - intuition. eexists; intuition eauto.
    - destruct_ex. intuition congruence.
  Qed.

  Corollary CorrectEncoder_Restrict_Format
            (format : FormatM S T)
            (encode : EncodeM S T)
            (P : S -> Prop)
            (decideable_P : DecideableEnsemble P)
    : CorrectEncoder format encode
      -> CorrectEncoder (Restrict_Format P format) (fun s => if (DecideableEnsembles.dec s) then encode s else fun _ => None).
  Proof.
    intros; replace
              (fun s : S => if DecideableEnsembles.dec s then encode s else fun _ : CacheFormat => None)
              with (Compose_Encode encode (fun s => if DecideableEnsembles.dec s then Some s else None)).
    eapply CorrectEncoder_Compose; intros;
      try (destruct (DecideableEnsembles.dec s) eqn: ?; first [discriminate | injections]);
      intuition eauto.
    - eapply dec_decides_P; eauto.
    - eapply Decides_false; subst; eauto.
    - subst; eauto.
    - apply functional_extensionality; intros; unfold Compose_Encode;
        find_if_inside; reflexivity.
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
    apply CorrectDecoder_Compose; eauto; intuition; subst;
      destruct (DecideableEnsembles.dec s') eqn: ?; eauto;
      try first [congruence | easy].
    - exfalso. eapply Decides_false; eauto.
    - eapply dec_decides_P; eauto.
  Qed.

  Definition Projection_Format
             (format : FormatM S' T)
             (f : S -> S')
    : FormatM S T :=
    Compose_Format format (fun s s' => f s = s').

  Lemma EquivFormat_Projection_Format
        (format : FormatM S' T)
        (f : S -> S')
    : EquivFormat (Projection_Format format f)
                  (fun s => format (f s)).
  Proof.
    unfold EquivFormat, Projection_Format, Compose_Format; split; intros ? ?.
    apply unfold_computes.
    eexists; eauto.
    rewrite unfold_computes in H; destruct_ex; intuition; subst; eauto.
  Qed.

  Corollary CorrectEncoder_Projection_Format
            (format : FormatM S' T)
            (encode : EncodeM S' T)
            (g : S -> S')
    : CorrectEncoder format encode
      -> CorrectEncoder (Projection_Format format g) (compose encode g).
  Proof.
    intros; replace
              (compose encode g)
              with (Compose_Encode encode (fun s => Some (g s))).
    eapply CorrectEncoder_Compose; intros;
      try (destruct (DecideableEnsembles.dec s') eqn: ?; first [discriminate | injections]);
      intuition eauto.
    apply functional_extensionality; intros; reflexivity.
  Qed.

End ComposeSpecializations.

Notation "format ◦ f" := (Projection_Format format f) (at level 55) : format_scope.
Notation "P ∩ format" := (Restrict_Format P format) (at level 55) : format_scope.
