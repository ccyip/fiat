Require Import
        Fiat.Computation
        Fiat.Common.DecideableEnsembles
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.LaxTerminalFormat.

Section SequenceFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)
  Context {monoid : Monoid T}. (* Target type is a monoid. *)

  Definition sequence
             (format1 : Comp T)
             (format2 : Comp T) :=
    (p <- format1;
       q <- format2;
       ret (mappend p q))%comp.

  Definition Sequence_Format
             (format1 format2 : FormatM S T)
    : FormatM S T := (fun s => sequence (format1 s) (format2 s))%comp.

  Global Add Parametric Morphism
    : Sequence_Format
      with signature ((@EquivFormat S T) ==> (@EquivFormat S T) ==> (@EquivFormat S T))
        as Sequence_Format_Equiv_congr.
  Proof.
    intros. unfold Sequence_Format, sequence.
    intro. setoid_rewrite H. setoid_rewrite H0. reflexivity.
  Qed.

  Definition Sequence_Decode
             {S' : Type}
             (decode1 : DecodeM (S' * T) T)
             (decode2 : S' -> DecodeM S T)
    : DecodeM S T
    := (fun t =>
          match decode1 t with
          | Some (s', t') => decode2 s' t'
          | None => None
          end).

  Definition Sequence_Encode
             (encode1 encode2 : EncodeM S T)
    := (fun s =>
          t1 <- encode1 s;
          t2 <- encode2 s;
          Some (mappend t1 t2)).

  Notation "x ++ y" := (Sequence_Format x y) : format_scope .

  Lemma CorrectEncoder_Sequence
        (format1 format2 : FormatM S T)
        (encode1 encode2 : EncodeM S T)
        (encode1_correct : CorrectEncoder format1 encode1)
        (encode2_correct : CorrectEncoder format2 encode2)
    : CorrectEncoder (format1 ++ format2)
                     (Sequence_Encode encode1 encode2).
  Proof.
    unfold CorrectEncoder, Sequence_Encode, Sequence_Format, sequence,
    BindOpt in *; intuition; intros.
    - destruct (encode1 s) as [ t1 | ] eqn: ? ;
        simpl in *; try discriminate.
      destruct (encode2 s) as [ t2 | ] eqn: ? ;
        simpl in *; try discriminate; injections.
      repeat computes_to_econstructor; eauto.
    - computes_to_inv. simpl in *.
       destruct (encode1 s) as [ t1 | ] eqn: ? ;
        simpl in *; try discriminate; eauto.
       eapply H2; try eassumption.
       destruct (encode2 s) as [ t2 | ] eqn: ? ;
        simpl in *; try discriminate; injections.
       reflexivity.
  Qed.

  Lemma CorrectDecoder_Sequence
        {S' : Type}
        (f : S -> S' -> Prop)
        (format1' : FormatM (S' * T) T)
        (format1 format2 : FormatM S T)
        (decode1 : DecodeM (S' * T) T)
        (decode2 : S' -> DecodeM S T)
        (format1_overlap : forall s t',
            format1 s ∋ t' -> exists s',
              forall t, format1' (s', t) ∋ (mappend t' t) /\ f s s')
        (format1'_overlap : forall s' t t'',
            format1' (s', t) ∋ t''
            -> forall s,
              f s s'
              -> exists t', format1 s ∋ t' /\ t'' = mappend t' t)
        (decode1_correct : CorrectDecoder_simpl format1' decode1)
        (decode2_correct : forall (s' : S'), CorrectDecoder_simpl (Restrict_Format (fun s => f s s') format2) (decode2 s'))
    : CorrectDecoder_simpl (format1 ++ format2)
                           (Sequence_Decode decode1 decode2).
  Proof.
    unfold CorrectDecoder_simpl, Projection_Format,
    Sequence_Decode, Sequence_Format, sequence, Compose_Format; split; intros.
    - computes_to_inv; subst.
      eapply format1_overlap in H; destruct_ex; split_and.
      simpl in *; injections.
      rewrite unfold_computes in H'.
      destruct decode1_correct as [? _].
      destruct (decode2_correct x) as [? _].
      specialize (H (x, v0) (mappend v v0)).
      rewrite H; eauto.
      apply H2.
      unfold Restrict_Format, Compose_Format; apply unfold_computes.
      setoid_rewrite unfold_computes; eexists; intuition eauto.
    - destruct (decode1 t) as [ [s' t'] | ] eqn: ?; try discriminate.
      destruct decode1_correct as [decode1_correct' decode1_correct].
      specialize (decode2_correct s'); destruct decode2_correct as [_ decode2_correct].
      generalize Heqo; intro Heqo'.
      eapply decode1_correct in Heqo; eauto.
      eapply decode2_correct in H; eauto.
      unfold Restrict_Format, Compose_Format, LaxTerminal_Format, Sequence_Format,
      Bind2 in H.
      rewrite unfold_computes in H. destruct_ex; split_and.
      rewrite unfold_computes in H1. split_and. subst.
      eapply format1'_overlap in H2; destruct_ex; split_and; subst; eauto.
      repeat computes_to_econstructor; eauto.
      rewrite H2. eauto.
  Qed.

  (* Corollary CorrectDecoder_Sequence_Projection *)
  (*       {S' : Type} *)
  (*       (f : S -> S') *)
  (*       (format1 : FormatM S' T) *)
  (*       (format2 : FormatM S T) *)
  (*       (decode1 : DecodeM (S' * T) T) *)
  (*       (decode2 : S' -> DecodeM S T) *)
  (*       (decode1_correct : CorrectDecoder_simpl (Projection_Format format1 fst ++ ?* ) decode1) *)
  (*       (decode2_correct : forall (s' : S'), CorrectDecoder_simpl (Restrict_Format (fun s => f s = s') format2) (decode2 s')) *)
  (*   : CorrectDecoder_simpl (Projection_Format format1 f ++ format2) *)
  (*                          (Sequence_Decode decode1 decode2). *)
  (* Proof. *)
  (*   unfold Projection_Format. *)
  (*   eapply (CorrectDecoder_Sequence (fun s s' => f s = s')); eauto; intros; *)
  (*     unfold Projection_Format, Compose_Format, Sequence_Format, sequence, Bind2, LaxTerminal_Format in *. *)
  (*   - rewrite @unfold_computes in H. *)
  (*     destruct_ex; split_and; subst. *)
  (*     eexists; intros; intuition. *)
  (*     simpl; computes_to_econstructor. *)
  (*     rewrite unfold_computes; eauto. *)
  (*     simpl; computes_to_econstructor; eauto. *)
  (*   - computes_to_inv; subst. *)
  (*     apply_in_hyp @unfold_computes; destruct_ex; split_and; subst. *)
  (*     eexists; simpl; intuition eauto. *)
  (* Qed. *)

  (*Corollary CorrectDecoder_sequence_Done
            {S : Type}
            (P : S -> Prop)
            (format : FormatM (S * T) T)
            (s : S)
            (singleton_format : forall (s' : S) (t : T) env tenv',
                format (s', t) env ∋ tenv' <-> s' = s
                                               /\ fst tenv' = mempty
                                               /\ snd tenv' = env)
    : CorrectDecoder_simpl (format ++ ?* ) (LaxTerminal_Decode s).
  Proof.
    unfold CorrectDecoder_simpl, LaxTerminal_Format,
    LaxTerminal_Decode, sequence_Format, Compose_Format; split; intros.
    - unfold Bind2 in H0; computes_to_inv; subst.
      injections.
      destruct data; eapply singleton_format in H0; simpl in *; intuition; subst.
      destruct v; simpl in *; subst.
      eexists; split; eauto.
      rewrite mempty_left; reflexivity.
    - injections; unfold Bind2; eexists.

      simpl.
      destruct v; destruct v0; simpl in *; injections.
      destruct decode1_correct as [? _].
      destruct (decode2_correct x) as [? _].
      destruct (H0 env env' c (x, t0) (mappend t t0)) as (xenv', (decode1_eq, Equiv_xenv));
        eauto.
      rewrite decode1_eq; eauto.
      eapply H3; eauto.
      unfold Restrict_Format, Compose_Format; apply unfold_computes.
      setoid_rewrite unfold_computes; eexists; intuition eauto.
    - destruct (decode1 bin env') as [ [ [s' t'] xenv'']  | ] eqn: ?; try discriminate.
      destruct decode1_correct as [decode1_correct' decode1_correct].
      specialize (decode2_correct s'); destruct decode2_correct as [_ decode2_correct].
      generalize Heqo; intro Heqo'.
      eapply decode1_correct in Heqo; eauto.
      destruct_ex; split_and.
      eapply decode2_correct in H0; eauto.
      destruct_ex; split_and.
      eexists; intuition eauto.
      unfold Restrict_Format, Compose_Format, LaxTerminal_Format, sequence_Format,
        Bind2 in *; computes_to_inv.
      rewrite @unfold_computes in H1.
      destruct_ex; split_and; simpl in *; subst.
      eapply format1'_overlap in H2; destruct_ex; split_and; subst; eauto.
  Qed.
    unfold

    eapply (CorrectDecoder_sequence (fun s s' => f s = s')); eauto; intros;
      unfold Projection_Format, Compose_Format, sequence_Format, Bind2, LaxTerminal_Format in *.
    - rewrite @unfold_computes in H.
      destruct_ex; split_and; subst.
      eexists; intros; intuition.
      destruct tenv'; simpl; computes_to_econstructor.
      rewrite unfold_computes; eauto.
      simpl; computes_to_econstructor; eauto.
    - computes_to_inv; subst.
      apply_in_hyp @unfold_computes; destruct_ex; split_and; subst.
      eexists; simpl; intuition eauto.
      destruct v; apply unfold_computes; eauto.
  Qed. *)


End SequenceFormat.

Notation "x ++ y" := (Sequence_Format x y) : format_scope .
