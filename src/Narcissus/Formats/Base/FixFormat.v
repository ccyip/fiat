Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.Formats.Base.FMapFormat.

Require Import Fiat.Computation.FixComp.
Import Fiat.Computation.FixComp.LeastFixedPointFun.

Section FixFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)

  Definition Fix_Format
             (format_body : FormatM S T -> FormatM S T)
    := LeastFixedPoint (fDom := [S]%type)
                       (fCod := T) format_body.

  Fixpoint FueledFix' {A B}
           (f : (B -> option A) -> B -> option A)
           (n : nat)
    : B -> option A :=
    match n with
    | Datatypes.S n' => f (FueledFix' f n')
    | _ => fun _ => None
    end.


  Theorem FueledFix_continuous {A B} (F : (B -> option A) -> B -> option A)
    : (forall n a b,
          FueledFix' F n b = Some a ->
          FueledFix' F (Datatypes.S n) b = Some a) ->
      forall n n',
        n <= n' ->
        forall a b,
          FueledFix' F n b = Some a ->
          FueledFix' F n' b = Some a.
  Proof.
    intros; induction H0; eauto.
  Qed.

  Definition Fix_Decode
             {monoid : Monoid T}
             (decode_body : DecodeM S T -> DecodeM S T)
    : DecodeM S T :=
    fun t => FueledFix' decode_body (Datatypes.S (bin_measure t)) t.

  Definition Compose_Target
             (P : T -> Prop)
             (format : FormatM S T)
    : FormatM S T :=
    fun s t =>
      format s ∋ t /\ P t.

  Lemma CorrectDecoder_Fix'
        (decode_body : DecodeM S T -> DecodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S] T ->
                                                                  funType [S] T))
        (bound : T -> nat)
        (decode_body_correct :
           forall n,
             (CorrectDecoder_simpl
                (Compose_Target (fun t => bound t < n)  (Fix_Format format_body))
                (FueledFix' decode_body n)) ->
             CorrectDecoder_simpl
               (Compose_Target (fun t => bound t < Datatypes.S n)
                            (format_body (Fix_Format format_body)))
               (decode_body (FueledFix' decode_body n)))
    : forall n,
      CorrectDecoder_simpl
        (Compose_Target (fun t => bound t < n) (Fix_Format format_body))
        (FueledFix' decode_body n).
  Proof.
    induction n; simpl; intros.
    - split; unfold Compose_Target; intros.
      + rewrite @unfold_computes in H; omega.
      + discriminate.
    - split; unfold Compose_Target in *; intros.
      + rewrite @unfold_computes in H; split_and.
        apply_in_hyp (unroll_LeastFixedPoint format_body_OK).
        eapply decode_body_correct; eauto.
        apply unfold_computes; intuition eauto.
      + eapply decode_body_correct in H; eauto.
        rewrite @unfold_computes in H.
        destruct_ex; split_and.
        apply unfold_computes.
        intuition eauto.
        eapply (unroll_LeastFixedPoint' format_body_OK).
        intuition.
  Qed.

  Lemma CorrectDecoder_Fix
        {monoid : Monoid T}
        (decode_body : DecodeM S T -> DecodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S] T ->
                                                                  funType [S] T))
        (decode_body_correct :
           forall n,
             (CorrectDecoder_simpl
                (Compose_Target (fun t => bin_measure t < n)
                             (Fix_Format format_body))
                (FueledFix' decode_body n)) ->
             CorrectDecoder_simpl
               (Compose_Target (fun t => bin_measure t < Datatypes.S n)
                            (format_body (Fix_Format format_body)))
               (decode_body (FueledFix' decode_body n)))
        (decode_body_continuous :
           forall decode,
             (forall t s,
                 decode t = Some s ->
                 decode_body decode t = Some s) ->
             forall t s,
               decode_body decode t = Some s ->
               decode_body (decode_body decode) t = Some s)
    : CorrectDecoder_simpl
        (Fix_Format format_body)
        (Fix_Decode decode_body).
  Proof.
    split; intros.
    - destruct (CorrectDecoder_Fix'
                  decode_body format_body_OK bin_measure
                  decode_body_correct (Datatypes.S (bin_measure t))) as [? _]; eauto.
      apply H0.
      unfold Compose_Target; apply unfold_computes; split; eauto.
    - destruct (CorrectDecoder_Fix'
                  decode_body format_body_OK bin_measure
                  decode_body_correct (Datatypes.S (bin_measure t))) as [_ ?]; eauto.
      apply H0.
      intuition eauto.
  Qed.

  Definition Fix_Encode
             (measure : S -> nat)
             (encode_body : EncodeM S T -> EncodeM S T)
    : EncodeM S T :=
    fun s => FueledFix' encode_body (Datatypes.S (measure s)) s.

    Lemma CorrectEncoder_Fix'
        (encode_body : EncodeM S T -> EncodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S] T ->
                                                                  funType [S] T))
        (measure : S -> nat)
        (encode_body_correct :
           forall n encode,
             (CorrectEncoder
                (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
                encode) ->
             CorrectEncoder
               (Restrict_Format (fun s => measure s < Datatypes.S n)
                                (format_body (Fix_Format format_body)))
               (encode_body encode))
    : forall n,
      CorrectEncoder
        (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
        (FueledFix' encode_body n).
    Proof.
    induction n; simpl; intros.
    - split; unfold Restrict_Format, Compose_Format; intros.
      + discriminate.
      + intro H'; rewrite @unfold_computes in H'. destruct_ex. rewrite !unfold_computes in H0. omega.
    - split; unfold Restrict_Format, Compose_Format in *; intros.
      + apply unfold_computes; intuition eauto.
        eapply encode_body_correct in H; eauto.
        rewrite @unfold_computes in H; destruct_ex; split_and.
        apply_in_hyp (unroll_LeastFixedPoint' format_body_OK); eauto.
      + intro H'; rewrite unfold_computes in H'.
        eapply encode_body_correct in H; eauto; eapply H.
        destruct_ex; split_and.
        apply unfold_computes.
        eexists; subst; intuition eauto.
        eapply (unroll_LeastFixedPoint format_body_OK); eauto.
  Qed.

    Lemma CorrectEncoder_Fix
          (encode_body : EncodeM S T -> EncodeM S T)
        (format_body : FormatM S T -> FormatM S T)
        (format_body_OK : Frame.monotonic_function (format_body : funType [S] T ->
                                                                  funType [S] T))
        (measure : S -> nat)
        (encode_body_correct :
           forall n encode,
             (CorrectEncoder
                (Restrict_Format (fun s => measure s < n) (Fix_Format format_body))
                encode) ->
             CorrectEncoder
               (Restrict_Format (fun s => measure s < Datatypes.S n)
                                (format_body (Fix_Format format_body)))
               (encode_body encode))
        (*
          (encode_body_continuous :
          forall encode,
          (forall t env s env',
          encode t env = Some (s, env') ->
          encode_body encode t env = Some (s, env')) ->
          forall t env s env',
          encode_body encode t env = Some (s, env') ->
                      encode_body (encode_body encode) t env = Some (s, env'))

         *)
    : CorrectEncoder
        (Fix_Format format_body)
        (Fix_Encode measure encode_body).
  Proof.
    split; intros.
    - destruct (CorrectEncoder_Fix'
                  encode_body format_body_OK measure
                  encode_body_correct (Datatypes.S (measure s))) as [? _]; eauto.
      eapply H0 in H. clear H0.
      unfold Restrict_Format, Compose_Format in H.
      rewrite  @unfold_computes in H.
      destruct_ex; split_and; subst; eauto.
      rewrite  @unfold_computes in H1.
      split_and. subst. auto.
    - destruct (CorrectEncoder_Fix'
                  encode_body format_body_OK measure
                  encode_body_correct (Datatypes.S (measure s))) as [_ ?]; eauto.
      eapply H0 in H. clear H0.
      intro; eapply H.
      unfold Restrict_Format, Compose_Format; apply unfold_computes.
      eexists. intuition eauto. apply unfold_computes. intuition eauto.
  Qed.

End FixFormat.
