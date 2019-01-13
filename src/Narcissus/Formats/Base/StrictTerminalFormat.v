Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.SpecsSimpl.

Section StrictTerminalFormat.

  Context {S : Type}. (* Source type *)
  Context {T : Type}. (* Target type *)
  Context {monoid : Monoid T}. (* Target type is a monoid *)

  Definition StrictTerminal_Format
    : FormatM S T :=
   (fun a =>
      t <- {t | bin_measure t = 0};
      ret t)%comp.

  Definition StrictTerminal_Decode
             (s : S)
    : DecodeM S T :=
    fun t =>
      If (beq_nat (bin_measure t) 0)
         Then Some s
         Else None.

  Definition StrictTerminal_Encode
    : EncodeM S T :=
    fun a => Some mempty.

  Lemma CorrectDecoder_StrictTerminal
        (s : S)
        (Singleton_Format : forall s' t,
            StrictTerminal_Format s ∋ t ->
            s = s')
    : CorrectDecoder_simpl StrictTerminal_Format (StrictTerminal_Decode s).
  Proof.
    unfold CorrectDecoder_simpl, StrictTerminal_Decode, StrictTerminal_Format in *; split; intros.
    { computes_to_inv; injections; subst.
      rewrite H; simpl.
      erewrite Singleton_Format; eauto.
    }
    { destruct (beq_nat (bin_measure t) 0) eqn: ?; simpl in *;
        try discriminate.
      apply_in_hyp beq_nat_true.
      injections.
      intuition eauto.
    }
  Qed.

  Lemma CorrectEncoder_StrictTerminal
    : CorrectEncoder StrictTerminal_Format StrictTerminal_Encode.
  Proof.
    unfold CorrectEncoder, StrictTerminal_Format, StrictTerminal_Encode;
      split; intros.
    -  injections;
         repeat computes_to_econstructor; eauto using measure_mempty.
    - discriminate.
  Qed.

End StrictTerminalFormat.

Notation "'ϵ'" := (StrictTerminal_Format) (at level 99) : format_scope.
