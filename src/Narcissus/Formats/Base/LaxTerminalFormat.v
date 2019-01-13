Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.SpecsSimpl.

Section LaxTerminalFormat.

  Context {S : Type}. (* Source type *)
  Context {T : Type}. (* Target type *)
  Context {monoid : Monoid T}. (* Target type is a monoid *)

  Definition LaxTerminal_Format
    : FormatM (S * T) T :=
    fun st => ret (snd st).

  Definition LaxTerminal_Decode
             (s : S)
    : DecodeM (S * T) T :=
    fun t => Some (s, t).

  Definition LaxTerminal_Encode
    : EncodeM (S * T) T :=
    fun st => Some (snd st).

  Lemma CorrectDecoder_LaxTerminal
        (s : S)
        (Singleton_Format : forall st t,
            LaxTerminal_Format st ∋ t ->
            s = fst st)
    : CorrectDecoder_simpl LaxTerminal_Format (LaxTerminal_Decode s).
  Proof.
    unfold CorrectDecoder_simpl, LaxTerminal_Decode, LaxTerminal_Format in *; split; intros.
    { computes_to_inv; injections; subst.
      destruct s0. simpl; intuition eauto.
      erewrite Singleton_Format with (st := (s0, t)); eauto.
    }
    { injections.
      intuition eauto.
    }
  Qed.

  Lemma CorrectEncoder_LaxTerminal
    : CorrectEncoder LaxTerminal_Format LaxTerminal_Encode.
  Proof.
    unfold CorrectEncoder, LaxTerminal_Format, LaxTerminal_Encode;
      split; intros.
    -  injections;
         repeat computes_to_econstructor; eauto using measure_mempty.
    - discriminate.
  Qed.

End LaxTerminalFormat.

Notation "'?*'" := (LaxTerminal_Format) (at level 99) : format_scope.
