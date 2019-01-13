Require Export
        Fiat.Narcissus.Formats.Base.FMapFormat
        Fiat.Narcissus.Formats.Base.UnionFormat
        Fiat.Narcissus.Formats.Base.SequenceFormat
        Fiat.Narcissus.Formats.Base.StrictTerminalFormat
        Fiat.Narcissus.Formats.Base.LaxTerminalFormat
        Fiat.Narcissus.Formats.Base.FixFormat
        (* Fiat.Narcissus.Formats.Base.EnqueueFormat *)
        .

Require Import Fiat.Narcissus.Common.SpecsSimpl.

Section ComposeUnion.
  Context {S : Type}.
  Context {T : Type}.
  Context {S' : Type}.

  Lemma Compose_Format_Union_dist_r (format1 format2 : FormatM S' T) (f : FormatM S S')
    : EquivFormat (Compose_Format (Union_Format format1 format2) f)
                  (Union_Format (Compose_Format format1 f) (Compose_Format format2 f)).
  Proof.
    unfold Compose_Format, Union_Format.
    split; intros ? ?; rewrite !@unfold_computes in *.
    - intuition; destruct_ex; eexists; rewrite unfold_computes; intuition eauto.
    - destruct_ex. intuition. rewrite @unfold_computes in *.
      intuition; eauto.
  Qed.

  Lemma Compose_Format_Union_dist_l (format1 format2 : FormatM S S') (f : FormatM S' T)
    : EquivFormat (Compose_Format f (Union_Format format1 format2))
                  (Union_Format (Compose_Format f format1) (Compose_Format f format2)).
  Proof.
    unfold Compose_Format, Union_Format.
    split; intros ? ?; rewrite !@unfold_computes in *.
    - intuition; destruct_ex; eexists; intuition eauto; rewrite unfold_computes; eauto.
    - destruct_ex. intuition. rewrite @unfold_computes in H1.
      intuition; [left | right]; eauto.
  Qed.

End ComposeUnion.

Corollary Restrict_Format_Union_dist {S T} (format1 format2 : FormatM S T) (P : S -> Prop)
  : EquivFormat (Restrict_Format P (Union_Format format1 format2))
                (Union_Format (Restrict_Format P format1) (Restrict_Format P format2)).
Proof.
  apply Compose_Format_Union_dist_r.
Qed.

