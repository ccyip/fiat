Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL
        Fiat.Narcissus.Common.SpecsSeq
        Fiat.Computation.FixComp.

Import LeastFixedPointFun.

Definition GammaT := list Type.
Definition ConstrT S (gamma : GammaT) := cfunType gamma (S -> Prop).
Definition DecT S T (gamma : GammaT) := cfunType gamma (DecodeM S T).

Inductive FormatDSL_CorrectDecoder_Rules {S T A}
  : forall gamma : GammaT, ConstrT S gamma -> FormatDSL S A ->
                      FormatDSL S T -> DecodeM S T -> Prop :=
.

Inductive AFormatDSL_CorrectDecoder_Rules {S T A}
  : forall gamma : GammaT, ConstrT S gamma -> FormatDSL S A ->
                      AFormatDSL S T -> DecodeM (S*T) T -> Prop :=
.

Inductive FormatSeq_CorrectDecoder_Rules {S T A}
  : forall gamma : GammaT, ConstrT S gamma -> FormatDSL S A ->
                      forall {n}, FormatSeq S T n -> DecodeM (S*T) T -> Prop :=
.
