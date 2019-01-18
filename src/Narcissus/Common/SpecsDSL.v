Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats.

Inductive SpecsDSL S T : Type :=
| SL_Primitive: FormatM S T -> SpecsDSL S T
| SL_Compose {S'}: SpecsDSL S' T -> SpecsDSL S S' -> SpecsDSL S T
| SL_Projection {S'}: SpecsDSL S' T -> (S -> S') -> SpecsDSL S T
| SL_Restrict: SpecsDSL S T -> (S -> Prop) -> SpecsDSL S T
| SL_Union: SpecsDSL S T -> SpecsDSL S T -> SpecsDSL S T
| SL_Sequence `{Monoid T}: SpecsDSL S T -> SpecsDSL S T -> SpecsDSL S T
(* | SL_Fixpoint: (FormatM S T -> SpecsDSL S T) -> SpecsDSL S T *)
.

Fixpoint SpecsDSL_denote {S T} (dsl : SpecsDSL S T) : FormatM S T :=
  match dsl with
  | SL_Primitive fmt => fmt
  | SL_Compose _ fmt1 fmt2 => Compose_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  | SL_Projection _ fmt1 f => Projection_Format (SpecsDSL_denote fmt1) f
  | SL_Restrict fmt1 P => Restrict_Format P (SpecsDSL_denote fmt1)
  | SL_Union fmt1 fmt2 => Union_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  | SL_Sequence _ fmt1 fmt2 => Sequence_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  (* | SL_Fixpoint F => Fix_Format (fun rec => SpecsDSL_denote (F rec)) *)
  end.