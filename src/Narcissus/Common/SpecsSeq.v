Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Section Specification_Sequence.

  Variable S : Type.
  Variable T : Type.
  Context {monoid : Monoid T}.

  Inductive SpecsSeq (bf bt : bool) : Type :=
  | SSeq_one: SpecsDSL S T -> bool -> SpecsSeq bf bt
  | SSeq_cons bm: SpecsDSL S T -> bool -> SpecsSeq bm bt -> SpecsSeq bf bt
  .

  Fixpoint SpecsSeq_len {bf bt : bool} (seq : SpecsSeq bf bt) : nat :=
    match seq with
    | SSeq_one _ _ => 1
    | SSeq_cons _ _ _ seq' => Datatypes.S (SpecsSeq_len seq')
    end.

  (* Definition SpecsSeq_lift {n} *)
  (*   : Vector.t (SpecsDSL S T) (Datatypes.S n) -> SpecsSeq false false := *)
  (*   Vector.rectS (fun _ _ => SpecsSeq false false) *)
  (*                (fun fmt => SSeq_one false false fmt false) *)
  (*                (fun fmt _ _ seq => SSeq_cons false fmt false seq). *)

  (* Fixpoint SpecsSeq_erase {bf bt} (seq : SpecsSeq bf bt) *)
  (*   : Vector.t _ (SpecsSeq_len seq) := *)
  (*   match seq with *)
  (*   | SSeq_one fmt _ => Vector.cons _ fmt _ (Vector.nil _) *)
  (*   | SSeq_cons _ fmt _ seq' => Vector.cons _ fmt _ (SpecsSeq_erase seq') *)
  (*   end. *)

End Specification_Sequence.
