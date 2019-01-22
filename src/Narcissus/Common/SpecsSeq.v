Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Section Specification_Sequence.

  Variable S : Type.
  Variable T : Type.

  Inductive SpecsSeg (bf bt : bool) : Type :=
  | SSeg_intro: SpecsDSL S T -> bool -> SpecsSeg bf bt
  .

  Inductive SpecsSeq (bf bt : bool) : Type :=
  | SSeq_one: SpecsSeg bf bt -> SpecsSeq bf bt
  | SSeq_cons bm: SpecsSeg bf bm -> SpecsSeq bm bt -> SpecsSeq bf bt
  .

  Fixpoint SpecsSeq_len {bf bt : bool} (seq : SpecsSeq bf bt) : nat :=
    match seq with
    | SSeq_one _ => 1
    | SSeq_cons _ _ seq' => Datatypes.S (SpecsSeq_len seq')
    end.

  (* Definition SpecsSeq_lift {n} *)
  (*   : Vector.t (SpecsDSL S T) (Datatypes.S n) -> SpecsSeq false false := *)
  (*   Vector.rectS (fun _ _ => SpecsSeq false false) *)
  (*                (fun fmt => SSeq_one (SSeg_intro false false fmt false)) *)
  (*                (fun fmt _ _ seq => SSeq_cons (SSeg_intro false false fmt false) seq). *)

  (* Fixpoint SpecsSeq_erase {bf bt} (seq : SpecsSeq bf bt) *)
  (*   : Vector.t _ (SpecsSeq_len seq) := *)
  (*   match seq with *)
  (*   | SSeq_one (SSeg_intro fmt _) => Vector.cons _ fmt _ (Vector.nil _) *)
  (*   | SSeq_cons _ (SSeg_intro fmt _) seq' => Vector.cons _ fmt _ (SpecsSeq_erase seq') *)
  (*   end. *)

End Specification_Sequence.
