Require Import
        Coq.omega.Omega
        Coq.Strings.String
        Coq.Vectors.Vector.

Require Import
        Fiat.Computation
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats.

Section SimpleFormat.
  Context {A : Type}. (* Carrier *)
  Context {T : Type}. (* Target Type. May use ByteString instead. *)

  Variable format_A : FormatM A T.
  Variable decode_A : DecodeM A T.
  Variable decode_A_pf : CorrectDecoder_simpl format_A decode_A.

  Inductive Simple : Type :=
  | C1 : A -> Simple
  | C2 : A -> Simple.

  Definition Simple_Format : FormatM Simple T :=
    Union_Format (Compose_Format format_A (fun s w => s = C1 w))
                 (Compose_Format format_A (fun s w => s = C2 w)).

  (* like len *)
  Definition Simple_tag (s : Simple) :=
    match s with
    | C1 _ => false
    | C2 _ => true
    end.

  Theorem Simple_Decode_correct t
    : {Simple_Decode : _ |
       CorrectDecoder_simpl
         (Restrict_Format (fun s => Simple_tag s = t) Simple_Format)
         Simple_Decode}.
  Proof.
    Admitted.

End SimpleFormat.