Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.Common.SumType
        Fiat.Common.EnumType
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Computation
        Fiat.Narcissus.BinLib
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeCheckSum
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Automation.AlignedAutomation.
Require Import Fiat.Narcissus.Examples.TutorialPrelude.
Require Import Bedrock.Word.

Import Vectors.VectorDef.VectorNotations.
Open Scope string_scope.
Open Scope format_scope.

(* Our source data type for IP packets. *)
Record IPv4_Packet :=
  { TotalLength : word 16;
    ID : word 16;
    DF : bool; (* Don't fragment flag *)
    MF : bool; (*  Multiple fragments flag *)
    FragmentOffset : word 13;
    TTL : word 8;
    Protocol : EnumType ["ICMP"; "TCP"; "UDP"];
    SourceAddress : word 32;
    DestAddress : word 32;
    Options : list (word 32) }.

(* Protocol Numbers from [RFC5237]*)
Definition ProtocolTypeCodes : Vector.t (word 8) 3 :=
  [WO~0~0~0~0~0~0~0~1; (* ICMP: 1*)
     WO~0~0~0~0~0~1~1~0; (* TCP:  6*)
     WO~0~0~0~1~0~0~0~1  (* UDP:  17*)
  ].

Definition IPv4_Packet_Format : FormatM IPv4_Packet ByteString :=
  (format_nat 4 ◦ (constant 4)
               ++ format_nat 4 ◦ (plus 5) ◦ @length _ ◦ Options
               ++ format_unused_word 8 (* TOS Field! *)
               ++ format_word ◦ TotalLength
               ++ format_word ◦ ID
               ++ format_unused_word 1 (* Unused flag! *)
               ++ format_bool ◦ DF
               ++ format_bool ◦ MF
               ++ format_word ◦ FragmentOffset
               ++ format_word ◦ TTL
               ++ format_enum ProtocolTypeCodes ◦ Protocol)
ThenChecksum IPChecksum_Valid OfSize 16 ThenCarryOn (format_word ◦ SourceAddress
               ++ format_word ◦ DestAddress
               ++ format_list format_word ◦ Options).

Definition IPv4_Packet_OK (ipv4 : IPv4_Packet) :=
  lt (|ipv4.(Options)|) 11 /\
  lt (20 + 4 * |ipv4.(Options)|) (wordToNat ipv4.(TotalLength)).

Ltac new_encoder_rules ::=
  match goal with
    |- CorrectAlignedEncoder (_ ThenChecksum _ OfSize _ ThenCarryOn _) _ =>
    eapply @CorrectAlignedEncoderForIPChecksumThenC
  end.

Ltac apply_new_combinator_rule ::=
  match goal with
  | H : cache_inv_Property ?mnd _
    |- CorrectDecoder _ _ _ _ (?fmt1 ThenChecksum _ OfSize _ ThenCarryOn ?format2) _ _ _ =>
    eapply compose_IPChecksum_format_correct' with (format1 := fmt1);
    [ exact H
    | repeat calculate_length_ByteString
    | repeat calculate_length_ByteString
    | solve_mod_8
    | solve_mod_8
    | normalize_format; apply_rules
    | normalize_format; apply_rules
    | solve_Prefix_Format
    ]
  end.

Let enc_dec : EncoderDecoderPair IPv4_Packet_Format IPv4_Packet_OK.
Proof. derive_encoder_decoder_pair. Defined.

Let IPv4_encoder :=  encoder_impl enc_dec.
Let IPv4_decoder := decoder_impl enc_dec.

Section BP.
  Local Opaque ByteBuffer.of_vector.
  Local Transparent weqb.
  Local Transparent natToWord.
  (* Some example uses of the encoder and decoder functions. *)
  (* A binary version of a packet, sourced directly from the web. *)
  Definition bin_pkt : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;243;159;192;168;222;10;192;168;222;1;0;0;0;0]).

  Definition bin_pkt' : ByteBuffer.t _ :=
    Eval compute in ByteBuffer.of_vector (Vector.map (@natToWord 8) [69;0;100;0;0;0;0;0;38;1;0;0;192;168;222;10;192;168;222;1;0;0;0;0]).
End BP.

(* An source version of a packet, different from binary packet above. *)
Definition pkt :=
  {| TotalLength := WO~0~1~1~1~0~1~0~0~0~0~0~0~0~0~0~0;
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Definition bad_pkt :=
  {| TotalLength := wzero _; (* length is too short *)
     ID := wones _;
     DF := false;
     MF := false;
     FragmentOffset := wzero _;
     TTL := WO~0~0~1~0~0~1~1~0;
     Protocol := Fin.F1;
     SourceAddress := WO~1~0~0~1~1~1~1~1~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     DestAddress := WO~0~0~0~0~1~0~1~0~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0;
     Options := [ ]%list |}.

Eval vm_compute in (IPv4_decoder _ bin_pkt).

Local Transparent natToWord.
Local Transparent weqb.
(* This should succeed, *)
Eval compute in
    Ifopt (IPv4_encoder _ pkt (initialize_Aligned_ByteString 100))
  as bs Then IPv4_decoder _ (fst (fst bs))
        Else None.
(* and it does! *)

(* This should fail because the total length field is too short, *)
Eval compute in
    Ifopt (IPv4_encoder _ bad_pkt (initialize_Aligned_ByteString 100))
  as bs Then IPv4_decoder _ (fst (fst bs))
        Else None.
(* and it does! *)

(* Some addition checksum sanity checks. *)
Compute
  match IPv4_decoder _ bin_pkt with
  | Some (p, _, _) => Some ((wordToN p.(SourceAddress)), wordToN p.(DestAddress))
  | None => None
  end.

Definition pkt' := {|
                    TotalLength := WO~0~1~1~0~0~1~0~0~0~0~0~0~0~0~0~0;
                    ID := WO~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    DF := false;
                    MF := false;
                    FragmentOffset := WO~0~0~0~0~0~0~0~0~0~0~0~0~0;
                    TTL := WO~0~0~1~0~0~1~1~0;
                    Protocol := Fin.F1;
                    SourceAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~1~0~1~0;
                    DestAddress := WO~1~1~0~0~0~0~0~0~1~0~1~0~1~0~0~0~1~1~0~1~1~1~1~0~0~0~0~0~0~0~0~1;
                    Options := [] |}.

Goal match IPv4_encoder _ pkt' (initialize_Aligned_ByteString 24) with
     | Some (p, _, _) => p = bin_pkt
     | None => True
     end.
  compute.
  reflexivity.
Qed.

(* For use in TestInfrastructure.v *)
Definition IPv4_encoder_impl {sz} v r :=
Eval simpl in (projT1 (enc enc_dec) sz v 0 r tt).
Definition IPv4_decoder_impl {sz} v :=
Eval simpl in (projT1 (dec enc_dec) sz v 0 tt).
