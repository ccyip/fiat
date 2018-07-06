Require Import
        Coq.ZArith.BinInt
        ExtrOcamlBasic
        ExtrOcamlNatInt
        ExtrOcamlZInt
        ExtrOcamlString.

Require Import
        Fiat.Computation
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedMonads
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Examples.Protobuf.ProtobufSpec.

Require Import NArith NArithRing.

Import Vectors.Vector.VectorNotations.
Open Scope Tuple_scope.

Definition Timestamp : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int64)) "seconds" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "nanos" 2)
    ].

Definition Timestamp_destruct {A}
           (f : N -> N -> A)
           (msg : PB_Message_denote Timestamp) :=
  f msg!"seconds" msg!"nanos".

Definition PhoneNumber : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "number" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "type" 2)
    ].

Definition PhoneNumber_destruct {A}
           (f : list char -> N -> A)
           (msg : PB_Message_denote PhoneNumber) :=
  f msg!"number" msg!"type".

Definition Person : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "name" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "id" 2);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "email" 3);
      (Build_PB_Field (PB_Repeated (PB_Embedded PhoneNumber)) "phones" 4);
      (Build_PB_Field (PB_Singular (PB_Embedded Timestamp)) "last_updated" 5)
    ].

Definition Person_destruct {A}
           (f : list char -> N -> list char ->
                list (PB_Message_denote PhoneNumber) ->
                option (PB_Message_denote Timestamp) -> A)
           (msg : PB_Message_denote Person)
           : A :=
  f msg!"name" msg!"id" msg!"email" msg!"phones" msg!"last_updated".

Definition AddressBook : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Repeated (PB_Embedded Person)) "people" 1)
    ].

Definition AddressBook_destruct {A}
           (f : list (PB_Message_denote Person) -> A)
           (msg : PB_Message_denote AddressBook) :=
  f msg!"people".

(* :TODO: generalize this and move to extraction.v *)
Definition AddressBook_decode bs :=
  match PB_Message_decode AddressBook bs () with
  | Some (msg, _, _) => Some msg
  | None => None
  end.

(* :TODO: move this to extraction.v *)
Extraction Inline DecodeBindOpt2.
Extraction Inline If_Opt_Then_Else.
Extract Constant whd => "(fun _ w -> ((Int64.logand Int64.one w) = Int64.one))".
Extract Constant wtl => "(fun _ w -> (Int64.shift_right_logical w 1))".
Extract Constant wplus => "(fun _ w w' -> Int64.add w w')".
Extract Constant wmult => "(fun _ w w' -> Int64.mul w w')".
Extract Constant wminus => "(fun _ w w' -> Int64.max (Int64.zero) (Int64.sub w w'))".
Extract Constant weq => "(fun _ w w' -> w = w')".
Extract Constant weqb => "(fun _ w w' -> w = w')".
Extract Constant wlt => "(fun _ w w' -> w < w')".
Extract Constant wlt_dec => "(fun _ w w' -> w < w')".
Extract Constant wand => "(fun _ w w' -> Int64.logand w w')".
Extract Constant wor => "(fun _ w w' -> Int64.logor w w')".
Extract Constant wnot => "(fun _ w -> Int64.lognot w)".
Extract Constant wneg => "(fun _ w w' -> failwith ""Called Wneg"")".
Extract Constant combine => "(fun _ w w' -> failwith ""Using combine"")".
Extract Constant wordToNat => "(fun _ w -> Int64.to_int w)". (* Not ideal *)
Extract Constant natToWord => "(fun _ w -> Int64.of_int w)".
Extract Constant wzero => "(fun _ -> Int64.zero)".
Extract Constant wzero' => "(fun _ -> Int64.zero)".
Extract Constant wones => "(fun n -> Int64.sub (Int64.shift_left Int64.one n) Int64.one)".

Extract Constant wordToN => "(fun _ w -> Int64.to_int w)". (* Not ideal *)

Extract Constant SW_word => "(fun sz b n -> Int64.add (if b then Int64.shift_left Int64.one sz else Int64.zero) n)".

Extract Inductive Word.word =>
int64 ["Int64.zero" "(fun (b, _, w') -> Int64.add (if b then Int64.one else Int64.zero) (Int64.shift_left w' 1))"]
      "failwith ""Destructing an int64""".
Extract Constant encode_word' => "encode_word'_recurse_on_size".

Extract Inlined Constant fst => "fst".
Extract Inlined Constant snd => "snd".
Extraction Inline test_cache.

Extract Inlined Constant char => "int64".
Extract Constant rev => "List.rev".
Extract Constant app => "List.append".
Extract Constant length => "List.length".

Extract Constant N.shiftl => "(lsl)".
Extract Constant N.shiftr => "(lsr)".
Extract Constant N.lor => "(lor)".
Extract Constant N.land => "(land)".
Extract Constant N.eqb => "(==)".
Extract Constant N.eq_dec => "(==)".
Extract Constant N.ltb => "(<)".
Extract Constant N.div2 => "(fun x -> x / 2)".
(* :TODO: Get rid of power and instead use bit operations *)
Extract Constant N.pow => "Batteries.Int.pow".

Extraction "addressbook"
           Vector.to_list Vector.of_list build_aligned_ByteString
           Timestamp_destruct
           PhoneNumber_destruct
           Person_destruct
           AddressBook_destruct
           AddressBook_decode.