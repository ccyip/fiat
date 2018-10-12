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
        Fiat.Narcissus.Examples.Protobuf.ProtobufSpec
        Fiat.Narcissus.Examples.Protobuf.ProtobufEncoder
        Fiat.Narcissus.Examples.Protobuf.ProtobufExtract.

Require Import NArith NArithRing.

Import Vectors.Vector.VectorNotations.
Open Scope Tuple_scope.

Definition Timestamp : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int64)) "seconds" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "nanos" 2)
    ].

Definition NestedMessage : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "a" 1)
    ].

Definition ForeignMessage : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "c" 1)
    ].

(* We use compatible types for high-level types that we don't support yet. *)
Definition TestAllTypesProto3 : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_int32" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int64)) "optional_int64" 2);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_uint32" 3);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int64)) "optional_uint64" 4);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_sint32" 5);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int64)) "optional_sint64" 6);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed32)) "optional_fixed32" 7);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed64)) "optional_fixed64" 8);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed32)) "optional_sfixed32" 9);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed64)) "optional_sfixed64" 10);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed32)) "optional_float" 11);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_fixed64)) "optional_double" 12);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_bool" 13);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "optional_string" 14);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "optional_bytes" 15);

      (Build_PB_Field (PB_Singular (PB_Embedded NestedMessage)) "optional_nested_message" 18);
      (Build_PB_Field (PB_Singular (PB_Embedded ForeignMessage)) "optional_foreign_message" 19);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_nested_enum" 21);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "optional_foreign_enum" 22);

      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "optional_string_piece" 24);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "optional_cord" 25);

      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_int32" 31);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int64)) "repeated_int64" 32);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_uint32" 33);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int64)) "repeated_uint64" 34);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_sint32" 35);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int64)) "repeated_sint64" 36);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed32)) "repeated_fixed32" 37);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed64)) "repeated_fixed64" 38);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed32)) "repeated_sfixed32" 39);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed64)) "repeated_sfixed64" 40);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed32)) "repeated_float" 41);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_fixed64)) "repeated_double" 42);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_bool" 43);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_string)) "repeated_string" 44);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_string)) "repeated_bytes" 45);

      (Build_PB_Field (PB_Repeated (PB_Embedded NestedMessage)) "repeated_nested_message" 48);
      (Build_PB_Field (PB_Repeated (PB_Embedded ForeignMessage)) "repeated_foreign_message" 49);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_nested_enum" 51);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_int32)) "repeated_foreign_enum" 52);

      (Build_PB_Field (PB_Repeated (PB_Primitive PB_string)) "repeated_string_piece" 54);
      (Build_PB_Field (PB_Repeated (PB_Primitive PB_string)) "repeated_cord" 55)
    ].

Definition testall_encode := PB_Message_encode_impl TestAllTypesProto3.

Definition testall_decode := PB_Message_decode_impl TestAllTypesProto3.

Extraction "testall"
           Vector.to_list Vector.of_list build_aligned_ByteString
           testall_encode
           testall_decode.