Require Import
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Protobuf.ProtobufExtract.

Open Scope Protobuf_scope.

(* The descriptors used in conformance test. *)
Definition NestedMessage : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_int32), "a", 1)].

Definition ForeignMessage : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_int32), "c", 1)].

(* We use compatible types for high-level types that we don't support yet. *)
Definition TestAllTypesProto3 : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_int32), "optional_int32", 1);
   ((PB_Singular (PB_Base PB_int64)), "optional_int64", 2);
   (PB_Singular (PB_Base PB_int32), "optional_uint32", 3);
   (PB_Singular (PB_Base PB_int64), "optional_uint64", 4);
   (PB_Singular (PB_Base PB_int32), "optional_sint32", 5);
   (PB_Singular (PB_Base PB_int64), "optional_sint64", 6);
   (PB_Singular (PB_Base PB_fixed32), "optional_fixed32", 7);
   (PB_Singular (PB_Base PB_fixed64), "optional_fixed64", 8);
   (PB_Singular (PB_Base PB_fixed32), "optional_sfixed32", 9);
   (PB_Singular (PB_Base PB_fixed64), "optional_sfixed64", 10);
   (PB_Singular (PB_Base PB_fixed32), "optional_float", 11);
   (PB_Singular (PB_Base PB_fixed64), "optional_double", 12);
   (PB_Singular (PB_Base PB_int32), "optional_bool", 13);
   (PB_Singular (PB_Base PB_string), "optional_string", 14);
   (PB_Singular (PB_Base PB_string), "optional_bytes", 15);

   (PB_Singular (PB_Embedded NestedMessage), "optional_nested_message", 18);
   (PB_Singular (PB_Embedded ForeignMessage), "optional_foreign_message", 19);
   (PB_Singular (PB_Base PB_int32), "optional_nested_enum", 21);
   (PB_Singular (PB_Base PB_int32), "optional_foreign_enum", 22);

   (PB_Singular (PB_Base PB_string), "optional_string_piece", 24);
   (PB_Singular (PB_Base PB_string), "optional_cord", 25);

   (PB_Repeated (PB_Base PB_int32), "repeated_int32", 31);
   (PB_Repeated (PB_Base PB_int64), "repeated_int64", 32);
   (PB_Repeated (PB_Base PB_int32), "repeated_uint32", 33);
   (PB_Repeated (PB_Base PB_int64), "repeated_uint64", 34);
   (PB_Repeated (PB_Base PB_int32), "repeated_sint32", 35);
   (PB_Repeated (PB_Base PB_int64), "repeated_sint64", 36);
   (PB_Repeated (PB_Base PB_fixed32), "repeated_fixed32", 37);
   (PB_Repeated (PB_Base PB_fixed64), "repeated_fixed64", 38);
   (PB_Repeated (PB_Base PB_fixed32), "repeated_sfixed32", 39);
   (PB_Repeated (PB_Base PB_fixed64), "repeated_sfixed64", 40);
   (PB_Repeated (PB_Base PB_fixed32), "repeated_float", 41);
   (PB_Repeated (PB_Base PB_fixed64), "repeated_double", 42);
   (PB_Repeated (PB_Base PB_int32), "repeated_bool", 43);
   (PB_Repeated (PB_Base PB_string), "repeated_string", 44);
   (PB_Repeated (PB_Base PB_string), "repeated_bytes", 45);

   (PB_Repeated (PB_Embedded NestedMessage), "repeated_nested_message", 48);
   (PB_Repeated (PB_Embedded ForeignMessage), "repeated_foreign_message", 49);
   (PB_Repeated (PB_Base PB_int32), "repeated_nested_enum", 51);
   (PB_Repeated (PB_Base PB_int32), "repeated_foreign_enum", 52);

   (PB_Repeated (PB_Base PB_string), "repeated_string_piece", 54);
   (PB_Repeated (PB_Base PB_string), "repeated_cord", 55)].

Definition testall_encode := PB_Message_encode_impl TestAllTypesProto3.

Definition testall_decode := PB_Message_decode_impl TestAllTypesProto3.

Extraction "testall"
           Vector.to_list Vector.of_list
           build_aligned_ByteString
           testall_encode
           testall_decode.