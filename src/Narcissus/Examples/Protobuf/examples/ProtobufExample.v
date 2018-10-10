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

Definition Timestamp_construct
           (seconds : N) (nanos : N) : PB_Message_denote Timestamp :=
  <"seconds" :: seconds,
   "nanos" :: nanos>.

Definition Timestamp_destruct {A}
           (f : N -> N -> A)
           (msg : PB_Message_denote Timestamp) :=
  f msg!"seconds" msg!"nanos".

Definition PhoneNumber : PB_Message :=
  Build_PB_Message [
      (Build_PB_Field (PB_Singular (PB_Primitive PB_string)) "number" 1);
      (Build_PB_Field (PB_Singular (PB_Primitive PB_int32)) "type" 2)
    ].

Definition PhoneNumber_construct
           (number : list char) (type : N) : PB_Message_denote PhoneNumber :=
  <"number" :: number,
   "type" :: type>.

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

Definition Person_construct
           (name : list char) (id : N) (email : list char)
           (phones : list (PB_Message_denote PhoneNumber))
           (last_updated : option (PB_Message_denote Timestamp)) : PB_Message_denote Person :=
  <"name" :: name,
   "id" :: id,
   "email" :: email,
   "phones" :: phones,
   "last_updated" :: last_updated>.

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

Definition AddressBook_construct
           (people : list (PB_Message_denote Person)) : PB_Message_denote AddressBook :=
  <"people" :: people>.

Definition AddressBook_destruct {A}
           (f : list (PB_Message_denote Person) -> A)
           (msg : PB_Message_denote AddressBook) :=
  f msg!"people".

Definition AddressBook_encode := PB_Message_encode_impl AddressBook.

Definition AddressBook_decode := PB_Message_decode_impl AddressBook.

Extraction "addressbook"
           Vector.to_list Vector.of_list build_aligned_ByteString
           Timestamp_destruct
           PhoneNumber_destruct
           Person_destruct
           AddressBook_destruct
           Timestamp_construct
           PhoneNumber_construct
           Person_construct
           AddressBook_construct
           AddressBook_encode
           AddressBook_decode.