Require Import
        Fiat.Protobuf.ProtobufExtract.

Open Scope Protobuf_scope.

Definition Timestamp : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_int64), "seconds", 1);
   (PB_Singular (PB_Base PB_int32), "nanos", 2)].

Definition PhoneNumber : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_string), "number", 1);
   (PB_Singular (PB_Base PB_int32), "type", 2)].

Definition Person : PB_Descriptor :=
  [(PB_Singular (PB_Base PB_string), "name", 1);
   (PB_Singular (PB_Base PB_int32), "id", 2);
   (PB_Singular (PB_Base PB_string), "email", 3);
   (PB_Repeated (PB_Embedded PhoneNumber), "phones", 4);
   (PB_Singular (PB_Embedded Timestamp), "last_updated", 5)].

Definition AddressBook : PB_Descriptor :=
  [(PB_Repeated (PB_Embedded Person), "people", 1)].

Definition AddressBook_encode := PB_Descriptor_encode_impl AddressBook.

Definition AddressBook_decode := PB_Message_decode_impl AddressBook.

(* Boilerplate for easier access to the message in the extracted code. *)
Require Import
        NArith
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.QueryStructure.Specification.Representation.Tuple.
Open Scope Tuple_scope.

Definition Timestamp_construct
           (seconds : N) (nanos : N) : PB_Descriptor_denote Timestamp :=
  <"seconds" :: seconds,
   "nanos" :: nanos>.

Definition Timestamp_destruct {A}
           (f : N -> N -> A)
           (msg : PB_Descriptor_denote Timestamp) :=
  f msg!"seconds" msg!"nanos".

Definition PhoneNumber_construct
           (number : list char) (type : N) : PB_Descriptor_denote PhoneNumber :=
  <"number" :: number,
   "type" :: type>.

Definition PhoneNumber_destruct {A}
           (f : list char -> N -> A)
           (msg : PB_Descriptor_denote PhoneNumber) :=
  f msg!"number" msg!"type".

Definition Person_construct
           (name : list char) (id : N) (email : list char)
           (phones : list (PB_Descriptor_denote PhoneNumber))
           (last_updated : option (PB_Descriptor_denote Timestamp)) : PB_Descriptor_denote Person :=
  <"name" :: name,
   "id" :: id,
   "email" :: email,
   "phones" :: phones,
   "last_updated" :: last_updated>.

Definition Person_destruct {A}
           (f : list char -> N -> list char ->
                list (PB_Descriptor_denote PhoneNumber) ->
                option (PB_Descriptor_denote Timestamp) -> A)
           (msg : PB_Descriptor_denote Person)
           : A :=
  f msg!"name" msg!"id" msg!"email" msg!"phones" msg!"last_updated".

Definition AddressBook_construct
           (people : list (PB_Descriptor_denote Person)) : PB_Descriptor_denote AddressBook :=
  <"people" :: people>.

Definition AddressBook_destruct {A}
           (f : list (PB_Descriptor_denote Person) -> A)
           (msg : PB_Descriptor_denote AddressBook) :=
  f msg!"people".

Extraction "addressbook"
           Vector.to_list Vector.of_list
           build_aligned_ByteString
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