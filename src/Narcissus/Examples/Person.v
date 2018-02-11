Require Import
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Common.BoundedLookup
        Fiat.Common.ilist
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Computation
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.WordOpt.

Import Vectors.VectorDef.VectorNotations.
Open Scope Tuple_scope.

Definition RefPerson :=
  @Tuple <"id" :: word 32, "age" :: word 32>.

Definition format_RefPerson_spec (msg : RefPerson) :=
  format_word (natToWord 16 1)
              ThenC format_word (natToWord 16 0)
              ThenC format_word msg!"id"
              ThenC format_word (natToWord 16 2)
              ThenC format_word (natToWord 16 0)
              ThenC format_word msg!"age"
              DoneC.

Definition RefPerson_OK (msg : RefPerson) := True.

(* Instance monoid : Monoid ByteString := ByteStringQueueMonoid. *)
Lemma AlignedFormatMempty
  : forall ce : CacheFormat,
    refine (ret (mempty, ce))
           (ret (build_aligned_ByteString [], ce)).
Proof.
  intros.
  f_equiv.
  f_equal.
  compute.
  f_equal.
  apply le_uniqueness_proof.
  (* eapply ByteString_f_equal; simpl; *)
  (*   apply Eqdep_dec.eq_rect_eq_dec; intros; eauto using Peano_dec.eq_nat_dec. *)
  (* Grab Existential Variables. *)
  (* reflexivity. *)
  (* reflexivity. *)
Qed.

Definition refine_ref_person_format
  : { numBytes : _ &
    { v : _ &
    { c : _ & forall (p : RefPerson), RefPerson_OK p ->
                                 refine (format_RefPerson_spec p ())
                                        (ret (@build_aligned_ByteString (numBytes p) (v p), c p)) } } }.
Proof.
  unfold format_RefPerson_spec.
  eexists _, _, _; intros.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat32Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat32Char; eauto.
  eapply AlignedFormatMempty.
Defined.

Arguments split1 : simpl never.
Arguments split2 : simpl never.
Arguments weq : simpl never.
Arguments natToWord : simpl never.
Arguments Guarded_Vector_split : simpl never.
Arguments Core.append_word : simpl never.
Definition ref_person_encoder := Eval simpl in (projT1 (projT2 refine_ref_person_format)).

Definition RefPerson_decoder
  : CorrectDecoderFor RefPerson_OK format_RefPerson_spec.
Proof.
  (* Set Debug Ltac. *)
  synthesize_decoder.
Defined.

Definition ref_person_decoder' := Eval simpl in proj1_sig RefPerson_decoder.
Definition ref_person_decoder := Eval simpl in fst ref_person_decoder'.

Definition ref_person : RefPerson :=
  ilist.Build_prim_prod (natToWord 32 4)
                        (ilist.Build_prim_prod (natToWord 32 27) tt).
Example ref_person_ex1 :
  ref_person_decoder
          (build_aligned_ByteString (ref_person_encoder ref_person)) ()
  = Some (ref_person, ByteString_id, ()).
Proof.
  compute.
  repeat progress f_equal.
  apply le_uniqueness_proof.
Qed.

Definition RefPersonNat :=
  @Tuple <"id" :: nat, "age" :: nat>.

Definition format_RefPersonNat_spec (msg : RefPersonNat) :=
  format_word (natToWord 16 1)
              ThenC format_word (natToWord 16 0)
              ThenC format_nat 32 msg!"id"
              ThenC format_word (natToWord 16 2)
              ThenC format_word (natToWord 16 0)
              ThenC format_nat 32 msg!"age"
              DoneC.

Definition RefPersonNat_OK (msg : RefPersonNat) :=
  lt msg!"id" (pow2 32) /\ lt msg!"age" (pow2 32).

Definition refine_ref_person_nat_format
  : { numBytes : _ &
    { v : _ &
    { c : _ & forall (p : RefPersonNat), RefPersonNat_OK p ->
                                 refine (format_RefPersonNat_spec p ())
                                        (ret (@build_aligned_ByteString (numBytes p) (v p), c p)) } } }.
Proof.
  unfold format_RefPersonNat_spec.
  eexists _, _, _; intros.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat32Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat2Char; eauto.
  eapply AlignedFormat32Char; eauto.
  eapply AlignedFormatMempty.
Defined.

Arguments split1 : simpl never.
Arguments split2 : simpl never.
Arguments weq : simpl never.
Arguments natToWord : simpl never.
Arguments Guarded_Vector_split : simpl never.
Arguments Core.append_word : simpl never.
Definition ref_person_nat_encoder := Eval simpl in (projT1 (projT2 refine_ref_person_nat_format)).

(* Opaque pow2. *)
Arguments pow2 : simpl never.

Definition RefPersonNat_decoder
  : CorrectDecoderFor RefPersonNat_OK format_RefPersonNat_spec.
Proof.
  synthesize_decoder.
Defined.

Definition ref_person_nat_decoder' := Eval simpl in proj1_sig RefPersonNat_decoder.
Definition ref_person_nat_decoder := Eval simpl in fst ref_person_nat_decoder'.

Definition ref_person_nat : RefPersonNat :=
  ilist.Build_prim_prod 4
                        (ilist.Build_prim_prod 27 tt).
Example ref_person_nat_ex1 :
  ref_person_nat_decoder
          (build_aligned_ByteString (ref_person_nat_encoder ref_person_nat)) ()
  = Some (ref_person_nat, ByteString_id, ()).
Proof.
  compute.
  repeat progress f_equal.
  apply le_uniqueness_proof.
Qed.
