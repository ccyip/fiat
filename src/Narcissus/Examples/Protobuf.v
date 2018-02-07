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
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Formats.WordOpt.

Import Vectors.VectorDef.VectorNotations.

Inductive PbType : Type :=
| PbInt32 : PbType              (* Fixed-size int32 for now. *)
| PbString : PbType.

(* Consider constraints in name and tag (also inter-constraints). *)
Record PbField := 
  { PbFieldType : PbType;
    PbFieldName : string;
    PbFieldTag : nat }.

Definition PbMessage := Vector.t PbField.

Definition DenotePbType (pt : PbType) : Type :=
  match pt with
  | PbInt32 => word 32 (* nat *)
  | PbString => string
  end.

Definition DenotePbField (pf : PbField) :=
  match pf with
  | {| PbFieldType := type; PbFieldName := name; PbFieldTag := _ |} =>
    (name :: DenotePbType type)%Attribute
  end.

Definition DenotePbMessage {n : nat} (pm : PbMessage n) :=
  @Tuple (BuildHeading (Vector.map DenotePbField pm)).

Definition PbTypeToWireType (pt : PbType) : nat :=
  match pt with
  | PbInt32 => 0
  | PbString => 1
  end.

Definition PbTypeToFormatSpec (pt : PbType) :=
  match pt return (DenotePbType pt) ->
                  CacheFormat -> Comp (ByteString * CacheFormat) with
  | PbInt32 => fun x => format_word x (* (natToWord 32 x) *)
  | PbString => format_string
  end.

Definition format_PbField_spec
           {pf : PbField} (fld : DenotePbType (PbFieldType pf)) :=
        format_word (natToWord 16 (PbFieldTag pf))
  ThenC format_word (natToWord 16 (PbTypeToWireType (PbFieldType pf)))
  ThenC PbTypeToFormatSpec (PbFieldType pf) fld.

(* Open Scope Tuple_scope. *)
(* Definition format_PbMessage_spec *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg: DenotePbMessage pm) := *)
(*   Vector.fold_right (fun pf spec => *)
(*                        ComposeOpt.compose _ (@format_PbField_spec pf msg!(PbFieldName pf)) *)
(*                                spec) *)
(*                     pm (fun e => ret (mempty, e)). *)

(* msg => msg' *)
(* Fixpoint format_PbMessage_spec *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg: DenotePbMessage pm) := *)
(*   match pm with *)
(*   | Vector.nil => fun e => ret (mempty, e) *)
(*   | Vector.cons pf _ pm' => ComposeOpt.compose (@format_PbField_spec pf msg!(PbFieldName pf)) *)
(*                                               (format_PbMessage_spec pm' msg) *)
(*   end. *)

(* Fixpoint format_PbMessage_spec *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg: DenotePbMessage pm) := *)
(*   match pm with *)
(*   | Vector.nil => fun e => ret (mempty, e) *)
(*   | Vector.cons pf n' pm' => ComposeOpt.compose (@format_PbField_spec *)
(*                                        pf (ilist.ith *)
(*                                              msg *)
(*                                              (Fin.R (n-n'-1) (@Fin.F1 n')))) *)
(*                                    (format_PbMessage_spec pm' msg) *)
(*   end. *)

(* Fixpoint format_PbMessage_spec *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg: DenotePbMessage pm) := *)
(*   match pm return DenotePbMessage pm -> CacheFormat -> Comp (ByteString * CacheFormat) with *)
(*   | Vector.nil => fun msg => fun e => ret (mempty, e) *)
(*   | Vector.cons pf _ pm' => fun msg => ComposeOpt.compose (@format_PbField_spec *)
(*                                        pf (ilist2.ilist2_hd msg)) *)
(*                                    (format_PbMessage_spec pm' (ilist2.ilist2_tl msg)) *)
(*   end msg. *)

Lemma TypeEq_for_format_PbMessage_spec : forall {n} (pm : PbMessage n) (pf : PbField) (msg : DenotePbMessage (pf::pm)),
    match AttrList (BuildHeading (Vector.map DenotePbField (pf::pm))) as As in (t _ n)
    return (ilist2.ilist2 As -> Type)
  with
  | [] => fun _ : ilist2.ilist2 [] => unit
  | @Vector.cons _ a n As' => fun _ : ilist2.ilist2 (a :: As') => id a
  end msg = DenotePbType (PbFieldType pf).
Proof.
  intros.
  simpl. unfold id.
  destruct pf as [ty ? ?].
  reflexivity.
Defined.

Fixpoint format_PbMessage_spec
           {n : nat} {pm : PbMessage n}
           (msg : DenotePbMessage pm) {struct pm} : CacheFormat -> Comp (ByteString * CacheFormat).
  refine (match pm return DenotePbMessage pm -> CacheFormat -> Comp (ByteString * CacheFormat) with
  | Vector.nil => fun msg => fun e => ret (mempty, e)
  | Vector.cons pf n' pm' => fun msg => ComposeOpt.compose _
                                      (@format_PbField_spec pf _) (* (ilist2.ilist2_hd msg) *)
                                      (@format_PbMessage_spec n' pm' (ilist2.ilist2_tl msg))
  end msg).
  rewrite <- (TypeEq_for_format_PbMessage_spec pm' pf msg).
  exact (ilist2.ilist2_hd msg).
Defined.

(* Definition format_PbField_spec' *)
(*            {pf : PbField} (fld : DenotePbType (PbFieldType pf)) := *)
(*   [format_word (natToWord 16 (PbFieldTag pf)); *)
(*   format_word (natToWord 16 (PbTypeToWireType (PbFieldType pf))); *)
(*   PbTypeToFormatSpec (PbFieldType pf) fld]. *)

(* (* Fixpoint format_PbMessage_spec_v *) *)
(* (*            {n : nat} {pm : PbMessage n} *) *)
(* (*            (msg : DenotePbMessage pm) {struct pm} : Vector.t (CacheFormat -> Comp (ByteString * CacheFormat)) (3*n). *) *)
(* (*   refine (match pm in (Vector.t _ n) return DenotePbMessage pm -> Vector.t (CacheFormat -> Comp (ByteString * CacheFormat)) (3*n) with *) *)
(* (*   | Vector.nil => fun msg => @Vector.nil _ *) *)
(* (*   | Vector.cons pf n' pm' => fun msg => (@format_PbField_spec' pf _) (* (ilist2.ilist2_hd msg) *) *) *)
(* (*                                       ++ (@format_PbMessage_spec_v n' pm' (ilist2.ilist2_tl msg)) *) *)
(* (*   end msg). *) *)
(* (*   rewrite <- (TypeEq_for_format_PbMessage_spec pm' pf msg). *) *)
(* (*   exact (ilist2.ilist2_hd msg). *) *)
(* (* Defined. *) *)

(* Fixpoint format_PbMessage_spec_v *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg : DenotePbMessage pm) {struct pm} : Vector.t (CacheFormat -> Comp (ByteString * CacheFormat)) (3*n). *)
(*   refine (match pm in (Vector.t _ n) return DenotePbMessage pm -> Vector.t (CacheFormat -> Comp (ByteString * CacheFormat)) (3*n) with *)
(*   | Vector.nil => fun msg => @Vector.nil _ *)
(*   | Vector.cons pf n' pm' => fun msg => _ *)
(*   end msg). *)
(*   replace (3*S n') with (3 + (3*n')) by omega. *)
(*   refine ((@format_PbField_spec' pf _) *)
(*             ++ (@format_PbMessage_spec_v n' pm' (ilist2.ilist2_tl msg))). *)
(*   rewrite <- (TypeEq_for_format_PbMessage_spec pm' pf msg). *)
(*   exact (ilist2.ilist2_hd msg). *)
(* Defined. *)

(* Definition format_PbMessage_spec' *)
(*            {n : nat} {pm : PbMessage n} *)
(*            (msg: DenotePbMessage pm) := *)
(*   Vector.fold_right (fun fmt spec => ComposeOpt.compose _ fmt spec) *)
(*                     (format_PbMessage_spec_v msg) *)
(*                     (fun e => ret (mempty, e)). *)

Open Scope list_scope.
Definition format_PbField_spec'
           {pf : PbField} (fld : DenotePbType (PbFieldType pf)) :=
  [format_word (natToWord 16 (PbFieldTag pf));
  format_word (natToWord 16 (PbTypeToWireType (PbFieldType pf)));
  PbTypeToFormatSpec (PbFieldType pf) fld].

Fixpoint format_PbMessage_spec_v
           {n : nat} {pm : PbMessage n}
           (msg : DenotePbMessage pm) {struct pm} : list (CacheFormat -> Comp (ByteString * CacheFormat)).
  refine (match pm in (Vector.t _ n) return DenotePbMessage pm -> list (CacheFormat -> Comp (ByteString * CacheFormat)) with
  | Vector.nil => fun msg => nil
  | Vector.cons pf n' pm' => fun msg => (@format_PbField_spec' pf _) (* (ilist2.ilist2_hd msg) *)
                                      ++ (@format_PbMessage_spec_v n' pm' (ilist2.ilist2_tl msg))
  end msg).
  rewrite <- (TypeEq_for_format_PbMessage_spec pm' pf msg).
  exact (ilist2.ilist2_hd msg).
Defined.

Definition format_PbMessage_spec'
           {n : nat} {pm : PbMessage n}
           (msg: DenotePbMessage pm) :=
  fold_right (fun fmt spec => ComposeOpt.compose _ fmt spec)
             (fun e => ret (mempty, e))
             (format_PbMessage_spec_v msg).

Open Scope vector_scope.

Definition PbMessage_OK 
           {n : nat} {pm : PbMessage n}
           (msg : DenotePbMessage pm) := True.

Arguments Vector.nth : simpl never.

(* Definition PbMessage_decoder {n : nat} (pm : PbMessage n) *)
(*   : CorrectDecoderFor (@PbMessage_OK _ pm) *)
(*                       (@format_PbMessage_spec' _ pm). *)
(* Proof. *)
(*   unfold format_PbMessage_spec'. *)
(*   unfold PbMessage_OK. *)
(*   simpl. *)
(*   unfold DenotePbMessage. *)
(*   (* Set Printing Implicit. *) *)
(*   unfold Vector.map, DenotePbField, DenotePbType. *)
(*   unfold format_PbMessage_spec_v. *)
(*   unfold PbFieldTag. *)
(*   unfold PbFieldType. *)
(*   unfold PbTypeToWireType. *)
(*   unfold PbTypeToFormatSpec. *)
(*   synthesize_decoder. *)
(* Defined. *)

(* Definition pbmessage_decoder := Eval simpl in proj1_sig PbMessage_decoder. *)

(* Example *)
Open Scope Tuple_scope.

(* Reference *)
(* Definition RefPerson := *)
(*   @Tuple <"id" :: nat, "age" :: nat>. *)
(* Definition RefPerson := *)
(*   @Tuple <"id" :: word 16, "age" :: word 16>. *)
Definition RefPerson :=
  @Tuple <"id" :: word 32, "age" :: word 32>.

(* Definition format_RefPerson_spec (p : RefPerson) := *)
(*   format_word p!"id" *)
(*               ThenC format_word p!"age" *)
(*               DoneC. *)
Definition format_RefPerson_spec (msg : RefPerson) :=
  format_word (natToWord 16 1)
              ThenC format_word (natToWord 16 0)
              ThenC format_word msg!"id"
              ThenC format_word (natToWord 16 2)
              ThenC format_word (natToWord 16 0)
              ThenC format_word msg!"age"
              DoneC.

Definition RefPerson_OK (msg : RefPerson) := True.

(* Set Printing Implicit. *)
(* Set Printing All. *)
Definition RefPerson_decoder
  : CorrectDecoderFor RefPerson_OK format_RefPerson_spec.
Proof.
  (* Set Debug Ltac. *)
  synthesize_decoder.
Defined.

Definition ref_person_decoder := Eval simpl in proj1_sig RefPerson_decoder.

Definition PersonMessage : PbMessage _ :=
  [{| PbFieldType := PbInt32; PbFieldName := "id"; PbFieldTag := 1 |};
     {| PbFieldType := PbInt32; PbFieldName := "age"; PbFieldTag := 2 |}].
Definition PersonFieldId := PersonMessage[@Fin.F1].

Compute (DenotePbMessage PersonMessage).

Definition person : DenotePbMessage PersonMessage :=
  (* ilist.Build_prim_prod 4 (ilist.Build_prim_prod 27 tt). *)
  ilist.Build_prim_prod (natToWord 32 4)
                        (ilist.Build_prim_prod (natToWord 32 27) tt).

Compute person!"id".
Compute DenotePbType (PbFieldType PersonFieldId).

Definition Person_decoder
  : CorrectDecoderFor (@PbMessage_OK _ PersonMessage)
                      (@format_PbMessage_spec' _ PersonMessage).
Proof.
  unfold format_PbMessage_spec'.
  (* unfold PbMessage_OK. *)
  (* simpl. *)
  (* unfold PbFieldTag. *)
  (* unfold PbFieldType. *)
  (* unfold PbTypeToWireType. *)
  (* unfold PbTypeToFormatSpec. *)
  (* unfold DenotePbMessage. *)

  (* unfold PersonMessage. *)
  (* unfold Vector.map, DenotePbField, DenotePbType. *)
  
  (* Set Printing Implicit. *)
  synthesize_decoder.
Defined.

Definition person_decoder := Eval simpl in proj1_sig Person_decoder.

(* Draft *)

(* Ltac Build_nth_IndexBound n A a As As' m ::= *)
Ltac Build_nth_IndexBound n A a As As' m :=
  match n with
  | S ?n' =>
    (let check := constr:(eq_refl : a = Vector.hd As') in (* Check if the terms match *)
     idtac check;
     exact (@Build_IndexBound A _ a As (Fin.R m (@Fin.F1 n'))
                              (@eq_refl A a)))
      ||
      let As'' := eval simpl in (Vector.tl As') in
          Build_nth_IndexBound n' A a As As'' (S m)
  end.

Set Debug Ltac.
Unset Debug Ltac.

Hint Extern 0 (@IndexBound ?A ?n ?a ?As) =>
idtac "Start" A n a As;
match goal with | [|- ?g] => idtac "goal" g end;
let n' := eval compute in n in
    Build_nth_IndexBound n' A a As As 0 : typeclass_instances.

(* Theorem vec_inv : forall A m (v: @Vector.t A (S m)), exists x xs, v = @Vector.cons A x m xs. *)
(* Proof. *)
(*   intros. *)
(*   (* destruct v. *) *)

(* (* Unset Printing Notations. *) *)
(* (* Unset Printing Implicit. *) *)

Fixpoint format_PbMessage_spec'
           {n : nat} {pm : PbMessage n}
           (msg: DenotePbMessage pm) {struct pm} : CacheFormat -> Comp (ByteString * CacheFormat).
  refine (match pm return DenotePbMessage pm -> CacheFormat -> Comp (ByteString * CacheFormat) with
  | Vector.nil => fun msg => fun e => ret (mempty, e)
  | Vector.cons pf n' pm' => fun msg => ComposeOpt.compose _
                                      (@format_PbField_spec pf _) (* msg!(PbFieldName pf) *)
                                      (@format_PbMessage_spec' n' pm' (ilist2.ilist2_tl msg))
  end msg).
  assert (Domain (BuildHeading (Vector.map DenotePbField (pf :: pm')))
                 (ibound (indexb {| bindex := PbFieldName pf;
                                    indexb := {| ibound := Fin.F1;
                                                 boundi := @eq_refl string (PbFieldName pf) |} |}))
          = DenotePbType (PbFieldType pf)).

  exact msg!(PbFieldName pf).