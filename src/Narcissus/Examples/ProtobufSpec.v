Require Import
        Coq.ZArith.BinInt
        Coq.Strings.String
        Coq.Sets.Image
        Coq.Vectors.Vector
        Coq.omega.Omega
        Coq.Logic.Eqdep_dec.

Require Import
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.Common
        Fiat.CommonEx
        Fiat.Common.BoundedLookup
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.ilist2
        Fiat.Common.Tactics.CacheStringConstant
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Sig
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedList
        Fiat.Narcissus.BinLib.AlignedDecoders
        Fiat.Narcissus.Formats.Option
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Formats.SizedListOpt
        Fiat.Narcissus.Formats.Bool
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.NatOpt
        Fiat.Narcissus.Formats.Vector
        Fiat.Narcissus.Formats.EnumOpt
        Fiat.Narcissus.Formats.SumTypeOpt
        Fiat.Narcissus.Formats.VarintOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver.

Local Arguments natToWord : simpl never.
Local Arguments NToWord : simpl never.
Local Arguments wordToN : simpl never.
Local Arguments pow2 : simpl never.
Local Arguments weqb : simpl never.
Local Arguments N.shiftl : simpl never.
Local Arguments N.shiftr : simpl never.
Local Arguments N.lor : simpl never.
Local Arguments N.land : simpl never.
Local Arguments CacheDecode : simpl never.

Section LengthDelimited.

  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Variable A_predicate : A -> Prop.
  Variable A_predicate_rest : A -> B -> Prop.
  Variable A_format : FormatM A B.
  Variable A_decode : DecodeM A B.
  Variable A_cache_inv : CacheDecode -> Prop.
  Variable A_format_sz_eq : forall x b1 b2 ce1 ce1' ce2 ce2', A_format x ce1 ↝ (b1, ce1') ->
                                                         A_format x ce2 ↝ (b2, ce2') ->
                                                         bin_measure b1 = bin_measure b2.
  Variable A_format_byte : forall d b ce ce', A_format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
  Variable A_decode_lt : forall b cd x b' cd', A_decode b cd = Some (x, b', cd') -> lt_B b' b.
  Variable A_decode_correct : CorrectDecoder monoid A_predicate A_predicate_rest A_format A_decode A_cache_inv.

  Definition PB_LengthDelimited_format
    : FormatM (list A) B :=
    (fun xs ce =>
       `(b1, ce1) <- SizedList_format A_format xs ce;
         `(b2, _) <- Varint_format (N.of_nat ((bin_measure b1) / 8)) ce;
         ret (mappend b2 b1, ce1))%comp.

Definition PB_LengthDelimited_decode
  : DecodeM (list A) B :=
  fun b cd =>
    `(sz, b1, cd1) <- (`(x, b1, cd1) <- Varint_decode b cd;
                        Some (N.to_nat x, b1, cd1));
      SizedList_decode A_decode A_decode_lt
                       (sz * 8) b1 cd.

Local Arguments Nat.div : simpl never.
Theorem PB_LengthDelimited_decode_correct
        (A_cache_inv_OK : cache_inv_Property A_cache_inv (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder monoid
                   (fun xs => forall x, In x xs -> A_predicate x)
                   (SizedList_predicate_rest A_predicate_rest A_format)
                   PB_LengthDelimited_format PB_LengthDelimited_decode A_cache_inv.
Proof.
  unfold PB_LengthDelimited_format, PB_LengthDelimited_decode.
  split; intros. {
    computes_to_inv2.
    pose proof (Varint_decode_correct (P:=A_cache_inv)) as Hv.
    eapply fun_compose_format_correct
      with (predicate:=fun _ => True) (predicate_rest:=fun _ _ => True) (im:=fun _ => true)
      in Hv.
    edestruct Hv as [[? [? [? ?]]] _]; eauto. clear H4 H5.
    edestruct (SizedList_decode_correct (A:=A)) as [[? [? [? ?]]] _]; try apply H2; eauto.
    intuition. eapply SizedList_format_sz_eq; eauto.
    eexists. repeat split; eauto.
    rewrite <- mappend_assoc. rewrite H3.
    simpl. rewrite Nat.mul_comm.
    assert (bin_measure b0 mod 8 = 0) as L. {
      eapply SizedList_format_byte; eauto.
    }
    apply Nat.div_exact in L; eauto. rewrite <- L; eauto.
    all : auto.
    intros. apply Nnat.Nat2N.id.
    intros. simpl. econstructor. intuition. symmetry. apply Nnat.N2Nat.id.
  } {
    decode_opt_to_inv.
    subst.
    pose proof (Varint_decode_correct (P:=A_cache_inv)) as Hv.
    eapply fun_compose_format_correct
      with (predicate:=fun _ => True) (predicate_rest:=fun _ _ => True) (im:=fun _ => true)
      in Hv.
    edestruct Hv as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
    rewrite H1. simpl. reflexivity.
    edestruct (SizedList_decode_correct (A:=A)) as [_ [? [? [? [? [? [[? ?] ?]]]]]]]; try apply H2; eauto.
    split; eauto.
    eexists _, _. repeat split; eauto.
    computes_to_econstructor; eauto.
    computes_to_econstructor; eauto.
    apply H11 in H9. simpl fst. rewrite H9. rewrite Nat.div_mul by auto. eauto.
    simpl fst. rewrite <- mappend_assoc. subst. reflexivity.
    all : auto.
    intros. apply Nnat.Nat2N.id.
    intros. simpl. econstructor. intuition. symmetry. apply Nnat.N2Nat.id.
  }
Qed.

Theorem PB_LengthDelimited_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_LengthDelimited_format d ce1 ↝ (b1, ce1') ->
    PB_LengthDelimited_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_LengthDelimited_format. intros.
  computes_to_inv2. rewrite !mappend_measure.
  assert (bin_measure b4 = bin_measure b0). {
    eapply SizedList_format_sz_eq; eauto.
  }
  rewrite H1 in *.
  erewrite Varint_format_sz_eq; eauto.
Qed.

Theorem PB_LengthDelimited_decode_lt
  : forall b cd d b' cd',
    PB_LengthDelimited_decode b cd = Some (d, b', cd') -> lt_B b' b.
Proof.
  unfold PB_LengthDelimited_decode. intros.
  decode_opt_to_inv.
  apply Varint_decode_lt in H.
  apply SizedList_decode_le in H0.
  unfold lt_B, le_B in *. subst. omega.
Qed.

End LengthDelimited.

Theorem PB_LengthDelimited_format_byte
        {A : Type} (A_format : FormatM A ByteString)
        (A_format_byte : forall d b ce ce', A_format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0)
  : forall d b ce ce',
    PB_LengthDelimited_format A_format d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_LengthDelimited_format.
  intros. computes_to_inv2.
  rewrite @mappend_measure.
  rewrite <- Nat.add_mod_idemp_l by auto.
  rewrite <- Nat.add_mod_idemp_r by auto.
  erewrite Varint_format_byte; eauto.
  erewrite SizedList_format_byte; eauto.
Qed.

Inductive PB_WireType : Set :=
| PB_Varint : PB_WireType
| PB_32bit : PB_WireType
| PB_64bit : PB_WireType
| PB_LengthDelimited : PB_WireType.

Definition PB_WireType_eq_dec (w1 w2 : PB_WireType)
  : {w1 = w2} + {w1 <> w2}.
Proof.
  decide equality.
Defined.
Arguments PB_WireType_eq_dec : simpl never.

Definition PB_WireType_denote (wty : PB_WireType) : Type :=
  match wty with
  | PB_Varint => N
  | PB_32bit => word 32
  | PB_64bit => word 64
  | PB_LengthDelimited => list char
  end.

Definition PB_WireType_val (wty : PB_WireType) : N :=
  match wty with
  | PB_Varint => 0
  | PB_32bit => 5
  | PB_64bit => 1
  | PB_LengthDelimited => 2
  end.

Definition PB_WireType_val_inv (n : N)
  : PB_WireType + {forall wty, PB_WireType_val wty <> n}.
Proof.
  refine
    (match n with
     | 0 => inleft PB_Varint
     | 5 => inleft PB_32bit
     | 1 => inleft PB_64bit
     | 2 => inleft PB_LengthDelimited
     | _ => inright _
     end)%N;
    abstract (destruct wty; inversion 1).
Defined.

Theorem PB_WireType_val_inv_correct (wty : PB_WireType)
  : PB_WireType_val_inv (PB_WireType_val wty) = inleft wty.
Proof.
  destruct wty; eauto.
Qed.

Theorem PB_WireType_val_inv_correct' (w : N)
  : forall wty, PB_WireType_val_inv w = inleft wty -> PB_WireType_val wty = w.
Proof.
  intros. unfold PB_WireType_val_inv in *.
  repeat match goal with
  | H : match ?w with _ => _ end = _ |- _ => destruct w; injections; auto; try easy
  end.
Qed.

Theorem PB_WireType_val_3bits (wty : PB_WireType)
  : N.lt (N.log2 (PB_WireType_val wty)) 3%N.
Proof.
  destruct wty; easy.
Qed.

Definition PB_WireType_default (wty : PB_WireType) : PB_WireType_denote wty :=
  match wty with
  | PB_Varint => 0%N
  | PB_32bit => wzero 32
  | PB_64bit => wzero 64
  | PB_LengthDelimited => []
  end.

Definition PB_WireType_format (wty : PB_WireType)
  : FormatM (PB_WireType_denote wty) ByteString :=
  match wty with
  | PB_32bit => format_word
  | PB_64bit => format_word
  | PB_Varint => Varint_format
  | PB_LengthDelimited => PB_LengthDelimited_format format_word
  end.

Definition PB_WireType_decoder
           (wty : PB_WireType)
  : { decode : _ |
      forall {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
        CorrectDecoder _
                       (fun _ => True)
                       (fun _ _ => True)
                       (PB_WireType_format wty) decode P }.
Proof.
  let d := fill_ind_h
             (PB_WireType_rect
                (fun pty => DecodeM (PB_WireType_denote pty)
                                 ByteString)) in
  refine (exist _ (d wty) _).

  intros; destruct wty; simpl;
    repeat decode_step idtac.
  apply Varint_decode_correct; repeat decode_step idtac.
  eapply shrink_format_correct_True; eauto.
  apply PB_LengthDelimited_decode_correct; repeat decode_step idtac.
  apply word_format_sz_eq. intros. eapply word_format_byte; eauto; eauto.
  intuition. intros. apply SizedList_predicate_rest_True.
  Grab Existential Variables.
  apply decode_word_lt.
Defined.

Definition PB_WireType_decode (wty : PB_WireType) :=
  Eval simpl in proj1_sig (PB_WireType_decoder wty).

Theorem PB_WireType_decode_correct (wty : PB_WireType)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder
      _ (fun _ => True) (fun _ _ => True)
      (PB_WireType_format wty) (PB_WireType_decode wty) P.
Proof.
  apply (proj2_sig (PB_WireType_decoder wty)). auto.
Qed.

Theorem PB_WireType_format_sz_eq (wty : PB_WireType)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_WireType_format wty d ce1 ↝ (b1, ce1') ->
    PB_WireType_format wty d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_WireType_format; intros.
  destruct wty.
  eapply Varint_format_sz_eq; eauto.
  eapply word_format_sz_eq; eauto.
  eapply word_format_sz_eq; eauto.
  eapply PB_LengthDelimited_format_sz_eq; eauto.
  eapply word_format_sz_eq; eauto.
Qed.

Theorem PB_WireType_format_byte (wty : PB_WireType)
  : forall d b ce ce',
    PB_WireType_format wty d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_WireType_format.
  destruct wty; intros.
  eapply Varint_format_byte; eauto.
  eapply word_format_byte; eauto; eauto.
  eapply word_format_byte; eauto; eauto.
  eapply PB_LengthDelimited_format_byte; eauto.
  intros. eapply word_format_byte; eauto; eauto.
Qed.

Theorem PB_WireType_decode_lt (wty : PB_WireType)
  : forall (b : ByteString) (cd : CacheDecode) (d : PB_WireType_denote wty)
      (b' : ByteString) (cd' : CacheDecode),
    PB_WireType_decode wty b cd = Some (d, b', cd') -> lt_B b' b.
Proof.
  intros. destruct wty; simpl in *.
  eapply Varint_decode_lt; eauto.
  eapply decode_word_lt; eauto.
  eapply decode_word_lt; eauto.
  eapply PB_LengthDelimited_decode_lt; eauto.
Qed.

Inductive PB_PrimitiveType : Set :=
| PB_fixed32 : PB_PrimitiveType
| PB_fixed64 : PB_PrimitiveType
| PB_int32 : PB_PrimitiveType
| PB_int64 : PB_PrimitiveType
(* | PB_sfixed32 : PB_PrimitiveType *)
(* | PB_sfixed64 : PB_PrimitiveType *)
(* | PB_bool : PB_PrimitiveType *)
| PB_string : PB_PrimitiveType
.

Definition PB_PrimitiveType_toWireType (pty : PB_PrimitiveType) : PB_WireType :=
  match pty with
  | PB_fixed32 => PB_32bit
  | PB_fixed64 => PB_64bit
  | PB_int32 => PB_Varint
  | PB_int64 => PB_Varint
  | PB_string => PB_LengthDelimited
  end.

Definition PB_PrimitiveType_denote (pty : PB_PrimitiveType) : Type :=
  PB_WireType_denote (PB_PrimitiveType_toWireType pty).
Arguments PB_PrimitiveType_denote /.

Definition PB_PrimitiveType_default (pty : PB_PrimitiveType) : PB_PrimitiveType_denote pty :=
  PB_WireType_default (PB_PrimitiveType_toWireType pty).
Arguments PB_PrimitiveType_default /.

Inductive PB_SingularType : Set :=
| PB_Primitive : PB_PrimitiveType -> PB_SingularType
| PB_Embedded : PB_Message -> PB_SingularType

with PB_Type : Set :=
     | PB_Singular : PB_SingularType -> PB_Type
     | PB_Repeated : PB_SingularType -> PB_Type

with PB_Field : Set :=
     | Build_PB_Field : PB_Type -> string -> N -> PB_Field

with PB_Message : Set :=
     | Build_PB_Message : forall {n}, Vector.t PB_Field n -> PB_Message.

Definition PB_FieldType (fld : PB_Field) := let (ty, _, _) := fld in ty.
Definition PB_FieldName (fld : PB_Field) := let (_, name, _) := fld in name.
Definition PB_FieldTag (fld : PB_Field) := let (_, _, tag) := fld in tag.

Definition PB_Desc := Vector.t PB_Field.

Definition PB_MessageLen (desc : PB_Message) :=
  let (n, _) := desc in n.

Definition PB_MessageDesc (desc : PB_Message) :=
  let (_, v) return (Vector.t _ (PB_MessageLen desc)) := desc in v.

Definition PB_Message_tags (desc : PB_Message) :=
  Vector.map PB_FieldTag (PB_MessageDesc desc).

Definition PB_Message_heading' denote (desc : PB_Message) :=
  BuildHeading (Vector.map denote (PB_MessageDesc desc)).
Arguments PB_Message_heading' /.

Fixpoint PB_Type_denote (ty : PB_Type) : Type :=
  match ty with
  | PB_Singular sty =>
    match sty with
    | PB_Primitive pty => PB_PrimitiveType_denote pty
    | PB_Embedded desc => option (PB_Message_denote desc)
    end
  | PB_Repeated sty =>
    match sty with
    | PB_Primitive pty => list (PB_PrimitiveType_denote pty)
    | PB_Embedded desc => list (PB_Message_denote desc)
    end
  end

with PB_Field_denote (fld : PB_Field) : Attribute :=
       ((PB_FieldName fld) :: PB_Type_denote (PB_FieldType fld))%Attribute

with PB_Message_denote (desc : PB_Message) : Type :=
       @Tuple (PB_Message_heading' PB_Field_denote desc).

Definition PB_Message_heading := PB_Message_heading' PB_Field_denote.

Definition PB_Type_default (ty : PB_Type) : PB_Type_denote ty :=
  match ty with
  | PB_Singular sty =>
    match sty with
    | PB_Primitive pty => PB_PrimitiveType_default pty
    | PB_Embedded _ => None
    end
  | PB_Repeated sty =>
    match sty with
    | PB_Primitive _ => nil
    | PB_Embedded _ => nil
    end
  end.

Fixpoint PB_Message_default' {n} (desc : PB_Desc n) : PB_Message_denote (Build_PB_Message desc).
Proof.
  refine
    (match desc return (PB_Message_denote (Build_PB_Message desc)) with
     | Vector.nil => inil2 (B:=id)
     | Vector.cons fld _ desc' =>
       icons2 (B:=id) _ (PB_Message_default' _ desc')
     end).
  destruct fld as [ty ? ?].
  exact (PB_Type_default ty).
Defined.

Definition PB_Message_default (desc : PB_Message) := PB_Message_default' (PB_MessageDesc desc).

Definition PB_FieldTag_OK (t : N) :=
  ((1 <= t <= 18999) \/ (20000 <= t <= 536870911))%N.

Definition PB_FieldName_OK (n : string) :=
  n <> EmptyString.

Definition PB_Field_OK (fld : PB_Field) :=
  PB_FieldName_OK (PB_FieldName fld) /\
  PB_FieldTag_OK (PB_FieldTag fld).

(* :TODO: abstract out this proof as ltac. *)
Lemma PB_Message_tags_correct (desc : PB_Message)
  : forall i, Vector.nth (PB_Message_tags desc) i
         = PB_FieldTag (Vector.nth (PB_MessageDesc desc) i).
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros.
    + reflexivity.
    + apply IHdesc.
Qed.

Lemma PB_denote_type_eq (desc : PB_Message) (i : Fin.t (PB_MessageLen desc))
  : PB_Type_denote (PB_FieldType (Vector.nth (PB_MessageDesc desc) i))
    = Domain (PB_Message_heading desc) i.
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Defined.

Lemma PB_Message_default_correct (desc : PB_Message)
  : forall (i : Fin.t (PB_MessageLen desc)),
    type_cast (PB_denote_type_eq desc i)
              (PB_Type_default (PB_FieldType (Vector.nth (PB_MessageDesc desc) i)))
    = ith2 (PB_Message_default desc) i.
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Qed.

Definition PB_Message_tags_nodup (desc : PB_Message) :=
  forall i1 i2 : Fin.t (PB_MessageLen desc),
    Vector.nth (PB_Message_tags desc) i1 = Vector.nth (PB_Message_tags desc) i2 ->
    i1 = i2.

Definition PB_Message_names_nodup (desc : PB_Message) :=
  forall i1 i2 : Fin.t (PB_MessageLen desc),
    PB_FieldName (Vector.nth (PB_MessageDesc desc) i1) = PB_FieldName (Vector.nth (PB_MessageDesc desc) i2) ->
    i1 = i2.

Definition PB_Message_OK (desc : PB_Message) :=
  Vector.Forall PB_Field_OK (PB_MessageDesc desc) /\
  PB_Message_tags_nodup desc /\ PB_Message_names_nodup desc.

Definition BoundedTag (desc : PB_Message) :=
  BoundedIndex (PB_Message_tags desc).

Record UnboundedIndex {A} {n : nat} (Bound : Vector.t A n) :=
  { uindex : A;
    uboundi : ~ Vector.In uindex Bound
  }.

Global Arguments uindex {A n Bound} u.

Definition UnboundedTag (desc : PB_Message) :=
  UnboundedIndex (PB_Message_tags desc).

Theorem BoundedTag_inj (desc : PB_Message)
  : PB_Message_OK desc ->
    forall t1 t2 : BoundedTag desc,
      bindex t1 = bindex t2 -> t1 = t2.
Proof.
  unfold PB_Message_OK, PB_Message_tags_nodup.
  destruct desc as [n desc].
  intros [_ [? _]]; intros. destruct t1, t2. destruct indexb, indexb0.
  simpl in *. subst. apply H in H0. subst. reflexivity.
Qed.

Lemma vector_in_fin {A} {n} (v : Vector.t A n)
  : forall a : A, Vector.In a v -> exists i, Vector.nth v i = a.
Proof.
  intros. induction H.
  - exists Fin.F1. auto.
  - destruct IHIn. exists (Fin.FS x0).
    auto.
Qed.

Theorem PB_Field_inj (desc : PB_Message)
  : PB_Message_OK desc ->
    forall fld1 fld2 : PB_Field,
      Vector.In fld1 (PB_MessageDesc desc) -> Vector.In fld2 (PB_MessageDesc desc) ->
      PB_FieldTag fld1 = PB_FieldTag fld2 ->
      fld1 = fld2.
Proof.
  unfold PB_Message_OK, PB_Message_tags_nodup.
  destruct desc as [n desc].
  intros [_ [? _]]; intros.
  destruct (vector_in_fin _ _ H0).
  destruct (vector_in_fin _ _ H1).
  subst.
  f_equal. apply H.
  rewrite !PB_Message_tags_correct.
  assumption.
Qed.

Lemma vector_in {A} {n} (v : Vector.t A n)
  : forall i,  Vector.In (Vector.nth v i) v.
Proof.
  intros. induction i.
  - subst. revert n v. apply caseS. intros.
    simpl. constructor.
  - subst. revert i IHi. pattern n, v. apply caseS.
    intros. simpl in *. constructor. apply IHi.
Qed.

Theorem BoundedTag_in (desc : PB_Message)
  : forall t1 : BoundedTag desc, Vector.In (bindex t1) (PB_Message_tags desc).
Proof.
  intros. destruct t1. destruct indexb. simpl in *.
  subst. eapply vector_in; eauto.
Qed.

Fixpoint PB_Message_boundedTag' {n} (tags : Vector.t N n) (m : N)
  : {ibound : _ | Vector.nth tags ibound = m} + {~ Vector.In m tags}.
Proof.
  refine
    (match tags with
     | Vector.nil => inright _
     | Vector.cons t n' tags' =>
       if N.eq_dec t m then
         inleft (exist _ Fin.F1 _)
       else
         match PB_Message_boundedTag' n' tags' m with
         | inleft (exist i _) =>
           inleft (exist _ (Fin.FS i) _)
         | inright _ => inright _
         end
     end); auto.
  - abstract inversion 1.
  - abstract
      (inversion 1; auto; existT_eq_dec;
       subst; congruence).
Defined.

Definition PB_Message_boundedTag (desc : PB_Message) (m : N)
  : (BoundedTag desc) + (UnboundedTag desc) :=
  match PB_Message_boundedTag' (PB_Message_tags desc) m with
  | inleft (exist i pf) => inl {| bindex := m; indexb := {| ibound := i; boundi := pf |} |}
  | inright pf => inr {| uindex := m; uboundi := pf |}
  end.

Theorem PB_Message_boundedTag_correct (desc : PB_Message) (m : N)
  : forall tag, PB_Message_boundedTag desc m = inl tag -> bindex tag = m.
Proof.
  unfold PB_Message_boundedTag.
  intros. destruct PB_Message_boundedTag'; try easy.
  destruct s. inversion H. reflexivity.
Qed.

Theorem PB_Message_boundedTag_correct' (desc : PB_Message) (m : N)
  : forall tag, PB_Message_boundedTag desc m = inr tag -> uindex tag = m.
Proof.
  unfold PB_Message_boundedTag.
  intros. destruct PB_Message_boundedTag'. destruct s.
  easy. inversion H. reflexivity.
Qed.

Definition PB_Message_tagToIndex {desc : PB_Message}
         (tag : BoundedTag desc) :=
  ibound (indexb tag).
Arguments PB_Message_tagToIndex /.

Theorem PB_Message_tagToIndex_correct (desc : PB_Message)
        (tag : BoundedTag desc)
  : PB_FieldTag (Vector.nth (PB_MessageDesc desc) (PB_Message_tagToIndex tag))
    = bindex tag.
Proof.
  destruct desc as [n desc].
  rewrite <- PB_Message_tags_correct.
  destruct tag. destruct indexb.
  eauto.
Qed.

Theorem PB_Message_tagToIndex_correct' (desc : PB_Message)
        (tag : BoundedTag desc)
  : PB_Message_OK desc ->
    forall fld, Vector.In fld (PB_MessageDesc desc) ->
           PB_FieldTag fld = bindex tag ->
           fld = Vector.nth (PB_MessageDesc desc) (PB_Message_tagToIndex tag).
Proof.
  intros. destruct desc as [n desc].
  destruct tag. destruct indexb.
  destruct desc; intros; try easy.
  simpl in ibound.
  revert desc boundi H fld H0 H1. pattern n, ibound.
  apply Fin.caseS; intros; simpl in *.
  - subst. eapply PB_Field_inj; eauto. constructor.
  - eapply PB_Field_inj; eauto. constructor. apply vector_in.
    subst. rewrite <- (PB_Message_tags_correct (Build_PB_Message desc)). auto.
Qed.

Definition PB_Message_tagToType {desc : PB_Message}
           (tag : BoundedTag desc) :=
  PB_FieldType (Vector.nth (PB_MessageDesc desc) (PB_Message_tagToIndex tag)).

Theorem PB_Message_tagToType_correct (desc : PB_Message)
        (tag : BoundedTag desc)
  : PB_Message_OK desc ->
    forall fld, Vector.In fld (PB_MessageDesc desc) ->
           PB_FieldTag fld = bindex tag ->
           PB_FieldType fld = PB_Message_tagToType tag.
Proof.
  intros.
  rewrite (PB_Message_tagToIndex_correct' desc tag H fld); eauto.
Qed.

Definition PB_Message_tagToDenoteType {desc : PB_Message}
           (tag : BoundedTag desc) :=
  Domain (PB_Message_heading desc) (PB_Message_tagToIndex tag).

Theorem PB_Message_tagToDenoteType_correct (desc : PB_Message)
        (tag : BoundedTag desc)
  : PB_Type_denote (PB_Message_tagToType tag)
    = PB_Message_tagToDenoteType tag.
Proof.
  apply PB_denote_type_eq.
Qed.

(* Definition PB_Message_lookup {desc : PB_Message} *)
(*            (msg : PB_Message_denote (Build_PB_Message (PB_MessageDesc desc))) *)
(*            (tag : BoundedTag desc) := *)
(*   type_cast_r (PB_Message_tagToDenoteType_correct desc tag) *)
(*               (GetAttributeRaw msg (PB_Message_tagToIndex tag)). *)

Definition PB_Message_lookup' {n} {desc : PB_Desc n}
           (msg : PB_Message_denote (Build_PB_Message desc))
           (tag : BoundedTag (Build_PB_Message desc)) :=
  type_cast_r (PB_Message_tagToDenoteType_correct (Build_PB_Message desc) tag)
              (GetAttributeRaw msg (PB_Message_tagToIndex tag)).

Definition PB_Message_lookup {desc : PB_Message} :=
  match desc return PB_Message_denote desc ->
                    forall tag : BoundedTag desc,
                      PB_Type_denote (PB_Message_tagToType tag) with
  | Build_PB_Message _ v =>
    fun msg tag => @PB_Message_lookup' _ v msg tag
  end.

(* Definition PB_Message_update {desc : PB_Message} *)
(*            (msg : PB_Message_denote (Build_PB_Message (PB_MessageDesc desc))) *)
(*            (tag : BoundedTag desc) *)
(*            (value : PB_Type_denote (PB_Message_tagToType tag)) *)
(*   : PB_Message_denote (Build_PB_Message (PB_MessageDesc desc)) := *)
(*   SetAttributeRaw msg (PB_Message_tagToIndex tag) *)
(*                   (type_cast *)
(*                      (PB_Message_tagToDenoteType_correct *)
(*                         desc tag) *)
(*                      value). *)

Definition PB_Message_update' {n} {desc : PB_Desc n}
           (msg : PB_Message_denote (Build_PB_Message desc))
           (tag : BoundedTag (Build_PB_Message desc))
           (value : PB_Type_denote (PB_Message_tagToType tag))
  : PB_Message_denote (Build_PB_Message desc) :=
  SetAttributeRaw msg (PB_Message_tagToIndex tag)
                  (type_cast
                     (PB_Message_tagToDenoteType_correct
                        (Build_PB_Message desc) tag)
                     value).

Definition PB_Message_update {desc : PB_Message} :=
  match desc return PB_Message_denote desc ->
                    forall tag : BoundedTag desc,
                      PB_Type_denote (PB_Message_tagToType tag) ->
                      PB_Message_denote desc with
  | Build_PB_Message _ v =>
    fun msg tag value => PB_Message_update' msg tag value
  end.

Definition PB_IRElm_OK {n} (desc : PB_Message n) (elm : PB_IRElm) :=
  match PB_Message_boundedTag desc (PB_IRTag elm) with
  | inleft tag => PB_Message_tagToType tag = PB_IRType elm
  | _ => False
  end.

Definition PB_IRVal_format
  : FormatM PB_IRElm ByteString :=
  fun elm => PB_Type_format (PB_IRType elm) (PB_IRVal elm).

Definition PB_IRVal_decode {n} (desc : PB_Message n)
           (t : N) (wty : N)
  : DecodeM PB_IRElm ByteString :=
  fun b cd =>
    match PB_Message_boundedTag desc t with
      | inleft tag =>
        `(v, b', cd') <- PB_Type_decode (PB_Message_tagToType tag) b cd;
          Some ({| PB_IRTag := (bindex tag);
                   PB_IRType := (PB_Message_tagToType tag);
                   PB_IRVal := v|}, b', cd')
      | _ => None
      end.

Theorem PB_IRVal_decode_correct
        {n} (desc : PB_Message n)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : forall (t : N) (wty : N),
    CorrectDecoder _
                   (fun elm => PB_IRTag elm = t /\ PB_IRElm_OK desc elm)
                   (fun _ _ => True)
                   PB_IRVal_format (PB_IRVal_decode desc t wty) P.
Proof.
  unfold PB_IRElm_OK, PB_IRVal_format, PB_IRVal_decode.
  intros. split; intros.
  - edestruct PB_Type_decode_correct as [Ht _]. decode_step idtac.
    edestruct Ht; clear Ht; eauto; intuition.
    exists x. intuition. subst.
    destruct (PB_Message_boundedTag desc (PB_IRTag data)) eqn:Heq; intuition.
    rewrite H5. rewrite H0. simpl.
    erewrite PB_Message_boundedTag_correct by eassumption.
    repeat progress f_equal.
    destruct data as [tag ty val]; destruct ty as [sty | sty]; destruct sty;
      simpl in *; try reflexivity.
  - destruct (PB_Message_boundedTag desc t) eqn:Heq; try solve [inversion H1].
    decode_opt_to_inv.
    subst; simpl.
    erewrite PB_Message_boundedTag_correct by eassumption.
    edestruct PB_Type_decode_correct as [_ Ht]. decode_step idtac.
    edestruct Ht; clear Ht; eauto; intuition.
    destruct H3 as [bin' [xenv]]. intuition.
    exists bin', xenv. intuition.
    rewrite Heq. auto.
Qed.

Theorem PB_IRVal_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRVal_format d ce1 ↝ (b1, ce1') ->
    PB_IRVal_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_IRVal_format. destruct d.
  apply PB_Type_format_sz_eq.
Qed.

Theorem PB_IRVal_format_byte
  : forall d b ce ce',
    PB_IRVal_format d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_IRVal_format. intros.
  destruct d.
  eapply PB_Type_format_byte; eauto.
Qed.

Local Arguments N.shiftl : simpl never.
Local Arguments N.shiftr : simpl never.
Local Arguments N.lor : simpl never.
Local Arguments N.land : simpl never.
Definition PB_IRElm_format
  : FormatM PB_IRElm ByteString :=
  fun elm =>
    Varint_format (N.lor
                     (N.shiftl (PB_IRTag elm) 3)
                     (PB_WireType_denote (PB_Type_toWireType (PB_IRType elm))))
    ThenC PB_IRVal_format elm
    DoneC.

Lemma N_shiftr_lor_shiftl
  : forall a b n, N.lt (N.log2 b) n ->
             a = N.shiftr (N.lor (N.shiftl a n) b) n.
Proof.
  intros. rewrite N.shiftr_lor.
  rewrite N.shiftr_shiftl_r by apply N.le_refl.
  rewrite (N.shiftr_eq_0 b); auto.
  rewrite N.sub_diag.
  symmetry.
  apply N.lor_0_r.
Qed.

Lemma decides_N_eq
  : forall (n n' : N),
    decides (N.eqb n n') (n = n').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct (N.eqb_spec n n'); auto.
Qed.
Hint Resolve decides_N_eq : decide_data_invariant_db.

Local Arguments CacheDecode : simpl never.
Definition PB_IRElm_decoder {n} (desc : PB_Message n)
  : { decode : _ |
      forall {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
        CorrectDecoder _
                       (PB_IRElm_OK desc)
                       (fun _ _ => True)
                       PB_IRElm_format decode P }.
Proof.
  unfold PB_IRElm_OK, PB_IRElm_format.
  eexists.
  intros. eapply compose_format_correct;
  unfold cache_inv_Property; intuition.
  apply Varint_decode_correct.
  decode_step idtac.
  decode_step idtac.
  decode_step idtac.
  intros. eapply compose_format_correct.
  unfold cache_inv_Property; intuition.
  intros.
  eapply (PB_IRVal_decode_correct desc)
    with (t := N.shiftr proj 3)
         (wty := N.land proj 7).
  decode_step idtac.

  intro. intros[? ?]. split; eauto. subst.
  apply N_shiftr_lor_shiftl. apply PB_WireType_denote_3bits.

  all : decode_step idtac.
Defined.

Definition PB_IRElm_decode {n} (desc : PB_Message n) :=
  Eval simpl in proj1_sig (PB_IRElm_decoder desc).

Definition PB_IRElm_decode_correct {n} (desc : PB_Message n) :=
  Eval simpl in proj2_sig (PB_IRElm_decoder desc).

Theorem PB_IRElm_decode_lt {n} (desc : PB_Message n)
  : forall (b : ByteString) (cd : CacheDecode) (elm : PB_IRElm) 
      (b' : ByteString) (cd' : CacheDecode),
    PB_IRElm_decode desc b cd = Some (elm, b', cd') -> lt_B b' b.
Proof.
  intros.
  decode_opt_to_inv.
  destruct (N.eqb _); inversion H1; clear H1. subst.
  edestruct (PB_IRVal_decode_correct desc (P := fun _ => True))
            as [_ Hd].
  unfold cache_inv_Property; intuition.
  edestruct Hd as [_ [? [_ [_ [Hm _]]]]]; try reflexivity; eauto. clear Hd.
  subst. apply Varint_decode_lt in H.
  unfold lt_B in *. rewrite mappend_measure in H.
  omega.
  Grab Existential Variables.
  auto.
Qed.

Theorem PB_IRElm_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRElm_format d ce1 ↝ (b1, ce1') ->
    PB_IRElm_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_IRElm_format.
  intros.
  computes_to_inv2.
  rewrite !(@mempty_right _ ByteStringQueueMonoid).
  rewrite !@mappend_measure.
  erewrite Varint_format_sz_eq; eauto.
  erewrite PB_IRVal_format_sz_eq with (b1:=b6) (b2:=b0); eauto.
Qed.

Theorem PB_IRElm_format_byte
  : forall d b ce ce',
    PB_IRElm_format d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_IRElm_format. intros.
  intros. computes_to_inv2.
  apply Varint_format_byte in H.
  apply PB_IRVal_format_byte in H'; auto.
  repeat rewrite @mappend_measure.
  rewrite Nat.add_mod; auto.
  rewrite (Nat.add_mod (_ b1) (_ ByteString_id)); auto.
  rewrite H, H'; auto.
Qed.

Definition PB_IR := list PB_IRElm.

Instance PR_IR_monoid : Monoid PB_IR :=
  {| mappend := @app _;
     bin_measure := @length _;
     mempty := nil;
     mappend_measure := @app_length _;
     mempty_left := @app_nil_l _;
     mempty_right := @app_nil_r _;
     mappend_assoc := @app_assoc _
  |}.

Inductive PB_IR_refine {n} {desc : PB_Message n}
  : PB_IR -> PB_Message_denote desc -> Prop :=
| PB_IR_nil :
    PB_IR_refine nil
                 (PB_Message_default desc)
| PB_IR_cons :
    forall ir msg,
      PB_IR_refine ir msg ->
      forall (t : BoundedTag desc)
        (v : PB_Type_denote (PB_Message_tagToType t)),
        PB_IR_refine ({| PB_IRTag := bindex t;
                         PB_IRVal := v |} :: ir)
                     (PB_Message_update msg t v).

Definition PB_Message_IR_format {n} (desc : PB_Message n)
  : FormatM (PB_Message_denote desc) PB_IR :=
  fun msg _ => {b | PB_IR_refine (fst b) msg}.

Definition PB_Message_IR_decode {n} (desc : PB_Message n)
  : DecodeM (PB_Message_denote desc) PB_IR.
Proof.
  refine
    (fix decode ir cd :=
       match ir with
       | nil => Some (PB_Message_default desc, nil, cd)
       | {| PB_IRTag := t;
            PB_IRType := ty;
            PB_IRVal := v |} :: ir' =>
         `(msg, ir2, cd') <- decode ir' cd;
         match PB_Message_boundedTag desc t with
         | inleft tag =>
           if PB_Type_eq_dec ty (PB_Message_tagToType tag) then
             Some (PB_Message_update msg tag _ (* v *),
                   ir2, cd')
           else None
         | _ => None
         end
       end).
  rewrite <- e.
  exact v.
Defined.

Local Transparent computes_to.
Local Transparent Pick.

Lemma PB_Message_IR_Elm_OK {n} (desc : PB_Message n)
      (HP : PB_Message_OK desc)
      (msg : PB_Message_denote desc) (ir : PB_IR)
      (ce ce' : CacheFormat)
  : PB_Message_IR_format desc msg ce ↝ (ir, ce') ->
    forall elm : PB_IRElm, In elm ir -> PB_IRElm_OK desc elm.
Proof.
  unfold PB_Message_IR_format. unfold computes_to. unfold Pick.
  simpl. induction 1; intros; try easy.
  destruct H0; auto. subst.
  unfold PB_IRElm_OK. simpl. destruct PB_Message_boundedTag eqn:Hb.
  - apply PB_Message_boundedTag_correct in Hb.
    apply BoundedTag_inj in Hb; auto. subst. auto.
  - contradiction (BoundedTag_in _ t).
Qed.

Lemma PB_Message_IR_decode_nil {n} (desc : PB_Message n)
      (msg : PB_Message_denote desc) (ir ir' : PB_IR)
      (cd cd' : CacheDecode)
  : PB_Message_IR_decode desc ir cd = Some (msg, ir', cd') -> ir' = nil.
Proof.
  generalize dependent msg.
  generalize dependent cd.
  generalize dependent cd'.
  induction ir; intros.
  - inversion H. auto.
  - simpl in H. destruct a.
    decode_opt_to_inv.
    destruct PB_Message_boundedTag; try easy.
    destruct PB_Type_eq_dec; try easy.
    inversion H0. subst.
    eapply IHir; eauto.
Qed.

Theorem PB_Message_IR_decode_correct {n} (desc : PB_Message n)
        (HP : PB_Message_OK desc)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (fun _ => True)
                   (fun _ ext => ext = mempty)
                   (PB_Message_IR_format desc) (PB_Message_IR_decode desc) P.
Proof.
  unfold PB_Message_IR_format, PB_Message_IR_decode.
  split; intros. {
    subst ext.
    unfold computes_to in H2. unfold Pick in H2.
    simpl in H2. induction H2. {
      eexists. intuition.
    } {
      destruct IHPB_IR_refine as [? [? [? ?]]].
      eexists. repeat split; intros; eauto. simpl.
      simpl in H1. rewrite H1. simpl.
      destruct PB_Message_boundedTag eqn:Heq.
      apply PB_Message_boundedTag_correct in Heq.
      apply BoundedTag_inj in Heq. subst.
      - destruct PB_Type_eq_dec. 
        + repeat progress f_equal.
          rewrite <- eq_rect_eq_dec by (apply PB_Type_eq_dec). auto.
        + easy.
      - easy.
      - contradiction (BoundedTag_in desc t).
    }
  } {
    generalize dependent env.
    generalize dependent env'.
    generalize dependent xenv'.
    generalize dependent data.
    generalize dependent ext.
    induction bin; intros. {
      inversion H1. subst. split; auto.
      exists [], env. repeat split; eauto.
      constructor.
    } {
      destruct a.
      decode_opt_to_inv.
      destruct PB_Message_boundedTag eqn:Heq; try easy.
      destruct PB_Type_eq_dec; try easy.
      inversion H2. clear H2. subst.
      edestruct IHbin as [? [? [? [? [? [? ?]]]]]]; eauto. split; auto.
      eexists _, _; eauto. repeat split; eauto.
      constructor; eauto. subst. simpl.
      apply PB_Message_boundedTag_correct in Heq. subst. auto.
    }
  }
  Grab Existential Variables. auto.
Qed.

Definition PB_Message_format {n} (desc : PB_Message n)
  : FormatM (PB_Message_denote desc) ByteString :=
  (fun msg ce =>
     `(ir, ce') <- PB_Message_IR_format desc msg ce;
       SizedList_format PB_IRElm_format (rev ir) ce')%comp.

Definition PB_Message_decode {n} (desc : PB_Message n)
  : DecodeM (PB_Message_denote desc) ByteString :=
  fun b cd =>
    `(ir, b', cd1) <- SizedList_decode (PB_IRElm_decode desc) (PB_IRElm_decode_lt desc) (bin_measure b) b cd;
      `(msg, ir', cd2) <- PB_Message_IR_decode desc (rev ir) cd1;
      Some (msg, b', cd2).

Theorem PB_Message_decode_correct {n} (desc : PB_Message n)
        (HP : PB_Message_OK desc)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (fun _ => True)
                   (fun _ ext => ext = mempty)
                   (PB_Message_format desc) (PB_Message_decode desc) P.
Proof.
  unfold PB_Message_format, PB_Message_decode.
  split; intros. {
    subst.
    computes_to_inv2.
    edestruct (SizedList_decode_correct _ _ _ _ _
                                        PB_IRElm_format_sz_eq
                                        (PB_IRElm_decode_lt desc)
                                        (PB_IRElm_decode_correct desc P P_OK)) as [He2 _]; eauto.
    edestruct He2; try apply H3'; eauto.
    split. {
      intros. eapply (SizedList_format_sz_eq _ PB_IRElm_format_sz_eq); eauto.
    } {
      intros. rewrite <- in_rev in *.
      eapply PB_Message_IR_Elm_OK; eauto.
    }
    apply SizedList_predicate_rest_True. intuition. clear He2.
    edestruct (PB_Message_IR_decode_correct desc) as [He1 _]; eauto.
    edestruct He1; eauto. eauto. intuition. clear He1.
    eexists. repeat split; eauto.
    rewrite @mempty_right in *.
    rewrite H3. simpl. rewrite rev_involutive.
    rewrite H6. simpl. eauto.
  } {
    decode_opt_to_inv. subst.

    edestruct (PB_Message_IR_decode_correct desc) as [_ Hd1]; eauto.
    edestruct Hd1 as [? [? [? [? [? [? ?]]]]]]; try apply H2; eauto.
    all : edestruct (SizedList_decode_correct _ _ _ _ _
                                              PB_IRElm_format_sz_eq
                                              (PB_IRElm_decode_lt desc)
                                              (PB_IRElm_decode_correct desc P P_OK)) as [_ Hd2]; eauto.
    all : edestruct Hd2 as [? [? [? [? [? [? ?]]]]]]; try apply H1; eauto.

    subst. split; eauto. eexists _, _. repeat split; eauto.
    computes_to_econstructor; eauto. simpl.
    assert (x3 = nil) by (eapply PB_Message_IR_decode_nil; eauto).
    subst. rewrite @mempty_right in *. subst.
    rewrite rev_involutive. eauto.
  }
Qed.

Definition CorrectDecoderFor' {A B} {cache : Cache}
           {monoid : Monoid B} Invariant FormatSpec :=
  { decodePlusCacheInv : _ |
    exists P_inv,
    (cache_inv_Property (snd decodePlusCacheInv) P_inv
     -> CorrectDecoder (A := A) monoid Invariant (fun _ ext => ext = mempty)
                                FormatSpec
                                (fst decodePlusCacheInv)
                                (snd decodePlusCacheInv))
    /\ cache_inv_Property (snd decodePlusCacheInv) P_inv}%type.

Lemma Start_CorrectDecoderFor'
      {A B} {cache : Cache}
      {monoid : Monoid B}
      Invariant
      FormatSpec
      (decoder decoder_opt : B -> CacheDecode -> option (A * B * CacheDecode))
      (cache_inv : CacheDecode -> Prop)
      (P_inv : (CacheDecode -> Prop) -> Prop)
      (decoder_OK :
         cache_inv_Property cache_inv P_inv
         -> CorrectDecoder (A := A) monoid Invariant (fun _ ext => ext = mempty)
                                    FormatSpec decoder cache_inv)
      (cache_inv_OK : cache_inv_Property cache_inv P_inv)
      (decoder_opt_OK : forall b cd, decoder b cd = decoder_opt b cd)
  : @CorrectDecoderFor' A B cache monoid Invariant FormatSpec.
Proof.
  exists (decoder_opt, cache_inv); exists P_inv; split; simpl; eauto.
  unfold CorrectDecoder in *; intuition; intros.
  - destruct (H1 _ _ _ _ _ ext env_OK H0 H3 H4 H5).
    rewrite decoder_opt_OK in H6; eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
  - rewrite <- decoder_opt_OK in H4; destruct (H2 _ _ _ _ _ _ H0 H3 H4); eauto.
Defined.

Definition PB_Message_decoder {n} (desc : PB_Message n)
           (HP : PB_Message_OK desc)
  : CorrectDecoderFor' (fun _ => True) (PB_Message_format desc).
Proof.
  eapply Start_CorrectDecoderFor'.
  - intros. apply PB_Message_decode_correct; eauto.
  - cbv beta; synthesize_cache_invariant.
  - cbv beta; optimize_decoder_impl.
Defined.

(* Example *)
(* Open Scope Tuple. *)
(* Import Vectors.VectorDef.VectorNotations. *)

(* Notation "'PB_MESSAGE_TAG' t" := *)
(*   (@Build_BoundedIndex _ _ _ t%N _) *)
(*     (at level 70). *)

(* Definition PersonMessage : PB_Message _ := *)
(*   [{| PB_FieldType := PB_Singular PB_fixed64; PB_FieldName := "id"; PB_FieldTag := 1 |}; *)
(*      {| PB_FieldType := PB_Singular PB_fixed32; PB_FieldName := "age"; PB_FieldTag := 2 |}]. *)
(* Definition PersonFieldId := PersonMessage[@Fin.F1]. *)
(* Definition PersonFieldAge := PersonMessage[@Fin.FS Fin.F1]. *)

(* Compute (PB_Message_denote PersonMessage). *)

(* Definition person : PB_Message_denote PersonMessage := *)
(*   ilist.Build_prim_prod (natToWord 64 4) *)
(*                         (ilist.Build_prim_prod (natToWord 32 27) tt). *)
(* Definition def_person := PB_Message_default PersonMessage. *)

(* Compute person!"id". *)
(* Compute def_person!"id". *)
(* Compute (@PB_Message_tagToIndex _ PersonMessage (PB_MESSAGE_TAG 1)). *)
(* Compute (@PB_Message_tagToType _ PersonMessage (PB_MESSAGE_TAG 2)). *)

(* Compute (PB_Message_lookup person (PB_MESSAGE_TAG 2)). *)
(* Compute (PB_Message_update person (PB_MESSAGE_TAG 2) (natToWord 32 3)). *)