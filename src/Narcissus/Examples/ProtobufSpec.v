Require Import
        Coq.ZArith.BinInt
        Coq.Strings.String
        Coq.Vectors.Vector
        Coq.omega.Omega
        Coq.Logic.Eqdep_dec.

Require Import
        Fiat.QueryStructure.Specification.Representation.Notations
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.QueryStructure.Specification.Representation.Tuple
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

Inductive PB_WireType : Set :=
| PB_Varint : PB_WireType
| PB_32bit : PB_WireType
| PB_64bit : PB_WireType
| PB_LengthDelimited : PB_WireType.

Definition PB_WireType_denote (wty : PB_WireType) : N :=
  match wty with
  | PB_Varint => 0
  | PB_32bit => 5
  | PB_64bit => 1
  | PB_LengthDelimited => 2
  end.

Theorem PB_WireType_denote_3bits (wty : PB_WireType)
  : N.lt (N.log2 (PB_WireType_denote wty)) 3%N.
Proof.
  destruct wty; easy.
Qed.

Inductive PB_SingularType : Set :=
| PB_fixed32 : PB_SingularType
| PB_fixed64 : PB_SingularType
| PB_int32 : PB_SingularType
| PB_int64 : PB_SingularType
(* | PB_sfixed32 : PB_SingularType *)
(* | PB_sfixed64 : PB_SingularType *)
(* | PB_bool : PB_SingularType *)
(* | PB_string : PB_SingularType *)
.

Definition PB_SingularType_denote (sty : PB_SingularType) : Type :=
   match sty with
   | PB_fixed32 => word 32
   | PB_fixed64 => word 64
   (* :TODO: use word 32/64 later *)
   (* :TODO: combinator for function composition? *)
   | PB_int32 => N
   | PB_int64 => N
  end.

Definition PB_SingularType_format (sty : PB_SingularType)
  : FormatM (PB_SingularType_denote sty) ByteString :=
  match sty with
  | PB_fixed32 => format_word
  | PB_fixed64 => format_word
  | PB_int32 => Varint_format
  | PB_int64 => Varint_format
  end.

Definition PB_SingularType_decoder
           (sty : PB_SingularType)
  : { decode : _ |
      forall {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
        CorrectDecoder _
                       (fun _ => True)
                       (fun _ _ => True)
                       (PB_SingularType_format sty) decode P }.
Proof.
  let d := fill_ind_h
             (PB_SingularType_rect
                (fun sty => DecodeM (PB_SingularType_denote sty)
                                 ByteString)) in
  refine (exist _ (d sty) _).

  intros; destruct sty; simpl;
    repeat decode_step idtac.
  all : apply Varint_decode_correct.
  all : repeat decode_step idtac.
Defined.

Definition PB_SingularType_decode (sty : PB_SingularType) :=
  Eval simpl in proj1_sig (PB_SingularType_decoder sty).

(* :TODO: don't simply theorem and make them opaque. *)
Definition PB_SingularType_decode_correct (sty : PB_SingularType) :=
  Eval simpl in proj2_sig (PB_SingularType_decoder sty).

Theorem PB_SingularType_format_eq (sty : PB_SingularType)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_SingularType_format sty d ce1 ↝ (b1, ce1') ->
    PB_SingularType_format sty d ce2 ↝ (b2, ce2') ->
    b1 = b2.
Proof.
  unfold PB_SingularType_format.
  destruct sty; intros;
    repeat match goal with
           | H : format_word _  _ ↝ _ |- _ => inversion H; subst; clear H
           end;
    auto.
  all : eapply Varint_format_eq; eauto.
Qed.

Theorem PB_SingularType_format_sz_eq (sty : PB_SingularType)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_SingularType_format sty d ce1 ↝ (b1, ce1') ->
    PB_SingularType_format sty d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  intros; f_equal; eapply PB_SingularType_format_eq; eauto.
Qed.

Theorem PB_SingularType_format_byte (sty : PB_SingularType)
  : forall d b ce ce',
    PB_SingularType_format sty d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_SingularType_format.
  destruct sty; intros;
    solve [eapply format_word_byte; eauto; eauto |
           eapply Varint_format_byte; eauto; eauto].
Qed.

Inductive PB_Type : Set :=
| PB_Singular : PB_SingularType -> PB_Type
(* | PB_Repeated : PB_SingularType -> PB_Type *)
.

Definition PB_Type_eq_dec
  : forall t1 t2 : PB_Type, {t1 = t2} + {t1 <> t2}.
Proof.
  decide equality.
  decide equality.
Defined.

Definition PB_Type_denote (ty : PB_Type) : Type :=
  match ty with
  | PB_Singular sty => PB_SingularType_denote sty
  end.

Definition PB_Type_format (ty : PB_Type) : FormatM (PB_Type_denote ty) ByteString :=
  match ty with
  | PB_Singular sty => PB_SingularType_format sty
  end.

(* :TODO: extend decode_step *)
Definition PB_Type_decoder
        (ty : PB_Type)
  : { decode : _ |
      forall {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b))),
        CorrectDecoder _
                       (fun _ => True)
                       (fun _ _ => True)
                       (PB_Type_format ty) decode P }.
Proof.
  let d := fill_ind_h
             (PB_Type_rect
                (fun ty => DecodeM (PB_Type_denote ty)
                                ByteString)) in
  refine (exist _ (d ty) _).

  intros; destruct ty; simpl;
    apply PB_SingularType_decode_correct;
    repeat decode_step idtac.
Defined.

Definition PB_Type_decode (ty : PB_Type) :=
  Eval simpl in proj1_sig (PB_Type_decoder ty).

Definition PB_Type_decode_correct (ty : PB_Type) :=
  Eval simpl in proj2_sig (PB_Type_decoder ty).

Theorem PB_Type_format_eq (ty : PB_Type)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_Type_format ty d ce1 ↝ (b1, ce1') ->
    PB_Type_format ty d ce2 ↝ (b2, ce2') ->
    b1 = b2.
Proof.
  unfold PB_Type_format. destruct ty.
  apply PB_SingularType_format_eq.
Qed.

Theorem PB_Type_format_sz_eq (ty : PB_Type)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_Type_format ty d ce1 ↝ (b1, ce1') ->
    PB_Type_format ty d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  intros; f_equal; eapply PB_Type_format_eq; eauto.
Qed.

Theorem PB_Type_format_byte (ty : PB_Type)
  : forall d b ce ce',
    PB_Type_format ty d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_Type_format. destruct ty.
  apply PB_SingularType_format_byte.
Qed.

Definition PB_Type_default (ty : PB_Type) : PB_Type_denote ty :=
  match ty with
  | PB_Singular sty => match sty with
                      | PB_fixed32 => wzero 32
                      | PB_fixed64 => wzero 64
                      | PB_int32 => 0%N
                      | PB_int64 => 0%N
                      end
  end.

Definition PB_Type_toWireType (ty : PB_Type) : PB_WireType :=
  match ty with
  | PB_Singular sty => match sty with
                          | PB_fixed32 => PB_32bit
                          | PB_fixed64 => PB_64bit
                          | PB_int32 => PB_Varint
                          | PB_int64 => PB_Varint
                          end
  end.

Record PB_Field := 
  { PB_FieldType : PB_Type;
    PB_FieldName : string;
    PB_FieldTag : N }.

Definition PB_Field_denote (fld : PB_Field) :=
  match fld with
  | {| PB_FieldType := ty; PB_FieldName := name |} =>
    (name :: PB_Type_denote ty)%Attribute
  end.

Definition PB_FieldTag_OK (t : N) :=
  ((1 <= t <= 18999) \/ (20000 <= t <= 536870911))%N.

Definition PB_FieldName_OK (n : string) :=
  n <> EmptyString.

Definition PB_Field_OK (fld : PB_Field) :=
  PB_FieldName_OK (PB_FieldName fld) /\
  PB_FieldTag_OK (PB_FieldTag fld).

Definition PB_Message := Vector.t PB_Field.

Definition PB_Message_heading {n} (desc : PB_Message n) :=
  (BuildHeading (Vector.map PB_Field_denote desc)).

Definition PB_Message_denote {n} (desc : PB_Message n) :=
  @Tuple (PB_Message_heading desc).

Definition PB_Message_tags {n} (desc : PB_Message n) :=
  Vector.map PB_FieldTag desc.

(* :TODO: abstract out this proof as ltac. *)
Lemma PB_Message_tags_correct {n} (desc : PB_Message n)
  : forall i, Vector.nth (PB_Message_tags desc) i
         = PB_FieldTag (Vector.nth desc i).
Proof.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros.
    + reflexivity.
    + apply IHdesc.
Qed.

Fixpoint PB_Message_default {n} (desc : PB_Message n) : PB_Message_denote desc :=
  match desc with
  | Vector.nil => inil2 (B:=id)
  | Vector.cons fld _ desc' => match fld with
                              | {| PB_FieldType := ty |} =>
                                icons2 (B:=id) (PB_Type_default ty)
                                            (PB_Message_default desc')
                              end
  end.

Lemma PB_denote_type_eq {n} (desc : PB_Message n) (i : Fin.t n)
  : PB_Type_denote (PB_FieldType (Vector.nth desc i))
    = Domain (PB_Message_heading desc) i.
Proof.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Defined.

Lemma PB_Message_default_correct {n} (desc : PB_Message n)
  : forall (i : Fin.t n),
    type_cast (PB_denote_type_eq desc i)
              (PB_Type_default (PB_FieldType (Vector.nth desc i)))
    = ith2 (PB_Message_default desc) i.
Proof.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Qed.

Lemma PB_Message_default_correct' {n} (desc : PB_Message n)
  : forall (i : Fin.t n),
    PB_Type_default (PB_FieldType (Vector.nth desc i))	
    ~= ith2 (PB_Message_default desc) i.
Proof.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Qed.

Definition PB_Message_tags_nodup {n} (desc : PB_Message n) :=
  forall i1 i2 : Fin.t n,
    Vector.nth (PB_Message_tags desc) i1 = Vector.nth (PB_Message_tags desc) i2 ->
    i1 = i2.

Definition PB_Message_names_nodup {n} (desc : PB_Message n) :=
  forall i1 i2 : Fin.t n,
    PB_FieldName (Vector.nth desc i1) = PB_FieldName (Vector.nth desc i2) ->
    i1 = i2.

Definition PB_Message_OK {n} (desc : PB_Message n) :=
  Vector.Forall PB_Field_OK desc /\
  PB_Message_tags_nodup desc /\ PB_Message_names_nodup desc.

Definition BoundedTag {n} (desc : PB_Message n) :=
  BoundedIndex (PB_Message_tags desc).

Theorem BoundedTag_inj {n} (desc : PB_Message n)
  : PB_Message_OK desc ->
    forall t1 t2 : BoundedTag desc,
      bindex t1 = bindex t2 -> t1 = t2.
Proof.
  unfold PB_Message_OK, PB_Message_tags_nodup.
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

Theorem PB_Field_inj {n} (desc : PB_Message n)
  : PB_Message_OK desc ->
    forall fld1 fld2 : PB_Field,
      Vector.In fld1 desc -> Vector.In fld2 desc ->
      PB_FieldTag fld1 = PB_FieldTag fld2 ->
      fld1 = fld2.
Proof.
  unfold PB_Message_OK, PB_Message_tags_nodup.
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

Theorem BoundedTag_in {n} (desc : PB_Message n)
  : forall t1 : BoundedTag desc, Vector.In (bindex t1) (PB_Message_tags desc).
Proof.
  intros. destruct t1. destruct indexb. simpl in *.
  subst. eapply vector_in; eauto.
Qed.

Fixpoint PB_Message_boundedTag' {n} (tags : Vector.t N n) (m : N)
  : (BoundedIndex tags) + {~ Vector.In m tags}.
Proof.
  refine
    (match tags with
     | Vector.nil => inright _
     | Vector.cons t n' tags' =>
       if N.eq_dec t m then
         inleft
           {| bindex := m;
              indexb := {| ibound := Fin.F1;
                           boundi := _ |} |}
       else
         match PB_Message_boundedTag' n' tags' m with
         | inleft
             {| bindex := m';
                indexb := {| ibound := i;
                             boundi := _ |} |} =>
           inleft
             {| bindex := m';
                indexb := {| ibound := Fin.FS i;
                             boundi := _|} |}
         | inright _ => inright _
         end
     end); auto.
  - abstract inversion 1.
  - abstract
      (inversion 1; auto; existT_eq_dec;
       subst; congruence).
Defined.

Definition PB_Message_boundedTag {n} (desc : PB_Message n) (m : N)
  : (BoundedTag desc) + {~ Vector.In m (PB_Message_tags desc)} :=
  PB_Message_boundedTag' (PB_Message_tags desc) m.

Theorem PB_Message_boundedTag_correct {n} (desc : PB_Message n) (m : N)
  : forall tag, PB_Message_boundedTag desc m = inleft tag -> bindex tag = m.
Proof.
  unfold BoundedTag. unfold PB_Message_boundedTag.
  remember (PB_Message_tags desc) as tags.
  induction tags; intros.
  - inversion H.
  - revert tags Heqtags tag H IHtags.
    pattern n, desc. apply caseS. intros.
    inversion Heqtags.
    existT_eq_dec.
    specialize (IHtags t H2).
    inversion H. destruct (N.eq_dec _ _).
    + inversion H3; auto.
    + destruct (PB_Message_boundedTag' tags m);
        try solve [inversion H3].
      destruct b, indexb. destruct tag, indexb.
      simpl. rewrite <- boundi0.
      revert t tags Heqtags boundi0 H ibound boundi IHtags H2 H3.
      pattern n0, ibound0. apply Fin.caseS; intros; inversion H3.
      simpl. simpl in boundi0.
      specialize
        (IHtags {| bindex := bindex0;
                   indexb := {| ibound := p;
                                boundi := boundi0 |} |}).
      simpl in IHtags.
      rewrite boundi0. apply IHtags.
      inversion H3.
      existT_eq_dec.
      f_equal.
      revert boundi IHtags H3.
      rewrite H6, H7.
      intros. f_equal. f_equal.
      apply UIP_dec. apply N.eq_dec.
Qed.

Definition PB_Message_tagToIndex {n} {desc : PB_Message n}
         (tag : BoundedTag desc) :=
  ibound (indexb tag).
Arguments PB_Message_tagToIndex /.

Theorem PB_Message_tagToIndex_correct {n} (desc : PB_Message n)
        (tag : BoundedTag desc)
  : PB_FieldTag (Vector.nth desc (PB_Message_tagToIndex tag))
    = bindex tag.
Proof.
  rewrite <- PB_Message_tags_correct.
  destruct tag. destruct indexb.
  eauto.
Qed.

Theorem PB_Message_tagToIndex_correct' {n} (desc : PB_Message n)
        (tag : BoundedTag desc)
  : PB_Message_OK desc ->
    forall fld, Vector.In fld desc ->
           PB_FieldTag fld = bindex tag ->
           fld = Vector.nth desc (PB_Message_tagToIndex tag).
Proof.
  intros. destruct tag. destruct indexb.
  destruct desc; intros; try easy.
  revert desc boundi H fld H0 H1. pattern n, ibound.
  apply Fin.caseS; intros; simpl in *.
  - subst. eapply PB_Field_inj; eauto. constructor.
  - eapply PB_Field_inj; eauto. constructor. apply vector_in.
    subst. rewrite <- PB_Message_tags_correct. auto.
Qed.

Definition PB_Message_tagToType {n} {desc : PB_Message n}
           (tag : BoundedTag desc) :=
  PB_FieldType (Vector.nth desc (PB_Message_tagToIndex tag)).

Theorem PB_Message_tagToType_correct {n} (desc : PB_Message n)
        (tag : BoundedTag desc)
  : PB_Message_OK desc ->
    forall fld, Vector.In fld desc ->
           PB_FieldTag fld = bindex tag ->
           PB_FieldType fld = PB_Message_tagToType tag.
Proof.
  intros.
  rewrite (PB_Message_tagToIndex_correct' desc tag H fld); eauto.
Qed.

Definition PB_Message_tagToDenoteType {n} {desc : PB_Message n}
           (tag : BoundedTag desc) :=
  Domain (PB_Message_heading desc) (PB_Message_tagToIndex tag).

Theorem PB_Message_tagToDenoteType_correct {n} (desc : PB_Message n)
        (tag : BoundedTag desc)
  : PB_Type_denote (PB_Message_tagToType tag)
    = PB_Message_tagToDenoteType tag.
Proof.
  apply PB_denote_type_eq.
Qed.

Definition PB_Message_lookup {n} {desc : PB_Message n}
           (msg : PB_Message_denote desc) (tag : BoundedTag desc) :=
  GetAttributeRaw msg (PB_Message_tagToIndex tag).

Definition PB_Message_update' {n} {desc : PB_Message n}
           (msg : PB_Message_denote desc) (tag : BoundedTag desc)
           (value : Domain (PB_Message_heading desc)
                           (PB_Message_tagToIndex tag))
  : PB_Message_denote desc :=
  SetAttributeRaw msg (PB_Message_tagToIndex tag) value.

Definition PB_Message_update {n} {desc : PB_Message n}
           (msg : PB_Message_denote desc) (tag : BoundedTag desc)
           (value : PB_Type_denote (PB_Message_tagToType tag))
  : PB_Message_denote desc :=
  SetAttributeRaw msg (PB_Message_tagToIndex tag)
                  (type_cast
                     (PB_Message_tagToDenoteType_correct
                        desc tag)
                     value).

Record PB_IRElm :=
  { PB_IRTag : N;
    PB_IRType : PB_Type;
    PB_IRVal : PB_Type_denote PB_IRType }.

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
    destruct data as [tag ty val]; destruct ty as [sty]; destruct sty;
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

Theorem PB_IRVal_format_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRVal_format d ce1 ↝ (b1, ce1') ->
    PB_IRVal_format d ce2 ↝ (b2, ce2') ->
    b1 = b2.
Proof.
  unfold PB_IRVal_format.
  destruct d.
  apply PB_Type_format_eq.
Qed.

Theorem PB_IRVal_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRVal_format d ce1 ↝ (b1, ce1') ->
    PB_IRVal_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  intros; f_equal; eapply PB_IRVal_format_eq; eauto.
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

Theorem PB_IRElm_format_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRElm_format d ce1 ↝ (b1, ce1') ->
    PB_IRElm_format d ce2 ↝ (b2, ce2') ->
    b1 = b2.
Proof.
  unfold PB_IRElm_format.
  intros.
  computes_to_inv2.
  progress repeat f_equal.
  eapply Varint_format_eq; eauto.
  eapply PB_IRVal_format_eq; eauto.
Qed.

Theorem PB_IRElm_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IRElm_format d ce1 ↝ (b1, ce1') ->
    PB_IRElm_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  intros; f_equal; eapply PB_IRElm_format_eq; eauto.
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

Definition PB_IR_format
  : FormatM PB_IR ByteString :=
  fix format ir ce :=
    match ir with
    | nil => ret (mempty, ce)
    | elm :: ir' => 
      `(b1, ce1) <- PB_IRElm_format elm ce;
        `(b2, ce2) <- format ir' ce1;
        ret (mappend b1 b2, ce2)
    end%comp.

Theorem PB_IR_format_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IR_format d ce1 ↝ (b1, ce1') ->
    PB_IR_format d ce2 ↝ (b2, ce2') ->
    b1 = b2.
Proof.
  unfold PB_IR_format. induction d; intros.
  - inversion H. inversion H0. reflexivity.
  - computes_to_inv2.
    repeat progress f_equal.
    eapply PB_IRElm_format_eq; eauto.
    eauto.
Qed.

Theorem PB_IR_format_sz_eq
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_IR_format d ce1 ↝ (b1, ce1') ->
    PB_IR_format d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  intros; f_equal; eapply PB_IR_format_eq; eauto.
Qed.

Definition PB_IR_decode {n} (desc : PB_Message n)
  : nat -> DecodeM PB_IR ByteString.
Proof.
  refine
    (Fix lt_wf _
         (fun sz decode =>
            fun b cd =>
              match sz with
              | O => Some (nil, b, cd)
              | S _ => `(elm, b1, cd1) <- Decode_w_Measure_lt (PB_IRElm_decode desc) b cd _;
                        if lt_dec sz (bin_measure b - bin_measure (proj1_sig b1)) then
                          None
                        else
                          `(ir, b2, cd2) <- decode (sz - (bin_measure b - bin_measure (proj1_sig b1))) _ (proj1_sig b1) cd1;
                        Some (elm :: ir, b2, cd2)
              end)).
  - apply PB_IRElm_decode_lt.
  - destruct b1. unfold lt_B in l. simpl in *. abstract omega.
Defined.

Theorem PB_IR_decode_correct {n} (desc : PB_Message n)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : forall sz,
    CorrectDecoder _
                   (fun ir =>
                      (forall b ce ce',
                          PB_IR_format ir ce ↝ (b, ce') ->
                          bin_measure b = sz) /\
                      forall elm, In elm ir -> PB_IRElm_OK desc elm)
                   (fun _ _ => True)
                   PB_IR_format (PB_IR_decode desc sz) P.
Proof.
  unfold PB_IRElm_OK, PB_IR_format, PB_IR_decode.
  split; intros. {
    generalize dependent sz.
    generalize dependent env.
    generalize dependent env'.
    generalize dependent xenv.
    generalize dependent ext.
    generalize dependent bin.
    clear H1.
    induction data; intros. {
      eexists.
      intuition; eauto. specialize (H1 _ _ _ H2).
      inversion H2. clear H2.
      assert (sz = 0). {
        subst.
        simpl in *. unfold length_ByteString in *.
        simpl in *. omega.
      } subst.
      rewrite @mempty_left.
      simpl in *. rewrite Coq.Init.Wf.Fix_eq by solve_extensionality; simpl.
      auto.
    } {
      destruct H0 as [H1 H3]. specialize (H1 _ _ _ H2).
      computes_to_inv2.
      destruct (PB_IRElm_decode_correct desc) with (P:=P) as [He _]; auto.
      edestruct He with (ext:=mappend b ext) as [? [? [? ?]]]; eauto.
      apply H3. intuition.
      rewrite @mappend_measure.
      edestruct IHdata with (ext:=ext) as [? [? [? ?]]]; intros; eauto.
      split. intros.
      eapply PB_IR_format_sz_eq; eauto.
      intros. apply H3. intuition. clear IHdata.
      eexists; intuition; eauto.
      rewrite Coq.Init.Wf.Fix_eq by solve_extensionality; simpl.
      match goal with
      | _ : _ |- context [match ?a with _ => _ end] => destruct a eqn:?
      end.
      pose proof (PB_IRElm_decode_lt desc _ _ _ _ _ H0).
      match goal with
      | H : lt_B _ _ |- _ => unfold lt_B in H; repeat rewrite @mappend_measure in H; simpl in H
      end; omega.
      edestruct @Decode_w_Measure_lt_eq
        with (A_decode_lt:=(PB_IRElm_decode_lt desc)).
      unfold PB_IRElm_decode. apply H0.
      revert x1 H8. rewrite mappend_assoc. simpl. intros.
      rewrite H8. simpl. clear x1 H8.
      destruct lt_dec.
      repeat rewrite (@mappend_measure _ ByteStringQueueMonoid) in l. simpl in l.
      omega. repeat rewrite (@mappend_measure _ ByteStringQueueMonoid).
      match goal with
      | _ : _ |- context [Fix _ _ _ ?a _ _] => 
        replace a with (bin_measure b)
      end. simpl in H5. simpl. rewrite H5. auto.
      match goal with
      | _ : _ |- context [match ?a with _ => _ end] =>
        replace a with (bin_measure b0) by omega
      end.
      destruct (bin_measure b0) eqn:Heq; simpl in *; omega.
    }
  } {
    generalize dependent env.
    generalize dependent env'.
    generalize dependent xenv'.
    generalize dependent data.
    generalize dependent ext.
    generalize dependent bin.
    induction sz using (well_founded_ind lt_wf); intros.
    rewrite Coq.Init.Wf.Fix_eq in H1 by solve_extensionality.
    destruct sz. {
      inversion H1. clear H1. subst. split; auto.
      exists mempty, env. repeat split; intros.
      - symmetry. apply mempty_left.
      - inversion H1. reflexivity.
      - inversion H1.
    } {
      decode_opt_to_inv.
      destruct x0. simpl proj1_sig in H3.  simpl proj2_sig in H3.
      apply Decode_w_Measure_lt_eq_inv in H1. simpl in H1.
      destruct (PB_IRElm_decode_correct desc) with (P:=P) as [_ Hd]; auto.
      edestruct Hd as [? [? [? [? [? [? ?]]]]]]; eauto. clear Hd.
      destruct lt_dec; try congruence.
      decode_opt_to_inv. subst.
      edestruct H. 3:eauto. unfold lt_B in l. omega. eauto. eauto.
      destruct H11 as [? [? [? [? [[? ?] ?]]]]].
      split; eauto. eexists _, _. repeat split.
      - computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
      - simpl fst. rewrite <- mappend_assoc. subst. auto.
      - intros. unfold compose in H16. unfold Bind2 in H16.
        computes_to_inv. destruct v, v0. simpl fst in *. simpl snd in *.
        inversion H16''. subst. clear H16''.
        specialize (H13 _ _ _ H16'). rewrite @mappend_measure. rewrite H13.
        repeat rewrite @mappend_measure.
        repeat rewrite @mappend_measure in n0.
        assert (bin_measure b0 = bin_measure x2). {
          eapply PB_IRElm_format_sz_eq; eauto.
        } omega.
      - intros. destruct H16.
        + subst. eauto.
        + apply H14. eauto.
    }
  }
Qed.

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
       PB_IR_format (rev ir) ce')%comp.

Definition PB_Message_decode {n} (desc : PB_Message n)
  : DecodeM (PB_Message_denote desc) ByteString :=
  fun b cd =>
    `(ir, b', cd1) <- PB_IR_decode desc (bin_measure b) b cd;
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
    edestruct (PB_IR_decode_correct desc (P:=P)) as [He2 _]; eauto.
    edestruct He2; try apply H3'; eauto.
    split. {
      intros. eapply PB_IR_format_sz_eq; eauto.
    } {
      intros. rewrite <- in_rev in *.
      eapply PB_Message_IR_Elm_OK; eauto.
    }
    intuition. clear He2.
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
    edestruct (PB_IR_decode_correct desc (P:=P)) as [_ Hd2]; eauto.
    edestruct Hd2 as [? [? [? [? [? [? ?]]]]]]; try apply H1; eauto.
    edestruct (PB_IR_decode_correct desc (P:=P)) as [_ Hd2]; eauto.
    edestruct Hd2 as [? [? [? [? [? [? ?]]]]]]; try apply H1; eauto.

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