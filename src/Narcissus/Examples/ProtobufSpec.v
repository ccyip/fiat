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

Scheme PB_SingularType_mut := Induction for PB_SingularType Sort Prop
  with PB_Type_mut := Induction for PB_Type Sort Prop
  with PB_Field_mut := Induction for PB_Field Sort Prop
  with PB_Message_mut := Induction for PB_Message Sort Prop.

Section PB_Message_induction.
  Variable P_sty : PB_SingularType -> Prop.
  Variable P_ty : PB_Type -> Prop.
  Variable P_fld : PB_Field -> Prop.
  Variable P_desc : PB_Message -> Prop.
  Variable f0 : forall pty : PB_PrimitiveType, P_sty (PB_Primitive pty).
  Variable f1 : forall desc : PB_Message, P_desc desc -> P_sty (PB_Embedded desc).
  Variable f2 : forall sty : PB_SingularType, P_sty sty -> P_ty (PB_Singular sty).
  Variable f3 : forall sty : PB_SingularType, P_sty sty -> P_ty (PB_Repeated sty).
  Variable f4 : forall ty : PB_Type, P_ty ty -> forall (s : string) (n : N), P_fld (Build_PB_Field ty s n).
  Variable f5 : forall (n : nat) (v : Vector.t PB_Field n), Vector.Forall P_fld v -> P_desc (Build_PB_Message v).

  Fixpoint PB_SingularType_ind' (sty : PB_SingularType) : P_sty sty
  with PB_Type_ind' (ty : PB_Type) : P_ty ty
  with PB_Field_ind' (fld : PB_Field) : P_fld fld
  with PB_Message_ind' (desc : PB_Message) : P_desc desc.
  Proof.
    destruct sty. apply f0. apply f1. auto.
    destruct ty. apply f2. auto. apply f3. auto.
    destruct fld. apply f4. auto.
    destruct desc as [n desc]. apply f5.
    induction desc; constructor; auto.
  Defined.

End PB_Message_induction.

Definition PB_FieldType (fld : PB_Field) := let (ty, _, _) := fld in ty.
Definition PB_FieldName (fld : PB_Field) := let (_, name, _) := fld in name.
Definition PB_FieldTag (fld : PB_Field) := let (_, _, tag) := fld in tag.

Definition PB_Desc := Vector.t PB_Field.

Definition PB_MessageLen (desc : PB_Message) :=
  let (n, _) := desc in n.

Definition PB_MessageDesc (desc : PB_Message) :=
  let (_, v) return (Vector.t _ (PB_MessageLen desc)) := desc in v.

Definition PB_Message_tags' {n} (desc : PB_Desc n) :=
  Vector.map PB_FieldTag desc.

Definition PB_Message_tags (desc : PB_Message) :=
  PB_Message_tags' (PB_MessageDesc desc).

Definition vec_eq_dec
           {A} (A_eq_dec : forall (a1 a2 : A), {a1 = a2} + {a1 <> a2})
  : forall {n} (v1 v2 : Vector.t A n), {v1 = v2} + {v1 <> v2}.
Proof.
  refine (@Vector.rect2 _ _ _ _ _). {
    left. reflexivity.
  } {
    intros.
    destruct (A_eq_dec a b). {
      destruct H. {
        left. subst. reflexivity.
      } {
        right. inversion 1. existT_eq_dec. easy.
      }
    } {
      right. inversion 1. easy.
    }
  }
Defined.

Fixpoint PB_SingularType_eq_dec (sty1 sty2 : PB_SingularType)
  : {sty1 = sty2} + {sty1 <> sty2}
with PB_Type_eq_dec (ty1 ty2 : PB_Type)
     : {ty1 = ty2} + {ty1 <> ty2}
with PB_Field_eq_dec (fld1 fld2 : PB_Field)
     : {fld1 = fld2} + {fld1 <> fld2}
with PB_Message_eq_dec (desc1 desc2 : PB_Message)
  : {desc1 = desc2} + {desc1 <> desc2}.
Proof.
  all : repeat decide equality.
  destruct desc1 as [n1 desc1], desc2 as [n2 desc2].
  destruct (Nat.eq_dec n1 n2). {
    destruct e.
    assert ({desc1 = desc2} + {desc1 <> desc2}) as L. {
      apply vec_eq_dec. auto.
    }
    clear PB_Message_eq_dec.
    destruct L.
    - left. subst. reflexivity.
    - right. inversion 1.
      existT_eq_dec. easy.
  } {
    right. inversion 1. easy.
  }
Defined.

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

Definition PB_Message_default (desc : PB_Message) : PB_Message_denote desc :=
  match desc with
  | Build_PB_Message _ desc => PB_Message_default' desc
  end.

(* :TODO: show equivalence of two default functions. *)
Definition PB_Message_default2 (desc : PB_Message) := PB_Message_default' (PB_MessageDesc desc).

Lemma PB_Message_tags_correct (desc : PB_Message)
  : forall i, Vector.nth (PB_Message_tags desc) i
         = PB_FieldTag (Vector.nth (PB_MessageDesc desc) i).
Proof.
  destruct desc as [n desc]. simpl in *.
  unfold PB_Message_tags. simpl.
  intros. apply Vector.nth_map. reflexivity.
Qed.

Definition PB_FieldTag_OK (t : N) :=
  ((1 <= t <= 18999) \/ (20000 <= t <= 536870911))%N.

Definition PB_FieldName_OK (n : string) :=
  n <> EmptyString.

Definition PB_Field_OK (fld : PB_Field) :=
  PB_FieldName_OK (PB_FieldName fld) /\
  PB_FieldTag_OK (PB_FieldTag fld).

Definition PB_Message_tags_nodup (desc : PB_Message) :=
  forall i1 i2 : Fin.t (PB_MessageLen desc),
    Vector.nth (PB_Message_tags desc) i1 = Vector.nth (PB_Message_tags desc) i2 ->
    i1 = i2.

Lemma vec_nodup_cons {A n} (h : A) (v : Vector.t A n)
  : (forall i1 i2 : Fin.t (S n), Vector.nth (Vector.cons _ h _ v) i1 = Vector.nth (Vector.cons _ h _ v) i2 -> i1 = i2) ->
    (forall i1 i2 : Fin.t n, Vector.nth v i1 = Vector.nth v i2 -> i1 = i2).
Proof.
  intros.
  destruct (Fin.eq_dec i1 i2); auto.
  exfalso.
  specialize (H (Fin.FS i1) (Fin.FS i2)).
  simpl in H. apply H in H0. inversion H0. existT_eq_dec. easy.
Qed.

Definition PB_Message_names_nodup (desc : PB_Message) :=
  forall i1 i2 : Fin.t (PB_MessageLen desc),
    Vector.nth (Vector.map PB_FieldName (PB_MessageDesc desc)) i1 = Vector.nth (Vector.map PB_FieldName (PB_MessageDesc desc)) i2 ->
    i1 = i2.

Fixpoint PB_Message_OK (desc : PB_Message) : Prop :=
  Vector.Forall PB_Field_OK (PB_MessageDesc desc) /\
  PB_Message_tags_nodup desc /\ PB_Message_names_nodup desc /\
  match desc with
  | Build_PB_Message n desc =>
    (fix OK {n} (desc : PB_Desc n) :=
       match desc with
       | Vector.nil => True
       | Vector.cons h _ t =>
         match h with
         | Build_PB_Field ty _ _ =>
           match ty with
           | PB_Singular (PB_Embedded desc'')
           | PB_Repeated (PB_Embedded desc'') =>
             PB_Message_OK desc''
           | _ => True
           end
         end /\ OK t
       end) n desc
  end.

Theorem PB_Message_OK_sub (desc : PB_Message)
  : PB_Message_OK desc ->
    forall fld, Vector.In fld (PB_MessageDesc desc) ->
           forall desc', (PB_FieldType fld = PB_Singular (PB_Embedded desc') \/
                     PB_FieldType fld = PB_Repeated (PB_Embedded desc')) ->
                    PB_Message_OK desc'.
Proof.
  destruct desc as [n desc]. simpl.
  intros. induction H0.
  - destruct fld; destruct p; destruct p; intuition; try easy; injections; auto.
  - apply IHIn. destruct H as [? [? [? [? ?]]]].
    repeat split; auto.
    + inversion H. existT_eq_dec. congruence.
    + unfold PB_Message_tags_nodup in *. eapply vec_nodup_cons. simpl in *. eauto.
    + unfold PB_Message_names_nodup in *. eapply vec_nodup_cons. simpl in *. eauto.
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
    = ith2 (PB_Message_default2 desc) i.
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Qed.

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

Theorem BoundedTag_not_unbounded (desc : PB_Message)
  : forall (t1 : BoundedTag desc) (t2 : UnboundedTag desc), bindex t1 <> uindex t2.
Proof.
  intros. intro. pose proof (BoundedTag_in _ t1). destruct t2. simpl in *.
  subst. easy.
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

Theorem PB_Message_boundedTag_inv (desc : PB_Message)
  : PB_Message_OK desc -> forall tag, PB_Message_boundedTag desc (bindex tag) = inl tag.
Proof.
  intros. destruct (PB_Message_boundedTag desc (bindex tag)) eqn:?.
  apply PB_Message_boundedTag_correct in Heqs.
  apply BoundedTag_inj in Heqs; eauto. subst. auto.
  exfalso. apply PB_Message_boundedTag_correct' in Heqs.
  destruct tag as [? [? ?]]. destruct u. simpl in *.
  subst. apply uboundi0. apply vector_in.
Qed.

Theorem PB_Message_boundedTag_notr (desc : PB_Message)
  : PB_Message_OK desc -> forall (tag : BoundedTag desc) utag, PB_Message_boundedTag desc (bindex tag) <> inr utag.
Proof.
  intros. intro. apply PB_Message_boundedTag_correct' in H0.
  destruct desc. destruct tag as [? [? ?]]; destruct utag. simpl in *. subst.
  apply uboundi0. apply vector_in.
Qed.

Theorem PB_Message_boundedTag_notl (desc : PB_Message)
  : PB_Message_OK desc -> forall (utag : UnboundedTag desc) tag, PB_Message_boundedTag desc (uindex utag) <> inl tag.
Proof.
  intros. intro. apply PB_Message_boundedTag_correct in H0.
  destruct desc. destruct tag as [? [? ?]]; destruct utag. simpl in *. subst.
  apply uboundi0. apply vector_in.
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
  apply Fin.caseS; intros.
  - subst. eapply PB_Field_inj; eauto. constructor.
  - eapply PB_Field_inj; eauto; clear H; simpl in *. constructor. apply vector_in.
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

Theorem PB_Message_OK_sub_tagToType (desc : PB_Message)
  : PB_Message_OK desc ->
    forall (tag : BoundedTag desc) desc',
      (PB_Message_tagToType tag = PB_Singular (PB_Embedded desc') \/
       PB_Message_tagToType tag = PB_Repeated (PB_Embedded desc')) ->
      PB_Message_OK desc'.
Proof.
  intros. eapply PB_Message_OK_sub in H; eauto.
  destruct desc as [n desc]. destruct tag as [? [? ?]]. simpl.
  apply vector_in.
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

Lemma N_land_lor_shiftl
  : forall a b n, N.lt (N.log2 b) n ->
             b = N.land (N.lor (N.shiftl a n) b) (N.ones n).
Proof.
  intros.
  rewrite N.land_lor_distr_l.
  rewrite N.land_ones.
  rewrite N.shiftl_mul_pow2.
  rewrite N.mod_mul by (apply N.pow_nonzero; easy).
  rewrite N.land_ones_low by auto.
  apply N.lor_0_l.
Qed.

Lemma decides_N_eq
  : forall (n n' : N),
    decides (N.eqb n n') (n = n').
Proof.
  unfold decides, If_Then_Else; intros;
    destruct (N.eqb_spec n n'); auto.
Qed.
Hint Resolve decides_N_eq : decide_data_invariant_db.

Inductive PB_IRElm : Type :=
| Build_PB_IRElm : N ->
                   forall PB_IRType : PB_WireType,
                     PB_WireType_denote PB_IRType +
                     list (PB_WireType_denote PB_IRType) +
                     list PB_IRElm ->
                     PB_IRElm.

Section PB_IRElm_induction.
  Variable P : PB_IRElm -> Prop.
  Hypothesis f1 : forall n w s, P (Build_PB_IRElm n w (inl s)).
  Hypothesis f2 : forall n w l, Forall P l -> P (Build_PB_IRElm n w (inr l)).

  Fixpoint PB_IRElm_ind' (e : PB_IRElm)
    : P e.
  Proof.
    destruct e. destruct s.
    auto.
    apply f2. induction l; auto.
  Defined.
End PB_IRElm_induction.

Definition PB_IRTag (elm : PB_IRElm) :=
  let (t, _, _) := elm in t.

Definition PB_IRType (elm : PB_IRElm) :=
  let (_, ty, _) := elm in ty.

Definition PB_IRVal (elm : PB_IRElm) :=
  let (_, ty, v)
      return (PB_WireType_denote (PB_IRType elm) +
              list (PB_WireType_denote (PB_IRType elm)) +
              list PB_IRElm) := elm in v.

Fixpoint PB_IRElm_OK (desc : PB_Message) (elm : PB_IRElm) :=
  match elm with
  | Build_PB_IRElm t ty val =>
    match PB_Message_boundedTag desc t with
    | inl tag =>
      match PB_Message_tagToType tag with
      | PB_Singular (PB_Primitive pty) =>
        match val with
        | inl (inl _) => PB_PrimitiveType_toWireType pty = ty
        | _ => False
        end
      | PB_Repeated (PB_Primitive pty) =>
        match val with
        | inl (inl _) => PB_PrimitiveType_toWireType pty = ty
        | inl (inr _) => PB_PrimitiveType_toWireType pty = ty /\ ty <> PB_LengthDelimited
        | _ => False
        end
      | PB_Singular (PB_Embedded desc')
      | PB_Repeated (PB_Embedded desc') =>
        match val with
        | inr ir =>
          ty = PB_LengthDelimited /\
          (fix IR_OK ir :=
             match ir with
             | nil => True
             | elm' :: ir' => PB_IRElm_OK desc' elm' /\ IR_OK ir'
             end) ir
        | _ => False
        end
      end
    | inr tag =>
      match val with
      | inl (inl _) => True
      | _ => False
      end
    end
  end.

Lemma PB_IRElm_OK_equiv (desc : PB_Message) (ir : list PB_IRElm)
  : (fix IR_OK ir :=
       match ir with
       | nil => True
       | elm' :: ir' => PB_IRElm_OK desc elm' /\ IR_OK ir'
       end) ir <->
    (forall elm, In elm ir -> PB_IRElm_OK desc elm).
Proof.
  split. {
    induction ir; intros. easy. intuition.
    destruct H0; subst; auto.
  } {
    induction ir; intros. easy. intuition.
    apply IHir. intros. apply H.
    intuition.
  }
Qed.


Definition PB_IRElm_toWireType (elm : PB_IRElm) :=
  match PB_IRVal elm with
  | inl (inl _) => PB_IRType elm
  | _ => PB_LengthDelimited
  end.

Section PB_IRElm_body.

  Variable format : FormatM PB_IRElm ByteString.
  Variable decode : PB_Message -> DecodeM PB_IRElm ByteString.
  Variable format_sz_eq : forall x b1 b2 ce1 ce1' ce2 ce2', format x ce1 ↝ (b1, ce1') ->
                                                         format x ce2 ↝ (b2, ce2') ->
                                                         bin_measure b1 = bin_measure b2.
  Variable format_byte : forall d b ce ce', format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
  Variable decode_lt : forall desc b cd x b' cd', decode desc b cd = Some (x, b', cd') -> lt_B b' b.
  Variable P : CacheDecode -> Prop.
  Variable P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)).
  Variable decode_correct : forall desc', CorrectDecoder _ (PB_IRElm_OK desc') (fun _ _ => True) format (decode desc') P.

Definition PB_IRVal_format 
  : FormatM PB_IRElm ByteString :=
  fun elm =>
    match elm with
    | Build_PB_IRElm _ ty val =>
      match val with
      | inl (inl v) => PB_WireType_format ty v
      | inl (inr l) => PB_LengthDelimited_format (PB_WireType_format ty) l
      | inr ir => PB_LengthDelimited_format format ir
      end
    end.

(* :TODO: can we synthesize this? *)
Definition PB_IRVal_decode
           (desc : PB_Message)
           (t : N) (w : N)
  : DecodeM PB_IRElm ByteString :=
  fun b cd =>
    match PB_WireType_val_inv w with
    | inleft wty =>
      match PB_Message_boundedTag desc t with
      | inl tag =>
        match PB_Message_tagToType tag with
        | PB_Singular (PB_Primitive pty) =>
          if PB_WireType_eq_dec (PB_PrimitiveType_toWireType pty) wty then
            `(v, b', cd') <- PB_WireType_decode wty b cd;
              Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
          else None
        | PB_Repeated (PB_Primitive pty) =>
          if PB_WireType_eq_dec (PB_PrimitiveType_toWireType pty) wty then
            `(v, b', cd') <- PB_WireType_decode wty b cd;
              Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
          else if PB_WireType_eq_dec PB_LengthDelimited wty then
                 let wty := (PB_PrimitiveType_toWireType pty) in
                 `(l, b', cd') <- PB_LengthDelimited_decode (PB_WireType_decode wty) (PB_WireType_decode_lt wty) b cd;
                   Some (Build_PB_IRElm t wty (inl (inr l)), b', cd')
               else None
        | PB_Singular (PB_Embedded desc')
        | PB_Repeated (PB_Embedded desc') =>
          if PB_WireType_eq_dec PB_LengthDelimited wty then
            `(ir, b', cd') <- PB_LengthDelimited_decode (decode desc') (decode_lt desc') b cd;
              Some (Build_PB_IRElm t PB_LengthDelimited (inr ir), b', cd')
          else None
        end
      | inr tag =>
        `(v, b', cd') <- PB_WireType_decode wty b cd;
          Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
      end
    | inright _ => None
    end.

Local Opaque PB_LengthDelimited_decode.
Theorem PB_IRVal_decode_correct
        (desc : PB_Message)
  : forall (t : N) (w : N),
    CorrectDecoder _
                   (fun elm => PB_IRTag elm = t /\
                            PB_WireType_val (PB_IRElm_toWireType elm) = w /\
                            PB_IRElm_OK desc elm)
                   (fun _ _ => True)
                   PB_IRVal_format (PB_IRVal_decode desc t w) P.
Proof.
  unfold PB_IRElm_OK, PB_IRVal_format, PB_IRVal_decode, PB_IRElm_toWireType. simpl.
  destruct desc as [n desc].
  intros. split; intros.
  - intuition. destruct data as [tag wty val].
    destruct PB_WireType_val_inv eqn:?; subst;
      rewrite PB_WireType_val_inv_correct in Heqs; [| easy].
    simpl in *. subst.
    destruct PB_Message_boundedTag eqn:?. {
      destruct PB_Message_tagToType eqn:?; destruct p0.
      - destruct val; [destruct s |]; try easy. injections.
        destruct PB_WireType_eq_dec; [| easy].
        edestruct PB_WireType_decode_correct as [[? [? [? ?]]] _]; eauto.
        rewrite H0. simpl. eauto.
      - destruct val; [easy |]. injections. intuition.
        destruct PB_WireType_eq_dec; [| easy]. subst. 
        edestruct (PB_LengthDelimited_decode_correct (A:=PB_IRElm))
          as [[? [? [? ?]]] _]; eauto. instantiate (1 := p0).
        apply PB_IRElm_OK_equiv. apply H3.
        eapply SizedList_predicate_rest_True.
        rewrite H0. simpl. eauto.
      - destruct val; try easy. injections.
        destruct PB_WireType_eq_dec.
        + destruct s; intuition; subst; [| easy].
          edestruct PB_WireType_decode_correct as [[? [? [? ?]]] _]; eauto.
          rewrite H0. simpl. eauto.
        + destruct s; try easy. destruct PB_WireType_eq_dec; try easy. intuition. subst.
          edestruct (PB_LengthDelimited_decode_correct (A:=(PB_WireType_denote (PB_PrimitiveType_toWireType p0))))
            as [[? [? [? ?]]] _]; eauto.
          eapply PB_WireType_format_sz_eq; eauto.
          eapply PB_WireType_format_byte; eauto.
          eapply PB_WireType_decode_correct; eauto.
          intuition. eapply SizedList_predicate_rest_True.
          rewrite H0. simpl. eauto.
      - destruct val; [easy |]. injections. intuition.
        destruct PB_WireType_eq_dec; [| easy]. subst. 
        edestruct (PB_LengthDelimited_decode_correct (A:=PB_IRElm))
          as [[? [? [? ?]]] _]; eauto. instantiate (1 := p0).
        apply PB_IRElm_OK_equiv. apply H3.
        eapply SizedList_predicate_rest_True.
        rewrite H0. simpl. eauto.
    } {
      destruct val; [destruct s |]; try easy. injections.
      edestruct PB_WireType_decode_correct as [[? [? [? ?]]] _]; eauto.
      simpl in *. rewrite H0. simpl. eauto.
    }
  - destruct data as [tag wty val].
    destruct PB_WireType_val_inv eqn:?; [| easy].
    apply PB_WireType_val_inv_correct' in Heqs.
    simpl in *.
    destruct PB_Message_boundedTag eqn:?. {
      destruct PB_Message_tagToType eqn:?; destruct p0.
      - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
        subst. existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        intuition. eexists _, _. intuition; eauto.
        rewrite Heqs0.
        destruct PB_Message_tagToType; destruct p; injections; easy.
      - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
        subst. existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct (PB_LengthDelimited_decode_correct (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
        destruct PB_Message_tagToType; destruct p; injections; try easy.
        intuition. apply (PB_IRElm_OK_equiv p0). eauto.
      - destruct PB_WireType_eq_dec. decode_opt_to_inv.
        subst. existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
        destruct PB_Message_tagToType; destruct p; injections; easy.
        destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
        subst. existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct (PB_LengthDelimited_decode_correct (A:=(PB_WireType_denote (PB_PrimitiveType_toWireType p0))))
          as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        eapply PB_WireType_format_sz_eq; eauto.
        eapply PB_WireType_format_byte; eauto.
        eapply PB_WireType_decode_correct; eauto.
        intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
        destruct PB_Message_tagToType; destruct p; injections; easy.
      - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
        subst. existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct (PB_LengthDelimited_decode_correct (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
        destruct PB_Message_tagToType; destruct p; injections; try easy.
        intuition. apply (PB_IRElm_OK_equiv p0). eauto.
    } {
      decode_opt_to_inv.
      subst. existT_eq_dec; try apply PB_WireType_eq_dec.
      subst. simpl.
      edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
      intuition. eexists _, _. intuition; eauto. rewrite Heqs0. easy.
    }
Qed.

Definition PB_IRElm_format_body (elm : PB_IRElm) :=
  Varint_format (N.lor
                   (N.shiftl (PB_IRTag elm) 3)
                   (PB_WireType_val (PB_IRElm_toWireType elm)))
  ThenC PB_IRVal_format elm
  DoneC.

Definition PB_IRElm_body_decoder (desc : PB_Message)
  : CorrectDecoderFor (PB_IRElm_OK desc) PB_IRElm_format_body.
Proof.
  unfold PB_IRElm_OK, PB_IRElm_format_body.
  eapply Start_CorrectDecoderFor; simpl.
  - decode_step idtac.
    apply Varint_decode_correct.
    decode_step idtac.
    decode_step idtac.
    decode_step idtac.
    intros. apply (PB_IRVal_decode_correct desc)
              with (t := N.shiftr proj 3)
                   (w := N.land proj 7).
    intros ? [? ?]. repeat split; eauto; subst.
    apply N_shiftr_lor_shiftl. apply PB_WireType_val_3bits.
    apply N_land_lor_shiftl. apply PB_WireType_val_3bits.
    decode_step idtac.
    decode_step idtac.
  - cbv beta; synthesize_cache_invariant.
  - cbv beta; optimize_decoder_impl.
Defined.

Definition PB_IRElm_decode_body (desc : PB_Message) :=
  Eval simpl in fst (proj1_sig (PB_IRElm_body_decoder desc)).

Definition PB_IRElm_decode_body_correct (desc : PB_Message)
  : CorrectDecoder _
                   (PB_IRElm_OK desc)
                   (fun _ _ => True)
                   PB_IRElm_format_body (PB_IRElm_decode_body desc) P.
Proof.
  destruct (proj2_sig (PB_IRElm_body_decoder desc)) as [? [? ?]].
  apply H. simpl in *. auto.
Qed.

Theorem PB_IRElm_format_body_sz_eq
  : forall x b1 b2 ce1 ce1' ce2 ce2',
    PB_IRElm_format_body x ce1 ↝ (b1, ce1') ->
    PB_IRElm_format_body x ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_IRElm_format_body. intros.
  computes_to_inv2.
  rewrite !(@mappend_measure _ ByteStringQueueMonoid).
  f_equal.
  eapply Varint_format_sz_eq; eauto.
  f_equal.
  unfold PB_IRVal_format in *.
  destruct x. destruct s; try destruct s.
  eapply PB_WireType_format_sz_eq; eauto.
  eapply PB_LengthDelimited_format_sz_eq; [eapply PB_WireType_format_sz_eq | |]; eauto.
  eapply PB_LengthDelimited_format_sz_eq; [eapply format_sz_eq | |]; eauto.
Qed.

Theorem PB_IRElm_format_body_byte
  : forall d b ce ce',
    PB_IRElm_format_body d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
Proof.
  unfold PB_IRElm_format_body. intros.
  computes_to_inv2.
  rewrite !(@mappend_measure _ ByteStringQueueMonoid).
  rewrite <- Nat.add_mod_idemp_l by auto.
  erewrite Varint_format_byte; eauto.
  rewrite Nat.add_0_l.
  rewrite <- Nat.add_mod_idemp_l by auto.
  replace (bin_measure b1 mod 8) with 0.
  auto.
  symmetry.
  unfold PB_IRVal_format in *.
  destruct d; destruct s; try destruct s.
  eapply PB_WireType_format_byte; eauto.
  eapply PB_LengthDelimited_format_byte; [eapply PB_WireType_format_byte |]; eauto.
  eapply PB_LengthDelimited_format_byte; [eapply format_byte |]; eauto.
Qed.

Theorem PB_IRElm_decode_body_lt
  : forall desc b cd x b' cd', PB_IRElm_decode_body desc b cd = Some (x, b', cd') -> lt_B b' b.
Proof.
  unfold PB_IRElm_decode_body. intros.
  decode_opt_to_inv. destruct N.eqb; [| easy]. injections.
  apply Varint_decode_lt in H.
  unfold PB_IRVal_decode in *.
  repeat match goal with
  | H : match ?a with _ => _ end = _ |- _ => destruct a
  end; try easy; decode_opt_to_inv; subst.
  apply PB_WireType_decode_lt in H0. unfold lt_B in *. omega.
  apply PB_LengthDelimited_decode_lt in H0. unfold lt_B in *. omega.
  apply PB_WireType_decode_lt in H0. unfold lt_B in *. omega.
  apply PB_LengthDelimited_decode_lt in H0. unfold lt_B in *. omega.
  apply PB_LengthDelimited_decode_lt in H0. unfold lt_B in *. omega.
  apply PB_WireType_decode_lt in H0. unfold lt_B in *. omega.
Qed.

Local Transparent PB_LengthDelimited_decode.
End PB_IRElm_body.

(* Definition PB_IRElm_decode' *)
(*   : forall b : ByteString, PB_Message -> CacheDecode -> *)
(*                       option (PB_IRElm * ByteString * CacheDecode). *)
(* Proof. *)
(*   refine (Fix well_founded_lt_b _ *)
(*               (fun b rec desc cd => *)
(*                  exist *)
(*                    _ *)
(*                    (`(a, b0, cd0) <- Varint_decode b cd; *)
(*                     `() <- SizedList_decode PB_IRElm_decode' _ b0 cd0) *)
(*                    (PB_IRElm_decode_body (fun desc' b' cd' => proj1_sig (rec b' _ desc' cd')) _ desc b cd) *)
(*                    _)). *)

(* Definition PB_IRElm_decode' *)
(*   : forall b : ByteString, PB_Message -> CacheDecode -> *)
(*     {a : option (PB_IRElm * ByteString * CacheDecode) | *)
(*      forall elm b' cd', a = Some (elm, b', cd') -> lt_B b' b}. *)
(* Proof. *)
(*   refine (Fix well_founded_lt_b _ *)
(*               (fun b rec desc cd => *)
(*                  exist *)
(*                    _ *)
(*                    (PB_IRElm_decode_body (fun desc' b' cd' => proj1_sig (rec b' _ desc' cd')) _ desc b cd) *)
(*                    _)). *)
(*   intros. *)
(*   apply PB_IRElm_decode_body_lt in H. assumption. *)
(*   Show Proof. *)
(*   Grab Existential Variables. *)
(*   intros. *)
(*   destruct rec. simpl in *. eauto. *)

Definition PB_IR := list PB_IRElm.

Definition PB_IR_measure' f :=
  fix ir_measure (ir : PB_IR) :=
    match ir with
    | nil => 0
    | elm :: ir' =>
      f elm + ir_measure ir'
    end.
Arguments PB_IR_measure' /.

Fixpoint PB_IRElm_measure (elm : PB_IRElm) :=
  match elm with
  | Build_PB_IRElm _ _ v =>
    1 + match v with
        | inr ir =>
          PB_IR_measure' PB_IRElm_measure ir
        | _ => 0
        end
  end.

Definition PB_IR_measure (ir : PB_IR) := PB_IR_measure' PB_IRElm_measure ir.

Theorem PB_IR_mappend_measure
  : forall ir ir', PB_IR_measure (ir ++ ir') = (PB_IR_measure ir) + (PB_IR_measure ir').
Proof.
  induction ir; intros. easy.
  simpl. specialize (IHir ir').
  omega.
Qed.

Instance PB_IR_monoid : Monoid PB_IR :=
  {| mappend := @app _;
     bin_measure := PB_IR_measure;
     mempty := nil;
     mappend_measure := PB_IR_mappend_measure;
     mempty_left := @app_nil_l _;
     mempty_right := @app_nil_r _;
     mappend_assoc := @app_assoc _
  |}.

Lemma PB_IR_measure_cons_lt (ir : PB_IR)
  : forall elm, lt_B ir (elm :: ir).
Proof.
  unfold lt_B. destruct 0. simpl. omega.
Qed.

Lemma PB_IR_measure_embedded_lt (ir ir' : PB_IR)
  : forall t wty, lt_B ir' (Build_PB_IRElm t wty (inr ir') :: ir).
Proof.
  unfold lt_B. intros. simpl.
  unfold PB_IR_measure. simpl.
  omega.
Qed.

Inductive PB_IR_refine_ref
  : forall {desc : PB_Message}, PB_IR -> PB_Message_denote desc -> Prop :=
| PB_IR_nil_ref desc :
    PB_IR_refine_ref nil
                 (PB_Message_default desc)
| PB_IR_singular_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Primitive pty))
        (v : PB_Type_denote (PB_Singular (PB_Primitive pty))),
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t (eq_rect_r _ v pf))
| PB_IR_repeated_cons_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty))
        (v : PB_Type_denote (PB_Singular (PB_Primitive pty))),
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [v])
                                           pf))
| PB_IR_repeated_app_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty))
        (v : PB_Type_denote (PB_Repeated (PB_Primitive pty))),
        PB_PrimitiveType_toWireType pty <> PB_LengthDelimited ->
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inr v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ v)
                                           pf))
| PB_IR_unknown_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : UnboundedTag desc) (wty : PB_WireType)
        (v : PB_WireType_denote wty),
        PB_IR_refine_ref ((Build_PB_IRElm (uindex t)
                                      wty
                                      (inl (inl v))) :: ir)
                     msg
| PB_IR_embedded_none_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc'))
        v (msg' : PB_Message_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = None ->
        PB_IR_refine_ref v msg' ->
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg') pf))
| PB_IR_embedded_some_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc'))
        v ir' (msg' msg'' : PB_Message_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = Some msg'' ->
        PB_IR_refine_ref ir' msg'' ->
        PB_IR_refine_ref (v ++ ir') msg' ->
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg') pf))
| PB_IR_repeated_embedded_ref desc :
    forall ir (msg : PB_Message_denote desc),
      PB_IR_refine_ref ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Embedded desc'))
        v (msg' : PB_Message_denote desc'),
        PB_IR_refine_ref v msg' ->
        PB_IR_refine_ref ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [msg'])
                                           pf))
.

Inductive PB_IR_refine
  : forall {desc : PB_Message}, PB_Message_denote desc -> PB_IR -> PB_Message_denote desc -> Prop :=
| PB_IR_nil desc :
    forall msg : PB_Message_denote desc, PB_IR_refine msg nil msg
| PB_IR_singular desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Primitive pty))
        (v : PB_Type_denote (PB_Singular (PB_Primitive pty))),
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t (eq_rect_r _ v pf))
| PB_IR_repeated_cons desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty))
        (v : PB_Type_denote (PB_Singular (PB_Primitive pty))),
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [v])
                                           pf))
| PB_IR_repeated_app desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_PrimitiveType)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty))
        (v : PB_Type_denote (PB_Repeated (PB_Primitive pty))),
        PB_PrimitiveType_toWireType pty <> PB_LengthDelimited ->
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_PrimitiveType_toWireType pty)
                                      (inl (inr v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ v)
                                           pf))
| PB_IR_unknown desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : UnboundedTag desc) (wty : PB_WireType)
        (v : PB_WireType_denote wty),
        PB_IR_refine msg'
                     ((Build_PB_IRElm (uindex t)
                                      wty
                                      (inl (inl v))) :: ir)
                     msg
| PB_IR_embedded_none desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc'))
        v (msg'' : PB_Message_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = None ->
        PB_IR_refine (PB_Message_default desc') v msg'' ->
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg'') pf))
| PB_IR_embedded_some desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc'))
        v (msg'' msg''' : PB_Message_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = Some msg'' ->
        PB_IR_refine msg'' v msg''' ->
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg''') pf))
| PB_IR_repeated_embedded desc :
    forall (msg' : PB_Message_denote desc) ir (msg : PB_Message_denote desc),
      PB_IR_refine msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Message)
        (pf : PB_Message_tagToType t = PB_Repeated (PB_Embedded desc'))
        v (msg'' : PB_Message_denote desc'),
        PB_IR_refine (PB_Message_default desc') v msg'' ->
        PB_IR_refine msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [msg''])
                                           pf))
.

Ltac PB_IR_refine_inv_step :=
  match goal with
  | H : bindex ?a = bindex _ |- _ => apply BoundedTag_inj in H; [subst a | solve [eauto]]
  | H : uindex _ = bindex _ |- _ => symmetry in H
  | H : bindex _ = uindex _ |- _ => apply BoundedTag_not_unbounded in H; inversion H
  | H : PB_Message_tagToType ?t = ?c1 (?c2 ?a),
        H' : PB_Message_tagToType ?t = ?c1 (?c2 ?b) |- _ => progress replace b with a in * by congruence
  | H : existT _ _ _ = existT _ _ _ |- _  =>
    apply inj_pair2_eq_dec in H;
    [| clear H; try apply PB_Message_eq_dec || apply PB_WireType_eq_dec];
    subst
  | H : ?a = Some _, H' : ?b = None |- _ => progress replace a with b in *; [congruence | clear H H']
  | H : ?a = Some _, H' : ?b = Some _ |- _ => progress replace a with b in *; [substss; injections | clear H H']
  | |- ?a = ?b => progress f_equal; eauto; try apply (UIP_dec PB_Type_eq_dec)
  | _ => eauto using eq_sym, PB_Message_OK_sub_tagToType; easy || congruence
  end.

Ltac PB_IR_refine_inv hyp :=
  inversion hyp; repeat PB_IR_refine_inv_step.

Theorem PB_IR_refine_deterministic
  : forall desc,
    PB_Message_OK desc ->
    forall (msg' msg1 msg2 : PB_Message_denote desc) ir,
      PB_IR_refine msg' ir msg1 ->
      PB_IR_refine msg' ir msg2 ->
      msg1 = msg2.
Proof.
  intros. induction H0; PB_IR_refine_inv H1.
Qed.

Ltac PB_IR_refine_inv_step_ext :=
  match goal with
  | |- PB_IR_refine ?a nil ?b => replace a with b; [constructor |]
  | _ => eauto using eq_sym, PB_Message_OK_sub_tagToType, PB_IR_refine_deterministic
  end.

Ltac PB_IR_refine_inv hyp ::=
  inversion hyp; repeat first [PB_IR_refine_inv_step | PB_IR_refine_inv_step_ext].

Theorem PB_IR_refine_trans
  : forall desc,
    PB_Message_OK desc ->
    forall (msg1 msg2 msg3 : PB_Message_denote desc) (ir1 ir2 ir3 : PB_IR),
    PB_IR_refine msg1 ir1 msg2 ->
    (PB_IR_refine msg2 ir2 msg3 <-> PB_IR_refine msg1 (ir2 ++ ir1) msg3).
Proof.
  split; intros. {
    induction H1; simpl; eauto; try solve [constructor; eauto].
    eapply PB_IR_embedded_some; eauto.
  } {
    remember (ir2 ++ ir1).
    generalize dependent msg2.
    generalize dependent ir1.
    generalize dependent ir2.
    induction H1; simpl; intros.
    all : destruct ir2; simpl in Heql; injections; subst;
      [match goal with
       | H : PB_IR_refine _ _ ?a |- PB_IR_refine ?a _ _ => solve [PB_IR_refine_inv H]
       end |
       match goal with
       | H : _ = Some _ |- _ => eapply PB_IR_embedded_some; eauto
       | _ => try easy; constructor; eauto
       end].
  }
Qed.

(* Theorem PB_IR_refine_eq' *)
(*   : forall desc, *)
(*     PB_Message_OK desc -> *)
(*     forall ir ir' (msg msg' : PB_Message_denote desc), *)
(*       PB_IR_refine_ref ir' msg' -> *)
(*       PB_IR_refine msg' ir msg -> *)
(*       PB_IR_refine_ref (ir ++ ir') msg. *)
(* Proof. *)
(*   intros. *)
(*   generalize dependent ir'. *)
(*   induction H1; intros; simpl. *)
(*   - auto. *)
(*   - constructor; eauto. *)
(*   - constructor; eauto. *)
(*   - constructor; eauto. *)
(*   - constructor; eauto. *)
(*   - constructor; eauto using PB_Message_OK_sub_tagToType. *)
(*     replace v with (v++nil) by apply app_nil_r. *)
(*     eapply IHPB_IR_refine2; eauto using PB_Message_OK_sub_tagToType. *)
(*     constructor. *)
(*   - admit. *)
(*     (* eapply PB_IR_embedded_some_ref; eauto using PB_Message_OK_sub_tagToType. *) *)
(*   - constructor; eauto using PB_Message_OK_sub_tagToType. *)
(*     replace v with (v++nil) by apply app_nil_r. *)
(*     eapply IHPB_IR_refine2; eauto using PB_Message_OK_sub_tagToType. *)
(*     constructor. *)
(* Qed. *)

(* Theorem PB_IR_refine_eq *)
(*   : forall desc, *)
(*     PB_Message_OK desc -> *)
(*     forall ir (msg : PB_Message_denote desc), *)
(*       PB_IR_refine_ref ir msg <-> PB_IR_refine (PB_Message_default desc) ir msg. *)
(* Proof. *)
(*   intros. split. { *)
(*     induction 1; *)
(*       match goal with *)
(*       | H : _ = Some _ |- _ => eapply PB_IR_embedded_some; eauto *)
(*       | _ => constructor *)
(*       end; eauto using PB_Message_OK_sub_tagToType. *)
(*     eapply PB_IR_refine_trans; eauto using PB_Message_OK_sub_tagToType. *)
(*   } { *)
(*     intros. *)
(*     replace ir with (ir ++ nil) by apply app_nil_r. *)
(*     eapply PB_IR_refine_eq'; eauto. *)
(*     constructor. *)
(*   } *)
(* Qed. *)


Local Transparent computes_to.
Local Transparent Pick.

Ltac choose_br n :=
  match n with
  | O => try left
  | S ?n' => right; choose_br n'
  end.

Ltac destruct_many :=
  repeat first [match goal with
                | H : ?a \/ ?b |- _ => destruct H
                end |
                match goal with
                | [ H : ex _ |- _ ] => destruct H
                end |
                match goal with
                | H : ?a /\ ?b |- _ => destruct H
                end].


Definition PB_Message_IR_format_ref (desc : PB_Message)
  : FormatM (PB_Message_denote desc) PB_IR :=
  fun msg _ => {b | PB_IR_refine_ref (fst b) msg}.

Definition PB_Message_IR_format_strong (desc : PB_Message) (init : PB_Message_denote desc)
  : FormatM (PB_Message_denote desc) PB_IR :=
  fun msg _ => {b | PB_IR_refine init (fst b) msg}.

Definition PB_Message_IR_format (desc : PB_Message)
  : FormatM (PB_Message_denote desc) PB_IR :=
  PB_Message_IR_format_strong desc (PB_Message_default desc).

Definition PB_Message_IR_decode'
  : PB_IR -> forall desc, PB_Message_denote desc -> CacheDecode ->
                    option (PB_Message_denote desc * PB_IR * CacheDecode).
Proof.
  refine
    (Fix well_founded_lt_b _
         (fun ir =>
            match ir with
            | nil => fun decode desc (msg : PB_Message_denote desc) cd => Some (msg, nil, cd)
            | Build_PB_IRElm t wty v :: ir' =>
              fun decode desc (msg : PB_Message_denote desc) cd =>
                match PB_Message_boundedTag desc t with
                | inl tag =>
                  `(msg1, _, cd1) <- decode ir' _ desc msg cd;
                  match PB_Message_tagToType tag as x
                        return (PB_Type_denote x -> PB_Message_denote desc) ->
                               (PB_Type_denote x) ->
                               _ with
                  | PB_Singular (PB_Primitive pty) =>
                    fun f a =>
                      match PB_WireType_eq_dec wty (PB_PrimitiveType_toWireType pty) with
                      | left pf =>
                        match v with
                        | inl (inl v') =>
                          Some (f (eq_rect _ _ v' _ pf), nil, cd1)
                        | _ => None
                        end
                      | _ => None
                      end
                  | PB_Repeated (PB_Primitive pty) =>
                    fun f a =>
                      match PB_WireType_eq_dec wty (PB_PrimitiveType_toWireType pty) with
                      | left pf =>
                        match v with
                        | inl (inl v') =>
                          Some (f (a ++ [(eq_rect _ _ v' _ pf)]), nil, cd1)
                        | inl (inr l) =>
                          if PB_WireType_eq_dec PB_LengthDelimited (PB_PrimitiveType_toWireType pty) then None
                          else Some (f (a ++ (eq_rect _ (fun wty => list (PB_WireType_denote wty)) l _ pf)), nil, cd1)
                        | _ => None
                        end
                      | _ => None
                      end
                  | PB_Singular (PB_Embedded desc') =>
                    fun f a =>
                      match PB_WireType_eq_dec wty PB_LengthDelimited with
                      | left pf =>
                        match v return _ -> _ with
                        | inr ir2 =>
                          fun decode =>
                            match a with
                            | Some msg2 =>
                              `(msg3, _, cd2) <- decode ir2 _ desc' msg2 cd1;
                              Some (f (Some msg3), nil, cd2)
                            | None =>
                              `(msg2, _, cd2) <- decode ir2 _ desc' (PB_Message_default desc') cd1;
                              Some (f (Some msg2), nil, cd2)
                            end
                        | _ => fun _ => None
                        end decode
                      | _ => None
                      end
                  | PB_Repeated (PB_Embedded desc') =>
                    fun f a =>
                      match PB_WireType_eq_dec wty PB_LengthDelimited with
                      | left pf =>
                        match v return _ -> _ with
                        | inr ir2 =>
                          fun decode =>
                            `(msg2, _, cd2) <- decode ir2 _ desc' (PB_Message_default desc') cd1;
                            Some (f (a ++ [msg2]), nil, cd2)
                        | _ => fun _ => None
                        end decode
                      | _ => None
                      end
                  end (PB_Message_update msg1 tag) (PB_Message_lookup msg1 tag)
                | inr _ =>
                  match v with
                  | inl (inl _) => decode ir' _ desc msg cd
                  | _ => None
                  end
                end
            end));
    apply PB_IR_measure_cons_lt || apply PB_IR_measure_embedded_lt.
Defined.

Definition PB_Message_IR_decode_strong (desc : PB_Message) (init : PB_Message_denote desc)
  : DecodeM (PB_Message_denote desc) PB_IR :=
  fun ir cd =>
    PB_Message_IR_decode' ir desc init cd.

Definition PB_Message_IR_decode (desc : PB_Message)
  : DecodeM (PB_Message_denote desc) PB_IR :=
  PB_Message_IR_decode_strong desc (PB_Message_default desc).

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