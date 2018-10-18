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
        Fiat.Common.Frame
        Fiat.Common.BoundedLookup
        Fiat.Common.DecideableEnsembles
        Fiat.Common.EnumType
        Fiat.Common.ilist2
        (* Fiat.Common.Tactics.CacheStringConstant *)
        Fiat.Common.IterateBoundedIndex
        Fiat.Computation
        Fiat.Computation.FixComp
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.Sig
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeIf
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord
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
        Fiat.Narcissus.Formats.WordLEOpt
        Fiat.Narcissus.Formats.StringOpt
        Fiat.Narcissus.Stores.EmptyStore
        Fiat.Narcissus.Automation.Solver
        Fiat.Protobuf.ProtobufLengthDelimited.

Import FixComp.LeastFixedPointFun.

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

(* Other wire types are deprecated. *)
Definition PB_WireType_val (wty : PB_WireType) : N :=
  match wty with
  | PB_Varint => 0
  | PB_32bit => 5
  | PB_64bit => 1
  | PB_LengthDelimited => 2
  end.

(* Convert a number back to wire type. *)
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

(* The value of wire type can fit into 3 bits.  *)
Theorem PB_WireType_val_3bits (wty : PB_WireType)
  : N.lt (N.log2 (PB_WireType_val wty)) 3%N.
Proof.
  destruct wty; easy.
Qed.

(* Default value for wire type. *)
Definition PB_WireType_default (wty : PB_WireType) : PB_WireType_denote wty :=
  match wty with
  | PB_Varint => 0%N
  | PB_32bit => wzero 32
  | PB_64bit => wzero 64
  | PB_LengthDelimited => []
  end.

(* Format a single value. *)
Definition PB_WireType_format (wty : PB_WireType)
  : FormatM (PB_WireType_denote wty) ByteString :=
  match wty with
  | PB_32bit => format_wordLE
  | PB_64bit => format_wordLE
  | PB_Varint => Varint_format
  | PB_LengthDelimited => PB_LengthDelimited_format format_word
  end.

(* A value is always formatted into binary string of the same size. *)
Theorem PB_WireType_format_sz_eq (wty : PB_WireType)
  : forall d b1 b2 ce1 ce1' ce2 ce2',
    PB_WireType_format wty d ce1 ↝ (b1, ce1') ->
    PB_WireType_format wty d ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  unfold PB_WireType_format; intros.
  destruct wty.
  eapply Varint_format_sz_eq; eauto.
  eapply format_wordLE_sz_eq; eauto.
  eapply format_wordLE_sz_eq; eauto.
  eapply PB_LengthDelimited_format_sz_eq; eauto.
  eapply word_format_sz_eq; eauto.
Qed.

(* The formatted binary string is byte-aligned. *)
Theorem PB_WireType_format_byte (wty : PB_WireType)
  : forall d b ce ce',
    PB_WireType_format wty d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  unfold PB_WireType_format.
  destruct wty; intros.
  eapply Varint_format_byte; eauto.
  eapply format_wordLE_byte; eauto; eauto.
  eapply format_wordLE_byte; eauto; eauto.
  eapply PB_LengthDelimited_format_byte; eauto.
  intros. eapply word_format_byte; eauto; eauto.
Qed.

(* A value can never be formatted into empty string *)
Theorem PB_WireType_format_some (wty : PB_WireType)
  : forall d ce b ce',
    PB_WireType_format wty d ce ↝ (b, ce') ->
    lt 0 (bin_measure b).
Proof.
  unfold PB_WireType_format.
  destruct wty; intros.
  apply Varint_format_some in H; eauto.
  apply format_wordLE_some in H; eauto.
  apply format_wordLE_some in H; eauto.
  apply PB_LengthDelimited_format_some in H; eauto.
Qed.

Inductive PB_BaseType : Set :=
| PB_fixed32 : PB_BaseType
| PB_fixed64 : PB_BaseType
| PB_int32 : PB_BaseType
| PB_int64 : PB_BaseType
| PB_bool : PB_BaseType
| PB_string : PB_BaseType
.

(* Any base type is encoded as one of the wire type. *)
Definition PB_BaseType_toWireType (pty : PB_BaseType) : PB_WireType :=
  match pty with
  | PB_fixed32 => PB_32bit
  | PB_fixed64 => PB_64bit
  | PB_int32 => PB_Varint
  | PB_int64 => PB_Varint
  | PB_bool => PB_Varint
  | PB_string => PB_LengthDelimited
  end.

(* Low-level denotation for base type. *)
Definition PB_BaseType_denote (pty : PB_BaseType) : Type :=
  PB_WireType_denote (PB_BaseType_toWireType pty).
Arguments PB_BaseType_denote /.

(* Default value for base type. *)
Definition PB_BaseType_default (pty : PB_BaseType) : PB_BaseType_denote pty :=
  PB_WireType_default (PB_BaseType_toWireType pty).
Arguments PB_BaseType_default /.

(* The mutually inductive definition for Descriptor, Field, Protobuf Type and Base type. *)
Inductive PB_SingularType : Set :=
| PB_Base : PB_BaseType -> PB_SingularType
| PB_Embedded : PB_Descriptor -> PB_SingularType

with PB_Type : Set :=
     | PB_Singular : PB_SingularType -> PB_Type
     | PB_Repeated : PB_SingularType -> PB_Type

with PB_Field : Set :=
     | Build_PB_Field : PB_Type -> string -> N -> PB_Field

with PB_Descriptor : Set :=
     | Build_PB_Descriptor : forall {n}, Vector.t PB_Field n -> PB_Descriptor.

(* Mutual induction principle. *)
Scheme PB_SingularType_mut := Induction for PB_SingularType Sort Prop
  with PB_Type_mut := Induction for PB_Type Sort Prop
  with PB_Field_mut := Induction for PB_Field Sort Prop
  with PB_Descriptor_mut := Induction for PB_Descriptor Sort Prop.

Section PB_Descriptor_induction.
  Variable P_sty : PB_SingularType -> Prop.
  Variable P_ty : PB_Type -> Prop.
  Variable P_fld : PB_Field -> Prop.
  Variable P_desc : PB_Descriptor -> Prop.
  Variable f0 : forall pty : PB_BaseType, P_sty (PB_Base pty).
  Variable f1 : forall desc : PB_Descriptor, P_desc desc -> P_sty (PB_Embedded desc).
  Variable f2 : forall sty : PB_SingularType, P_sty sty -> P_ty (PB_Singular sty).
  Variable f3 : forall sty : PB_SingularType, P_sty sty -> P_ty (PB_Repeated sty).
  Variable f4 : forall ty : PB_Type, P_ty ty -> forall (s : string) (n : N), P_fld (Build_PB_Field ty s n).
  Variable f5 : forall (n : nat) (v : Vector.t PB_Field n), Vector.Forall P_fld v -> P_desc (Build_PB_Descriptor v).

  Fixpoint PB_SingularType_ind' (sty : PB_SingularType) : P_sty sty
  with PB_Type_ind' (ty : PB_Type) : P_ty ty
  with PB_Field_ind' (fld : PB_Field) : P_fld fld
  with PB_Descriptor_ind' (desc : PB_Descriptor) : P_desc desc.
  Proof.
    destruct sty. apply f0. apply f1. auto.
    destruct ty. apply f2. auto. apply f3. auto.
    destruct fld. apply f4. auto.
    destruct desc as [n desc]. apply f5.
    induction desc; constructor; auto.
  Defined.

End PB_Descriptor_induction.

(* Handy helper functions for accessing the projections.. *)
Definition PB_FieldType (fld : PB_Field) := let (ty, _, _) := fld in ty.
Definition PB_FieldName (fld : PB_Field) := let (_, name, _) := fld in name.
Definition PB_FieldTag (fld : PB_Field) := let (_, _, tag) := fld in tag.

Definition PB_Desc := Vector.t PB_Field.

Definition PB_DescriptorLen (desc : PB_Descriptor) :=
  let (n, _) := desc in n.

Definition PB_DescriptorDesc (desc : PB_Descriptor) :=
  let (_, v) return (Vector.t _ (PB_DescriptorLen desc)) := desc in v.

(* Get the list of tags from the descriptor. *)
Definition PB_Descriptor_tags' {n} (desc : PB_Desc n) :=
  Vector.map PB_FieldTag desc.

Definition PB_Descriptor_tags (desc : PB_Descriptor) :=
  PB_Descriptor_tags' (PB_DescriptorDesc desc).

(* Sanity check for tags function. *)
Lemma PB_Descriptor_tags_correct (desc : PB_Descriptor)
  : forall i, Vector.nth (PB_Descriptor_tags desc) i
         = PB_FieldTag (Vector.nth (PB_DescriptorDesc desc) i).
Proof.
  destruct desc as [n desc]. simpl in *.
  unfold PB_Descriptor_tags. simpl.
  intros. apply Vector.nth_map. reflexivity.
Qed.


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

(* Equality of Descriptor is decidable. *)
Fixpoint PB_SingularType_eq_dec (sty1 sty2 : PB_SingularType)
  : {sty1 = sty2} + {sty1 <> sty2}
with PB_Type_eq_dec (ty1 ty2 : PB_Type)
     : {ty1 = ty2} + {ty1 <> ty2}
with PB_Field_eq_dec (fld1 fld2 : PB_Field)
     : {fld1 = fld2} + {fld1 <> fld2}
with PB_Descriptor_eq_dec (desc1 desc2 : PB_Descriptor)
  : {desc1 = desc2} + {desc1 <> desc2}.
Proof.
  all : repeat decide equality.
  destruct desc1 as [n1 desc1], desc2 as [n2 desc2].
  destruct (Nat.eq_dec n1 n2). {
    destruct e.
    assert ({desc1 = desc2} + {desc1 <> desc2}) as L. {
      apply vec_eq_dec. auto.
    }
    clear PB_Descriptor_eq_dec.
    destruct L.
    - left. subst. reflexivity.
    - right. inversion 1.
      existT_eq_dec. easy.
  } {
    right. inversion 1. easy.
  }
Defined.

(* The low-level denotation of Descriptors, Fields, Protobuf type and Base type.
   We use the Tuple type in Fiat, which is essentially a heterogeneous list,
   supporting bounded element access. *)
Definition PB_Descriptor_heading' denote (desc : PB_Descriptor) :=
  BuildHeading (Vector.map denote (PB_DescriptorDesc desc)).
Arguments PB_Descriptor_heading' /.

Fixpoint PB_Type_denote (ty : PB_Type) : Type :=
  match ty with
  | PB_Singular sty =>
    match sty with
    | PB_Base pty => PB_BaseType_denote pty
    | PB_Embedded desc => option (PB_Descriptor_denote desc)
    end
  | PB_Repeated sty =>
    match sty with
    | PB_Base pty => list (PB_BaseType_denote pty)
    | PB_Embedded desc => list (PB_Descriptor_denote desc)
    end
  end

with PB_Field_denote (fld : PB_Field) : Attribute :=
       ((PB_FieldName fld) :: PB_Type_denote (PB_FieldType fld))%Attribute

with PB_Descriptor_denote (desc : PB_Descriptor) : Type :=
       @Tuple (PB_Descriptor_heading' PB_Field_denote desc).

Definition PB_Descriptor_heading := PB_Descriptor_heading' PB_Field_denote.

(* The default value of descriptor. *)
Definition PB_Type_default (ty : PB_Type) : PB_Type_denote ty :=
  match ty with
  | PB_Singular sty =>
    match sty with
    | PB_Base pty => PB_BaseType_default pty
    | PB_Embedded _ => None
    end
  | PB_Repeated sty =>
    match sty with
    | PB_Base _ => nil
    | PB_Embedded _ => nil
    end
  end.

Fixpoint PB_Descriptor_default' {n} (desc : PB_Desc n) : PB_Descriptor_denote (Build_PB_Descriptor desc).
Proof.
  refine
    (match desc return (PB_Descriptor_denote (Build_PB_Descriptor desc)) with
     | Vector.nil => inil2 (B:=id)
     | Vector.cons fld _ desc' =>
       icons2 (B:=id) _ (PB_Descriptor_default' _ desc')
     end).
  destruct fld as [ty ? ?].
  exact (PB_Type_default ty).
Defined.

Definition PB_Descriptor_default (desc : PB_Descriptor) : PB_Descriptor_denote desc :=
  match desc with
  | Build_PB_Descriptor _ desc => PB_Descriptor_default' desc
  end.

(* Tag has to be in a range by the specification, although it is not important
   for our implementation. *)
Definition PB_FieldTag_OK (t : N) :=
  ((1 <= t <= 18999) \/ (20000 <= t <= 536870911))%N.

(* Decision procedure for checking tag. *)
(* TODO: use Decidable module to synthesize it. *)
Definition PB_FieldTag_OK_dec (t : N) :=
  (((N.leb 1 t) && (N.leb t 18999)) || ((N.leb 20000 t) && (N.leb t 536870911)))%bool.

Definition PB_FieldTag_OK_true_iff (t : N)
  : PB_FieldTag_OK_dec t = true <-> (PB_FieldTag_OK t).
Proof.
  unfold PB_FieldTag_OK, PB_FieldTag_OK_dec.
  repeat match goal with
         | |- context [N.leb ?a ?b] => destruct (N.leb_spec a b)
         end; simpl; auto; split; auto; intros; try easy; destruct_many;
    match goal with
    | H : N.lt ?a ?b, H' : N.le ?b ?a |- _ => apply N.lt_nge in H; easy
    end.
Qed.

Definition PB_FieldTag_OK_false_iff (t : N)
  : PB_FieldTag_OK_dec t = false <-> ~ (PB_FieldTag_OK t).
Proof.
  split; intros. intro. apply PB_FieldTag_OK_true_iff in H0. congruence.
  destruct PB_FieldTag_OK_dec eqn:?; auto.
  apply PB_FieldTag_OK_true_iff in Heqb. congruence.
Qed.

(* Field name can not be empty. *)
Definition PB_FieldName_OK (n : string) :=
  n <> EmptyString.

Definition PB_Field_OK (fld : PB_Field) :=
  PB_FieldName_OK (PB_FieldName fld) /\
  PB_FieldTag_OK (PB_FieldTag fld).

(* Tags are unique. *)
Definition PB_Descriptor_tags_nodup (desc : PB_Descriptor) :=
  forall i1 i2 : Fin.t (PB_DescriptorLen desc),
    Vector.nth (PB_Descriptor_tags desc) i1 = Vector.nth (PB_Descriptor_tags desc) i2 ->
    i1 = i2.

(* Names are unique. *)
Definition PB_Descriptor_names_nodup (desc : PB_Descriptor) :=
  forall i1 i2 : Fin.t (PB_DescriptorLen desc),
    Vector.nth (Vector.map PB_FieldName (PB_DescriptorDesc desc)) i1 = Vector.nth (Vector.map PB_FieldName (PB_DescriptorDesc desc)) i2 ->
    i1 = i2.

(* Predicate for valid descriptor. *)
Fixpoint PB_Descriptor_OK (desc : PB_Descriptor) : Prop :=
  Vector.Forall PB_Field_OK (PB_DescriptorDesc desc) /\
  PB_Descriptor_tags_nodup desc /\ PB_Descriptor_names_nodup desc /\
  match desc with
  | Build_PB_Descriptor n desc =>
    (fix OK {n} (desc : PB_Desc n) :=
       match desc with
       | Vector.nil => True
       | Vector.cons h _ t =>
         match h with
         | Build_PB_Field ty _ _ =>
           match ty with
           | PB_Singular (PB_Embedded desc'')
           | PB_Repeated (PB_Embedded desc'') =>
             PB_Descriptor_OK desc''
           | _ => True
           end
         end /\ OK t
       end) n desc
  end.

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

(* Descriptor is valid implies all of its embedded descriptors are valid. *)
Theorem PB_Descriptor_OK_sub (desc : PB_Descriptor)
  : PB_Descriptor_OK desc ->
    forall fld, Vector.In fld (PB_DescriptorDesc desc) ->
           forall desc', (PB_FieldType fld = PB_Singular (PB_Embedded desc') \/
                     PB_FieldType fld = PB_Repeated (PB_Embedded desc')) ->
                    PB_Descriptor_OK desc'.
Proof.
  destruct desc as [n desc]. simpl.
  intros. induction H0.
  - destruct fld; destruct p; destruct p; intuition; try easy; injections; auto.
  - apply IHIn. destruct H as [? [? [? [? ?]]]].
    repeat split; auto.
    + inversion H. existT_eq_dec. congruence.
    + unfold PB_Descriptor_tags_nodup in *. eapply vec_nodup_cons. simpl in *. eauto.
    + unfold PB_Descriptor_names_nodup in *. eapply vec_nodup_cons. simpl in *. eauto.
Qed.

Lemma PB_denote_type_eq (desc : PB_Descriptor) (i : Fin.t (PB_DescriptorLen desc))
  : PB_Type_denote (PB_FieldType (Vector.nth (PB_DescriptorDesc desc) i))
    = Domain (PB_Descriptor_heading desc) i.
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Defined.

(* Sanity check for default function *)
Lemma PB_Descriptor_default_correct (desc : PB_Descriptor)
  : forall (i : Fin.t (PB_DescriptorLen desc)),
    type_cast (PB_denote_type_eq desc i)
              (PB_Type_default (PB_FieldType (Vector.nth (PB_DescriptorDesc desc) i)))
    = ith2 (PB_Descriptor_default' (PB_DescriptorDesc desc)) i.
Proof.
  destruct desc as [n desc]. simpl in *.
  induction desc; intros.
  - inversion i.
  - revert desc IHdesc. pattern n, i.
    apply Fin.caseS; intros; destruct h; simpl.
    + reflexivity.
    + apply IHdesc.
Qed.

(* A bounded tag is a tag which must be in the descriptor. *)
Definition BoundedTag (desc : PB_Descriptor) :=
  BoundedIndex (PB_Descriptor_tags desc).

Record UnboundedIndex {A} {n : nat} (Bound : Vector.t A n) :=
  { uindex : A;
    uboundi : ~ Vector.In uindex Bound
  }.

Global Arguments uindex {A n Bound} u.

(* An unbounded tag is a tag which must not be in the descriptor. *)
Definition UnboundedTag (desc : PB_Descriptor) :=
  UnboundedIndex (PB_Descriptor_tags desc).

(* Two bounded tags are equal if their tag numbers are equal. *)
Theorem BoundedTag_inj (desc : PB_Descriptor)
  : PB_Descriptor_OK desc ->
    forall t1 t2 : BoundedTag desc,
      bindex t1 = bindex t2 -> t1 = t2.
Proof.
  unfold PB_Descriptor_OK, PB_Descriptor_tags_nodup.
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

(* Two fields are equal if their tags are equal. *)
Theorem PB_Field_inj (desc : PB_Descriptor)
  : PB_Descriptor_OK desc ->
    forall fld1 fld2 : PB_Field,
      Vector.In fld1 (PB_DescriptorDesc desc) -> Vector.In fld2 (PB_DescriptorDesc desc) ->
      PB_FieldTag fld1 = PB_FieldTag fld2 ->
      fld1 = fld2.
Proof.
  unfold PB_Descriptor_OK, PB_Descriptor_tags_nodup.
  destruct desc as [n desc].
  intros [_ [? _]]; intros.
  destruct (vector_in_fin _ _ H0).
  destruct (vector_in_fin _ _ H1).
  subst.
  f_equal. apply H.
  rewrite !PB_Descriptor_tags_correct.
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

(* Some immediate lemmas for bounded and unbounded tags. *)
Lemma BoundedTag_in (desc : PB_Descriptor)
  : forall t1 : BoundedTag desc, Vector.In (bindex t1) (PB_Descriptor_tags desc).
Proof.
  intros. destruct t1. destruct indexb. simpl in *.
  subst. eapply vector_in; eauto.
Qed.

Lemma BoundedTag_not_unbounded (desc : PB_Descriptor)
  : forall (t1 : BoundedTag desc) (t2 : UnboundedTag desc), bindex t1 <> uindex t2.
Proof.
  intros. intro. pose proof (BoundedTag_in _ t1). destruct t2. simpl in *.
  subst. easy.
Qed.

(* A decision procedure to convert a tag number to bounded or unbounded tag. *)
Fixpoint PB_Descriptor_boundedTag' {n} (tags : Vector.t N n) (m : N)
  : {ibound : _ | Vector.nth tags ibound = m} + {~ Vector.In m tags}.
Proof.
  refine
    (match tags with
     | Vector.nil => inright _
     | Vector.cons t n' tags' =>
       if N.eq_dec t m then
         inleft (exist _ Fin.F1 _)
       else
         match PB_Descriptor_boundedTag' n' tags' m with
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

Definition PB_Descriptor_boundedTag (desc : PB_Descriptor) (m : N)
  : (BoundedTag desc) + (UnboundedTag desc) :=
  match PB_Descriptor_boundedTag' (PB_Descriptor_tags desc) m with
  | inleft (exist i pf) => inl {| bindex := m; indexb := {| ibound := i; boundi := pf |} |}
  | inright pf => inr {| uindex := m; uboundi := pf |}
  end.

(* Sanity check and useful lemmas for later proofs. *)
Lemma PB_Descriptor_boundedTag_correct (desc : PB_Descriptor) (m : N)
  : forall tag, PB_Descriptor_boundedTag desc m = inl tag -> bindex tag = m.
Proof.
  unfold PB_Descriptor_boundedTag.
  intros. destruct PB_Descriptor_boundedTag'; try easy.
  destruct s. inversion H. reflexivity.
Qed.

Lemma PB_Descriptor_boundedTag_correct' (desc : PB_Descriptor) (m : N)
  : forall tag, PB_Descriptor_boundedTag desc m = inr tag -> uindex tag = m.
Proof.
  unfold PB_Descriptor_boundedTag.
  intros. destruct PB_Descriptor_boundedTag'. destruct s.
  easy. inversion H. reflexivity.
Qed.

Lemma PB_Descriptor_boundedTag_inv (desc : PB_Descriptor)
  : PB_Descriptor_OK desc -> forall tag, PB_Descriptor_boundedTag desc (bindex tag) = inl tag.
Proof.
  intros. destruct (PB_Descriptor_boundedTag desc (bindex tag)) eqn:?.
  apply PB_Descriptor_boundedTag_correct in Heqs.
  apply BoundedTag_inj in Heqs; eauto. subst. auto.
  exfalso. apply PB_Descriptor_boundedTag_correct' in Heqs.
  destruct tag as [? [? ?]]. destruct u. simpl in *.
  subst. apply uboundi0. apply vector_in.
Qed.

Lemma PB_Descriptor_boundedTag_notr (desc : PB_Descriptor)
  : PB_Descriptor_OK desc -> forall (tag : BoundedTag desc) utag, PB_Descriptor_boundedTag desc (bindex tag) <> inr utag.
Proof.
  intros. intro. apply PB_Descriptor_boundedTag_correct' in H0.
  destruct desc. destruct tag as [? [? ?]]; destruct utag. simpl in *. subst.
  apply uboundi0. apply vector_in.
Qed.

Lemma PB_Descriptor_boundedTag_notl (desc : PB_Descriptor)
  : PB_Descriptor_OK desc -> forall (utag : UnboundedTag desc) tag, PB_Descriptor_boundedTag desc (uindex utag) <> inl tag.
Proof.
  intros. intro. apply PB_Descriptor_boundedTag_correct in H0.
  destruct desc. destruct tag as [? [? ?]]; destruct utag. simpl in *. subst.
  apply uboundi0. apply vector_in.
Qed.

(* Map a bounded tag to its index of the descriptor vector. *)
Definition PB_Descriptor_tagToIndex {desc : PB_Descriptor}
         (tag : BoundedTag desc) :=
  ibound (indexb tag).
Arguments PB_Descriptor_tagToIndex /.

Lemma PB_Descriptor_tagToIndex_correct (desc : PB_Descriptor)
        (tag : BoundedTag desc)
  : PB_FieldTag (Vector.nth (PB_DescriptorDesc desc) (PB_Descriptor_tagToIndex tag))
    = bindex tag.
Proof.
  destruct desc as [n desc].
  rewrite <- PB_Descriptor_tags_correct.
  destruct tag. destruct indexb.
  eauto.
Qed.

Lemma PB_Descriptor_tagToIndex_correct' (desc : PB_Descriptor)
        (tag : BoundedTag desc)
  : PB_Descriptor_OK desc ->
    forall fld, Vector.In fld (PB_DescriptorDesc desc) ->
           PB_FieldTag fld = bindex tag ->
           fld = Vector.nth (PB_DescriptorDesc desc) (PB_Descriptor_tagToIndex tag).
Proof.
  intros. destruct desc as [n desc].
  destruct tag. destruct indexb.
  destruct desc; intros; try easy.
  simpl in ibound.
  revert desc boundi H fld H0 H1. pattern n, ibound.
  apply Fin.caseS; intros.
  - subst. eapply PB_Field_inj; eauto. constructor.
  - eapply PB_Field_inj; eauto; clear H; simpl in *. constructor. apply vector_in.
    subst. rewrite <- (PB_Descriptor_tags_correct (Build_PB_Descriptor desc)). auto.
Qed.

(* Look up the type of the field by its tag. *)
Definition PB_Descriptor_tagToType {desc : PB_Descriptor}
           (tag : BoundedTag desc) :=
  PB_FieldType (Vector.nth (PB_DescriptorDesc desc) (PB_Descriptor_tagToIndex tag)).

Theorem PB_Descriptor_tagToType_correct (desc : PB_Descriptor)
        (tag : BoundedTag desc)
  : PB_Descriptor_OK desc ->
    forall fld, Vector.In fld (PB_DescriptorDesc desc) ->
           PB_FieldTag fld = bindex tag ->
           PB_FieldType fld = PB_Descriptor_tagToType tag.
Proof.
  intros.
  rewrite (PB_Descriptor_tagToIndex_correct' desc tag H fld); eauto.
Qed.

(* All embedded descriptors of a valid descripto are valid. *)
Lemma PB_Descriptor_OK_sub_tagToType (desc : PB_Descriptor)
  : PB_Descriptor_OK desc ->
    forall (tag : BoundedTag desc) desc',
      (PB_Descriptor_tagToType tag = PB_Singular (PB_Embedded desc') \/
       PB_Descriptor_tagToType tag = PB_Repeated (PB_Embedded desc')) ->
      PB_Descriptor_OK desc'.
Proof.
  intros. eapply PB_Descriptor_OK_sub in H; eauto.
  destruct desc as [n desc]. destruct tag as [? [? ?]]. simpl.
  apply vector_in.
Qed.

(* Mainly for type casting. *)
Definition PB_Descriptor_tagToDenoteType {desc : PB_Descriptor}
           (tag : BoundedTag desc) :=
  Domain (PB_Descriptor_heading desc) (PB_Descriptor_tagToIndex tag).

Theorem PB_Descriptor_tagToDenoteType_correct (desc : PB_Descriptor)
        (tag : BoundedTag desc)
  : PB_Type_denote (PB_Descriptor_tagToType tag)
    = PB_Descriptor_tagToDenoteType tag.
Proof.
  apply PB_denote_type_eq.
Defined.

Opaque PB_Descriptor_tagToDenoteType_correct.

(* Look up value of the field of the given message by its tag. *)
Definition PB_Message_lookup' {n} {desc : PB_Desc n}
           (msg : PB_Descriptor_denote (Build_PB_Descriptor desc))
           (tag : BoundedTag (Build_PB_Descriptor desc)) :=
  type_cast_r (PB_Descriptor_tagToDenoteType_correct (Build_PB_Descriptor desc) tag)
              (GetAttributeRaw msg (PB_Descriptor_tagToIndex tag)).

Definition PB_Message_lookup {desc : PB_Descriptor} :=
  match desc return PB_Descriptor_denote desc ->
                    forall tag : BoundedTag desc,
                      PB_Type_denote (PB_Descriptor_tagToType tag) with
  | Build_PB_Descriptor _ v =>
    fun msg tag => @PB_Message_lookup' _ v msg tag
  end.

(* Update value of the field of the given message by its tag. *)
Definition PB_Message_update' {n} {desc : PB_Desc n}
           (msg : PB_Descriptor_denote (Build_PB_Descriptor desc))
           (tag : BoundedTag (Build_PB_Descriptor desc))
           (value : PB_Type_denote (PB_Descriptor_tagToType tag))
  : PB_Descriptor_denote (Build_PB_Descriptor desc) :=
  SetAttributeRaw msg (PB_Descriptor_tagToIndex tag)
                  (type_cast
                     (PB_Descriptor_tagToDenoteType_correct
                        (Build_PB_Descriptor desc) tag)
                     value).

Definition PB_Message_update {desc : PB_Descriptor} :=
  match desc return PB_Descriptor_denote desc ->
                    forall tag : BoundedTag desc,
                      PB_Type_denote (PB_Descriptor_tagToType tag) ->
                      PB_Descriptor_denote desc with
  | Build_PB_Descriptor _ v =>
    fun msg tag value => PB_Message_update' msg tag value
  end.

(* This definition of IR Element is equivalent to the one in the paper. Notice
   that the denotation of a base type is just the denotation of its wire type
   and eventually we format the wire type to binary strings, so we directly use
   wire type here for both unknown fields and singular fields. We also factor
   out the wire type for simplicity. *)
Inductive PB_IRElm : Type :=
| Build_PB_IRElm : N ->
                   forall PB_IRType : PB_WireType,
                     PB_WireType_denote PB_IRType +
                     list (PB_WireType_denote PB_IRType) +
                     list PB_IRElm ->
                     PB_IRElm.

(* Induction principle for IR Element. *)
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

(* Helper functions for accessing element's fields. *)
Definition PB_IRTag (elm : PB_IRElm) :=
  let (t, _, _) := elm in t.

Definition PB_IRType (elm : PB_IRElm) :=
  let (_, ty, _) := elm in ty.

Definition PB_IRVal (elm : PB_IRElm) :=
  let (_, ty, v)
      return (PB_WireType_denote (PB_IRType elm) +
              list (PB_WireType_denote (PB_IRType elm)) +
              list PB_IRElm) := elm in v.

(* Well-formedness of IR Element. *)
Fixpoint PB_IRElm_OK (desc : PB_Descriptor) (elm : PB_IRElm) :=
  match elm with
  | Build_PB_IRElm t ty val =>
    match PB_Descriptor_boundedTag desc t with
    | inl tag =>
      match PB_Descriptor_tagToType tag with
      | PB_Singular (PB_Base pty) =>
        match val with
        | inl (inl _) => PB_BaseType_toWireType pty = ty
        | _ => False
        end
      | PB_Repeated (PB_Base pty) =>
        match val with
        | inl (inl _) => PB_BaseType_toWireType pty = ty
        | inl (inr _) => PB_BaseType_toWireType pty = ty /\ ty <> PB_LengthDelimited
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
      | inl (inl _) => PB_FieldTag_OK (uindex tag)
      | _ => False
      end
    end
  end.

(* Work around for a weired problem. *)
Lemma PB_IRElm_OK_equiv (desc : PB_Descriptor) (ir : list PB_IRElm)
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

(* Just a helper function to get the right wire type for encoding. *)
Definition PB_IRElm_toWireType (elm : PB_IRElm) :=
  match PB_IRVal elm with
  | inl (inl _) => PB_IRType elm
  | _ => PB_LengthDelimited
  end.

(* Format the value of an element. *)
Definition PB_IRVal_format
           (format : funType [PB_IRElm; CacheFormat] (ByteString * CacheFormat))
  : FormatM PB_IRElm ByteString :=
  fun elm =>
    match elm with
    | Build_PB_IRElm _ ty val =>
      match val with
      | inl (inl v) => PB_WireType_format ty v
      | inl (inr l) => PB_LengthDelimited_format (PB_WireType_format ty) l
      | inr ir => PB_LengthDelimited_format format (rev ir)
      end
    end.

Definition PB_IRElm_format_body
           (format : funType [PB_IRElm; CacheFormat] (ByteString * CacheFormat))
           (elm : PB_IRElm) :=
  Varint_format (N.lor
                   (N.shiftl (PB_IRTag elm) 3)
                   (PB_WireType_val (PB_IRElm_toWireType elm)))
  ThenC PB_IRVal_format format elm
  DoneC.

(* Format a single element. *)
Definition PB_IRElm_format
  : FormatM PB_IRElm ByteString :=
    LeastFixedPoint PB_IRElm_format_body.

Lemma PB_IRElm_format_body_monotone:
  monotonic_function PB_IRElm_format_body.
Proof.
  unfold monotonic_function. simpl. intros.
  unfold PB_IRElm_format_body.
  apply SetoidMorphisms.refine_bind. reflexivity.
  intros [? ?].
  apply SetoidMorphisms.refine_bind. 2 : reflexivity.
  unfold PB_IRVal_format.
  destruct t; repeat destruct s; try reflexivity.
  apply SetoidMorphisms.refine_bind. 2 : reflexivity.
  unfold PB_LengthDelimited_format.
  apply SetoidMorphisms.refine_bind. 2 : reflexivity.
  unfold SizedList_format, SizedList_format_body.
  unfold refine. intros. simpl snd in *.
  eapply (unroll_LeastFixedPoint' (SizedList_format_body_monotone _)).
  eapply (unroll_LeastFixedPoint (SizedList_format_body_monotone _)) in H0.
  revert v H0. revert c.
  induction (rev l). auto. intros ? ?.
  apply SetoidMorphisms.refine_bind. apply H.
  intros [? ?].
  apply SetoidMorphisms.refine_bind.
  unfold refine. destruct 0. intros.
  eapply (unroll_LeastFixedPoint' (SizedList_format_body_monotone _)).
  eapply (unroll_LeastFixedPoint (SizedList_format_body_monotone _)) in H0.
  auto. reflexivity.
Qed.

(* IR element can not formatted to empty string. *)
Theorem PB_IRElm_format_some
  : forall d b ce ce', PB_IRElm_format d ce ↝ (b, ce') -> lt 0 (bin_measure b).
Proof.
  unfold PB_IRElm_format. intros.
  eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H.
  unfold PB_IRElm_format_body in H.
  computes_to_inv2.
  apply Varint_format_some in H.
  rewrite !(@mappend_measure). omega.
Qed.

(* IR elements are always formatted into the same size. *)
Theorem PB_IRElm_format_sz_eq
  : forall x b1 b2 ce1 ce1' ce2 ce2',
    PB_IRElm_format x ce1 ↝ (b1, ce1') ->
    PB_IRElm_format x ce2 ↝ (b2, ce2') ->
    bin_measure b1 = bin_measure b2.
Proof.
  induction x using PB_IRElm_ind'; unfold PB_IRElm_format, PB_IRElm_format_body. {
    intros.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H0.
    unfold PB_IRElm_format_body in *.
    computes_to_inv2.
    rewrite !(@mappend_measure _ ByteStringQueueMonoid).
    f_equal. eapply Varint_format_sz_eq; eauto.
    f_equal. unfold PB_IRVal_format in *.
    destruct s. eapply PB_WireType_format_sz_eq; eauto.
    eapply PB_LengthDelimited_format_sz_eq; [eapply PB_WireType_format_sz_eq | |]; eauto.
  } {
    intros.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H0.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H1.
    unfold PB_IRElm_format_body in *.
    computes_to_inv2.
    rewrite !(@mappend_measure _ ByteStringQueueMonoid).
    f_equal. eapply Varint_format_sz_eq; eauto.
    f_equal. unfold PB_IRVal_format in *.
    rewrite Forall_forall in H.
    eapply PB_LengthDelimited_format_sz_eq'. intro. rewrite <- in_rev. all : eauto.
  }
Qed.

(* IR Elements' binary strings are byte-aligned. *)
Theorem PB_IRElm_format_byte
  : forall d b ce ce', PB_IRElm_format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
Proof.
  induction d using PB_IRElm_ind'; unfold PB_IRElm_format, PB_IRElm_format_body. {
    intros.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H.
    unfold PB_IRElm_format_body in H.
    computes_to_inv2.
    rewrite !(@mappend_measure _ ByteStringQueueMonoid).
    rewrite <- Nat.add_mod_idemp_l by auto.
    erewrite Varint_format_byte; eauto.
    rewrite Nat.add_0_l.
    rewrite <- Nat.add_mod_idemp_l by auto.
    rewrite @mempty_measure_0.
    rewrite Nat.add_0_r. rewrite Nat.mod_mod; eauto.
    unfold PB_IRVal_format in *.
    destruct s.
    eapply PB_WireType_format_byte; eauto.
    eapply PB_LengthDelimited_format_byte; [eapply PB_WireType_format_byte |]; eauto.
  } {
    intros.
    eapply (unroll_LeastFixedPoint PB_IRElm_format_body_monotone) in H0.
    unfold PB_IRElm_format_body in H0.
    computes_to_inv2.
    rewrite !(@mappend_measure _ ByteStringQueueMonoid).
    rewrite <- Nat.add_mod_idemp_l by auto.
    erewrite Varint_format_byte; eauto.
    rewrite Nat.add_0_l.
    rewrite <- Nat.add_mod_idemp_l by auto.
    rewrite @mempty_measure_0.
    rewrite Nat.add_0_r. rewrite Nat.mod_mod; eauto.
    unfold PB_IRVal_format in *.
    rewrite Forall_forall in H. 
    eapply PB_LengthDelimited_format_byte'. intro. rewrite <- in_rev. all : eauto.
  }
Qed.

Definition PB_IR := list PB_IRElm.

(* The measurement of IR is not the length of the list but includes the length
   of the sub-IR. *)
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

(* IR is a monoid. *)
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

(* The key inference rules for the relation msg' |- ir ~= msg *)
Inductive PB_IR_transit
  : forall {desc : PB_Descriptor}, PB_Descriptor_denote desc -> PB_IR -> PB_Descriptor_denote desc -> Prop :=
| PB_IR_nil desc :
    forall msg : PB_Descriptor_denote desc, PB_IR_transit msg nil msg
| PB_IR_singular desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_BaseType)
        (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Base pty))
        (v : PB_Type_denote (PB_Singular (PB_Base pty))),
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_BaseType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t (eq_rect_r _ v pf))
| PB_IR_repeated_cons desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_BaseType)
        (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Base pty))
        (v : PB_Type_denote (PB_Singular (PB_Base pty))),
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_BaseType_toWireType pty)
                                      (inl (inl v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [v])
                                           pf))
| PB_IR_repeated_app desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (pty : PB_BaseType)
        (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Base pty))
        (v : PB_Type_denote (PB_Repeated (PB_Base pty))),
        PB_BaseType_toWireType pty <> PB_LengthDelimited ->
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      (PB_BaseType_toWireType pty)
                                      (inl (inr v))) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ v)
                                           pf))
| PB_IR_unknown desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : UnboundedTag desc) (wty : PB_WireType)
        (v : PB_WireType_denote wty),
        PB_FieldTag_OK (uindex t) ->
        PB_IR_transit msg'
                     ((Build_PB_IRElm (uindex t)
                                      wty
                                      (inl (inl v))) :: ir)
                     msg
| PB_IR_embedded_none desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Descriptor)
        (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Embedded desc'))
        v (msg'' : PB_Descriptor_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = None ->
        PB_IR_transit (PB_Descriptor_default desc') v msg'' ->
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg'') pf))
| PB_IR_embedded_some desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Descriptor)
        (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Embedded desc'))
        v (msg'' msg''' : PB_Descriptor_denote desc'),
        eq_rect _ _ (PB_Message_lookup msg t) _ pf = Some msg'' ->
        PB_IR_transit msg'' v msg''' ->
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r _ (Some msg''') pf))
| PB_IR_repeated_embedded desc :
    forall (msg' : PB_Descriptor_denote desc) ir (msg : PB_Descriptor_denote desc),
      PB_IR_transit msg' ir msg ->
      forall (t : BoundedTag desc) (desc' : PB_Descriptor)
        (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Embedded desc'))
        v (msg'' : PB_Descriptor_denote desc'),
        PB_IR_transit (PB_Descriptor_default desc') v msg'' ->
        PB_IR_transit msg'
                     ((Build_PB_IRElm (bindex t)
                                      PB_LengthDelimited
                                      (inr v)) :: ir)
                     (PB_Message_update msg t
                                        (eq_rect_r
                                           _
                                           ((eq_rect _ _ (PB_Message_lookup msg t) _ pf) ++ [msg''])
                                           pf))
.

Ltac PB_IR_transit_inv_step :=
  match goal with
  | H : bindex ?a = bindex _ |- _ => apply BoundedTag_inj in H; [subst a | solve [eauto]]
  | H : uindex _ = bindex _ |- _ => symmetry in H
  | H : bindex _ = uindex _ |- _ => apply BoundedTag_not_unbounded in H; inversion H
  | H : PB_Descriptor_tagToType ?t = ?c1 (?c2 ?a),
        H' : PB_Descriptor_tagToType ?t = ?c1 (?c2 ?b) |- _ => progress replace b with a in * by congruence
  | H : existT _ _ _ = existT _ _ _ |- _  =>
    apply inj_pair2_eq_dec in H;
    [| clear H; try apply PB_Descriptor_eq_dec || apply PB_WireType_eq_dec];
    subst
  | H : ?a = Some _, H' : ?b = None |- _ => progress replace a with b in *; [congruence | clear H H']
  | H : ?a = Some _, H' : ?b = Some _ |- _ => progress replace a with b in *; [substss; injections | clear H H']
  | |- ?a = ?b => progress f_equal; eauto; try apply (UIP_dec PB_Type_eq_dec)
  | _ => eauto using eq_sym, PB_Descriptor_OK_sub_tagToType; easy || congruence
  end.

Ltac PB_IR_transit_inv hyp :=
  inversion hyp; repeat PB_IR_transit_inv_step.

(* Some properties for the relation. *)
Theorem PB_IR_transit_deterministic
  : forall desc,
    PB_Descriptor_OK desc ->
    forall (msg' msg1 msg2 : PB_Descriptor_denote desc) ir,
      PB_IR_transit msg' ir msg1 ->
      PB_IR_transit msg' ir msg2 ->
      msg1 = msg2.
Proof.
  intros. induction H0; PB_IR_transit_inv H1.
Qed.

Ltac PB_IR_transit_inv_step_ext :=
  match goal with
  | |- PB_IR_transit ?a nil ?b => replace a with b; [constructor |]
  | _ => eauto using eq_sym, PB_Descriptor_OK_sub_tagToType, PB_IR_transit_deterministic
  end.

Ltac PB_IR_transit_inv hyp ::=
  inversion hyp; repeat first [PB_IR_transit_inv_step | PB_IR_transit_inv_step_ext].

Theorem PB_IR_transit_trans
  : forall desc,
    PB_Descriptor_OK desc ->
    forall (msg1 msg2 msg3 : PB_Descriptor_denote desc) (ir1 ir2 ir3 : PB_IR),
    PB_IR_transit msg1 ir1 msg2 ->
    (PB_IR_transit msg2 ir2 msg3 <-> PB_IR_transit msg1 (ir2 ++ ir1) msg3).
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
       | H : PB_IR_transit _ _ ?a |- PB_IR_transit ?a _ _ => solve [PB_IR_transit_inv H]
       end |
       match goal with
       | H : _ = Some _ |- _ => eapply PB_IR_embedded_some; eauto
       | _ => try easy; constructor; eauto
       end].
  }
Qed.

(* We define the format directly from this relation. This is the stronger
   version. *)
Definition PB_Message_IR_format_ref' (desc : PB_Descriptor) msg'
  : FormatM (PB_Descriptor_denote desc) PB_IR :=
  fun msg _ => {b | PB_IR_transit msg' (fst b) msg}.
Arguments PB_Message_IR_format_ref' /.

(* This is the format we want, which is just a special case of the stronger
   version. *)
Definition PB_Message_IR_format_ref (desc : PB_Descriptor)
  : FormatM (PB_Descriptor_denote desc) PB_IR :=
  PB_Message_IR_format_ref' desc (PB_Descriptor_default desc).

(* Here is an alternative definition of the previous relation. They are
   equivalent as we show below. This is a byproduct of our another experiment
   but we end up proving the correctness theorem using this definition. *)
Definition PB_Message_IR_format_body
           (format : funType_dep [PB_Descriptor_denote; PB_Descriptor_denote; fun _ => CacheFormat]
                                 (PB_IR * CacheFormat))
  : funType_dep [PB_Descriptor_denote; PB_Descriptor_denote; fun _ => CacheFormat]
                (PB_IR * CacheFormat) :=
  fun desc msg' msg _ b =>
    let (ir, _) := b in
    (* nil *)
    (msg' = msg /\ ir = nil) \/
    (* singular *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Singular (PB_Base pty)))
       (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Base pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_BaseType_toWireType pty)
                             (inl (inl v))) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ v pf)) \/
    (* repeated_cons *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Singular (PB_Base pty)))
       (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Base pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_BaseType_toWireType pty)
                             (inl (inl v))) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r
                                   _
                                   ((eq_rect _ _ (PB_Message_lookup msg1 t) _ pf) ++ [v])
                                   pf)) \/
    (* repeated_app *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Repeated (PB_Base pty)))
       (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Base pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        PB_BaseType_toWireType pty <> PB_LengthDelimited /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_BaseType_toWireType pty)
                             (inl (inr v))) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r
                                   _
                                   ((eq_rect _ _ (PB_Message_lookup msg1 t) _ pf) ++ v)
                                   pf)) \/
    (* unknown *)
    (exists ir1 (t : UnboundedTag desc) wty (v : PB_WireType_denote wty) ce1 ce2,
        format _ msg' msg ce1 (ir1, ce2) /\
        PB_FieldTag_OK (uindex t) /\
        ir = (Build_PB_IRElm (uindex t)
                             wty
                             (inl (inl v))) :: ir1) \/
    (* embedded_none *)
    (exists ir1 msg1 t desc' v (msg2 : PB_Descriptor_denote desc')
       (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        eq_rect _ _ (PB_Message_lookup msg1 t) _ pf = None /\
        format _ (PB_Descriptor_default desc') msg2 ce3 (v, ce4) /\
        ir = (Build_PB_IRElm (bindex t)
                             PB_LengthDelimited
                             (inr v)) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ (Some msg2) pf)) \/
    (* embedded_some *)
    (exists ir1 msg1 t desc' v (msg2 msg3 : PB_Descriptor_denote desc')
       (pf : PB_Descriptor_tagToType t = PB_Singular (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        eq_rect _ _ (PB_Message_lookup msg1 t) _ pf = Some msg2 /\
        format _ msg2 msg3 ce3 (v, ce4) /\
        ir = (Build_PB_IRElm (bindex t)
                             PB_LengthDelimited
                             (inr v)) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ (Some msg3) pf)) \/
    (* repeated_embedded *)
    (exists ir1 msg1 t desc' v (msg2 : PB_Descriptor_denote desc')
       (pf : PB_Descriptor_tagToType t = PB_Repeated (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        format _ (PB_Descriptor_default desc') msg2 ce3 (v, ce4) /\
        ir = (Build_PB_IRElm (bindex t)
                             PB_LengthDelimited
                             (inr v)) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r
                                   _
                                   ((eq_rect _ _ (PB_Message_lookup msg1 t) _ pf) ++ [msg2])
                                   pf))
.

Local Transparent computes_to.
Local Transparent Pick.
Lemma PB_Message_IR_format_body_monotone
  : monotonic_function PB_Message_IR_format_body.
Proof.
  unfold monotonic_function. simpl. intros.
  unfold PB_Message_IR_format_body.
  intros [ir desc msg' msg ce]. intros [? ?]. unfold computes_to. intros.
  destruct_many;
    let solv n := solve [choose_br n; repeat eexists; eauto; apply H; eauto] in
    let rec trial n := match n with
                       | O => try solv 0
                       | S ?n' => try solv n; trial n'
                       end in
    trial 7.
Qed.

(* We define the format as a least fixed point. *)
Definition PB_Message_IR_format' := LeastFixedPoint_dep PB_Message_IR_format_body.

Definition PB_Message_IR_format (desc : PB_Descriptor)
  : FormatM (PB_Descriptor_denote desc) PB_IR :=
  fun msg =>
    PB_Message_IR_format' _ (PB_Descriptor_default desc) msg.

(* These two definitions of format are indeed equivalent. *)
Theorem PB_Message_IR_format_eq' (desc : PB_Descriptor)
  : forall msg' msg ce,
    refineEquiv (PB_Message_IR_format_ref' desc msg' msg ce)
                (PB_Message_IR_format' desc msg' msg ce).
Proof.
  unfold refineEquiv, refine.
  unfold PB_Message_IR_format_ref', PB_Message_IR_format'. unfold Pick.
  unfold computes_to. simpl.
  intros. split; intros [ir ce'] H; simpl in *. {
    generalize dependent desc.
    generalize dependent ce.
    generalize dependent ce'.
    induction ir as [ir IH] using (well_founded_ind well_founded_lt_b); intros;
      apply (unroll_LeastFixedPoint_dep PB_Message_IR_format_body_monotone) in H.
    unfold computes_to in H. simpl in H.
    destruct_many;
      try (subst; constructor; eauto; eapply IH; eauto; apply PB_IR_measure_cons_lt || apply PB_IR_measure_embedded_lt).
    subst. eapply PB_IR_embedded_some; eauto.
    eapply IH; eauto; apply PB_IR_measure_cons_lt || apply PB_IR_measure_embedded_lt.
    eapply IH; eauto; apply PB_IR_measure_cons_lt || apply PB_IR_measure_embedded_lt.
  } {
    induction H; intros; apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone);
      let rec trial n := match n with
                         | O => try solve [choose_br 0; auto]
                         | S ?n' => try solve [choose_br n; repeat eexists; eauto]; trial n'
                         end in
      trial 7.
  }
Qed.

Theorem PB_Message_IR_format_eq (desc : PB_Descriptor)
  : forall msg ce,
    refineEquiv (PB_Message_IR_format_ref desc msg ce)
                (PB_Message_IR_format desc msg ce).
Proof.
  apply PB_Message_IR_format_eq'.
Qed.

(* The format only produces well-formed IR. *)
Lemma PB_Message_IR_format_Elm_OK (desc : PB_Descriptor)
      (HP : PB_Descriptor_OK desc)
      (msg : PB_Descriptor_denote desc) (ir : PB_IR)
      (ce ce' : CacheFormat)
  : PB_Message_IR_format desc msg ce ↝ (ir, ce') ->
    forall elm : PB_IRElm, In elm ir -> PB_IRElm_OK desc elm.
Proof.
  intro H. apply (proj1 (PB_Message_IR_format_eq _ _ _)) in H. revert H.
  unfold PB_Message_IR_format_ref. simpl. unfold computes_to, Pick. simpl.
  induction 1; intros; try easy;
    match goal with
    | H : In _ _ |- _ => destruct H
    end; auto; subst;
      unfold PB_IRElm_OK;
      destruct PB_Descriptor_boundedTag eqn:Hb; auto;
        repeat match goal with
            | H : PB_Descriptor_boundedTag _ (uindex _) = inl _ |- _ =>
              exfalso; eapply PB_Descriptor_boundedTag_notl; eauto
            | H : PB_Descriptor_boundedTag _ (bindex _) = inr _ |- _ =>
              exfalso; eapply PB_Descriptor_boundedTag_notr; eauto
            end;
        try (apply PB_Descriptor_boundedTag_correct in Hb;
             apply BoundedTag_inj in Hb; auto; subst;
             rewrite pf; intuition;
             apply PB_IRElm_OK_equiv in IHPB_IR_transit2; eauto using PB_Descriptor_OK_sub_tagToType).
  apply PB_Descriptor_boundedTag_correct' in Hb.
  destruct u, t.
  simpl in Hb. subst. auto.
Qed.

(* The end-to-end format is just a composition of the formats of layers. *)
Definition PB_Message_format (desc : PB_Descriptor)
  : FormatM (PB_Descriptor_denote desc) ByteString :=
  (fun msg ce =>
     `(ir, _) <- PB_Message_IR_format desc msg ce; SizedList_format PB_IRElm_format (rev ir) ce)%comp.
