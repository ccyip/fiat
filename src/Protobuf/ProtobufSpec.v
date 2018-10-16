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

Local Arguments natToWord : simpl never.
Local Arguments NToWord : simpl never.
Local Arguments wordToN : simpl never.
Local Arguments pow2 : simpl never.
Local Arguments weqb : simpl never.
Arguments split1 : simpl never.
Arguments split2 : simpl never.
Arguments combine : simpl never.
Arguments format_wordLE : simpl never.
Arguments decode_wordLE : simpl never.
Local Arguments N.shiftl : simpl never.
Local Arguments N.shiftr : simpl never.
Local Arguments N.lor : simpl never.
Local Arguments N.land : simpl never.
Local Arguments CacheDecode : simpl never.

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
  | PB_32bit => format_wordLE
  | PB_64bit => format_wordLE
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
  apply decode_wordLE_correct; repeat decode_step idtac.
  apply decode_wordLE_correct; repeat decode_step idtac.
  eapply shrink_format_correct_True; eauto.
  apply PB_LengthDelimited_decode_correct; repeat decode_step idtac.
  apply word_format_sz_eq. intros. eapply word_format_byte; eauto; eauto.
  intros. apply format_word_some in H; omega.
  intuition. intros. apply SizedList_predicate_rest_True.
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
  eapply format_wordLE_sz_eq; eauto.
  eapply format_wordLE_sz_eq; eauto.
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
  eapply format_wordLE_byte; eauto; eauto.
  eapply format_wordLE_byte; eauto; eauto.
  eapply PB_LengthDelimited_format_byte; eauto.
  intros. eapply word_format_byte; eauto; eauto.
Qed.

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

Theorem PB_WireType_decode_lt (wty : PB_WireType)
  : forall (b : ByteString) (cd : CacheDecode) (d : PB_WireType_denote wty)
      (b' : ByteString) (cd' : CacheDecode),
    PB_WireType_decode wty b cd = Some (d, b', cd') -> lt_B b' b.
Proof.
  intros. destruct wty; simpl in *.
  eapply Varint_decode_lt; eauto.
  eapply decode_wordLE_lt; eauto.
  eapply decode_wordLE_lt; eauto.
  eapply PB_LengthDelimited_decode_lt; eauto.
  eapply decode_word_lt; eauto.
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

(* TODO: This should probably be synthesized automatically. *)
Definition PB_FieldTag_OK_dec (t : N) :=
  (((N.leb 1 t) && (N.leb t 18999)) || ((N.leb 20000 t) && (N.leb t 536870911)))%bool.

(* Should use reflect here. *)
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

(* Need abstraction. *)
Definition PB_FieldTag_OK_false_iff (t : N)
  : PB_FieldTag_OK_dec t = false <-> ~ (PB_FieldTag_OK t).
Proof.
  split; intros. intro. apply PB_FieldTag_OK_true_iff in H0. congruence.
  destruct PB_FieldTag_OK_dec eqn:?; auto.
  apply PB_FieldTag_OK_true_iff in Heqb. congruence.
Qed.

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
Defined.

Opaque PB_Message_tagToDenoteType_correct.

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
      | inl (inl _) => PB_FieldTag_OK (uindex tag)
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

Local Opaque PB_LengthDelimited_decode.
Local Opaque Varint_decode.
Section PB_IRElm_body.

  Variable format : funType [PB_IRElm; CacheFormat] (ByteString * CacheFormat).
  Variable decode : PB_Message -> DecodeM PB_IRElm ByteString.
  Variable format_some : forall d b ce ce', format d ce ↝ (b, ce') -> lt 0 (bin_measure b).
  Variable format_sz_eq : forall x b1 b2 ce1 ce1' ce2 ce2', format x ce1 ↝ (b1, ce1') ->
                                                       format x ce2 ↝ (b2, ce2') ->
                                                       bin_measure b1 = bin_measure b2.
  Variable format_byte : forall d b ce ce', format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
  Variable P : CacheDecode -> Prop.
  Variable P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)).
  Variable n : nat.
  Variable decode_correct : forall b,
      lt (bin_measure b) n ->
      forall desc', CorrectDecoder' _ (PB_IRElm_OK desc') (fun _ _ => True) format (decode desc') P b.

  Definition PB_IRVal_format 
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
                   `(l, b', cd') <- PB_LengthDelimited_decode (PB_WireType_decode wty) b cd;
                     Some (Build_PB_IRElm t wty (inl (inr l)), b', cd')
                 else None
          | PB_Singular (PB_Embedded desc')
          | PB_Repeated (PB_Embedded desc') =>
            if PB_WireType_eq_dec PB_LengthDelimited wty then
              `(ir, b', cd') <- PB_LengthDelimited_decode (decode desc') b cd;
                Some (Build_PB_IRElm t PB_LengthDelimited (inr (rev ir)), b', cd')
            else None
          end
        | inr tag =>
          if PB_FieldTag_OK_dec (uindex tag) then
            `(v, b', cd') <- PB_WireType_decode wty b cd;
              Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
          else None
        end
      | inright _ => None
      end.

  Local Opaque PB_LengthDelimited_decode.
  Local Opaque Varint_decode.
  Theorem PB_IRVal_decode_correct
          (desc : PB_Message)
    : forall (t : N) (w : N) b,
      lt (bin_measure b) (S n) ->
      CorrectDecoder' _
                     (fun elm => PB_IRTag elm = t /\
                              PB_WireType_val (PB_IRElm_toWireType elm) = w /\
                              PB_IRElm_OK desc elm)
                     (fun _ _ => True)
                     PB_IRVal_format (PB_IRVal_decode desc t w) P b.
  Proof.
    unfold PB_IRElm_OK, PB_IRVal_format, PB_IRVal_decode, PB_IRElm_toWireType. simpl.
    destruct desc as [n' desc].
    intros ? ? ? pf. split; intros.
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
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm)) as [[? [? [? ?]]] _]; eauto.
          intros. eapply decode_correct. auto.
          instantiate (1 := p0).
          intro. rewrite <- in_rev.
          apply PB_IRElm_OK_equiv. apply H3.
          eapply SizedList_predicate_rest_True.
          rewrite H0. simpl. rewrite rev_involutive. eauto.
        - destruct val; try easy. injections.
          destruct PB_WireType_eq_dec.
          + destruct s; intuition; subst; [| easy].
            edestruct PB_WireType_decode_correct as [[? [? [? ?]]] _]; eauto.
            rewrite H0. simpl. eauto.
          + destruct s; try easy. destruct PB_WireType_eq_dec; try easy. intuition. subst.
            edestruct (PB_LengthDelimited_decode_correct (A:=(PB_WireType_denote (PB_PrimitiveType_toWireType p0))))
              as [[? [? [? ?]]] _];
              eauto using PB_WireType_format_sz_eq, PB_WireType_format_byte,
              PB_WireType_format_some, PB_WireType_decode_correct.
            intuition. eapply SizedList_predicate_rest_True.
            rewrite H0. simpl. eauto.
        - destruct val; [easy |]. injections. intuition.
          destruct PB_WireType_eq_dec; [| easy]. subst.
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm))
            as [[? [? [? ?]]] _]; eauto. intros. apply decode_correct. auto.
          instantiate (1 := p0). intro. rewrite <- in_rev. apply PB_IRElm_OK_equiv. apply H3.
          eapply SizedList_predicate_rest_True.
          rewrite H0. simpl. rewrite rev_involutive. eauto.
      } {
        destruct val; [destruct s |]; try easy. injections.
        edestruct PB_WireType_decode_correct as [[? [? [? ?]]] _]; eauto.
        simpl in *. rewrite H0. simpl.
        destruct PB_FieldTag_OK_dec eqn:?.
        eauto.
        apply PB_FieldTag_OK_false_iff in Heqb0.
        easy.
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
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intros. apply decode_correct. auto.
          intuition. eexists _, _. intuition; eauto. rewrite rev_involutive. eauto. rewrite Heqs0.
          destruct PB_Message_tagToType; destruct p; injections; try easy.
          intuition. apply (PB_IRElm_OK_equiv p0). intro. rewrite <- in_rev. eauto.
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
            as [_ [? [? [? [? [? [? ?]]]]]]];
            eauto using PB_WireType_format_sz_eq, PB_WireType_format_byte,
            PB_WireType_format_some, PB_WireType_decode_correct.
          intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
          destruct PB_Message_tagToType; destruct p; injections; easy.
        - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intros. apply decode_correct. auto.
          intuition. eexists _, _. intuition; eauto. rewrite rev_involutive; eauto. rewrite Heqs0.
          destruct PB_Message_tagToType; destruct p; injections; try easy.
          intuition. apply (PB_IRElm_OK_equiv p0). intro. rewrite <- in_rev. eauto.
      } {
        destruct PB_FieldTag_OK_dec eqn:?.
        decode_opt_to_inv.
        subst.
        existT_eq_dec; try apply PB_WireType_eq_dec.
        subst. simpl.
        edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
        apply PB_FieldTag_OK_true_iff in Heqb0. auto.
        easy.
      }
  Qed.

  Definition PB_IRElm_format_body (elm : PB_IRElm) :=
    Varint_format (N.lor
                     (N.shiftl (PB_IRTag elm) 3)
                     (PB_WireType_val (PB_IRElm_toWireType elm)))
    ThenC PB_IRVal_format elm
    DoneC.

  (* :TODO: automate this! *)
  Definition PB_IRElm_decode_body (desc : PB_Message) :=
    fun (b0 : ByteString) (cd : CacheDecode) =>
      `(a, b1, d) <- Varint_decode b0 cd;
        `(a0, b2, d0) <- PB_IRVal_decode desc (N.shiftr a 3) (N.land a 7) b1 d;
        (if (N.lor (N.shiftl (PB_IRTag a0) 3) (PB_WireType_val (PB_IRElm_toWireType a0)) =? a)%N
         then Some (a0, b2, d0)
         else None).

  Definition PB_IRElm_decode_body_correct (desc : PB_Message)
    : forall b,
      lt (bin_measure b) (S n) ->
      CorrectDecoder' _ (PB_IRElm_OK desc) (fun _ _ => True) PB_IRElm_format_body (PB_IRElm_decode_body desc) P b.
  Proof.
    unfold PB_IRElm_format_body, PB_IRElm_decode_body.
    split; intros. {
      computes_to_inv2.
      pose proof H3.
      eapply Varint_decode_correct in H3; eauto. destruct_many.
      rewrite <- (@mappend_assoc _ ByteStringQueueMonoid). rewrite H3.
      simpl. eapply PB_IRVal_decode_correct in H3'; eauto. destruct_many.
      match goal with
      | H : PB_IRVal_decode _ ?t' ?w' _ _ = _ |- context [PB_IRVal_decode _ ?t ?w] =>
        replace t with t'; [replace w with w' | ]
      end.
      rewrite H7. simpl. rewrite N.eqb_refl. eauto.
      apply N_land_lor_shiftl. apply PB_WireType_val_3bits.
      apply N_shiftr_lor_shiftl. apply PB_WireType_val_3bits.
      apply Varint_format_some in H4.
      rewrite !(@mappend_measure _ ByteStringQueueMonoid) in H. omega.
    } {
      decode_opt_to_inv.
      match goal with
      | H : context [if (?a =? ?b)%N then _ else _] |- _ =>
        destruct (N.eqb_spec a b)
      end. 2 : easy.
      injections.
      eapply Varint_decode_correct in H2; eauto. destruct_many.
      eapply PB_IRVal_decode_correct in H3; eauto. destruct_many.
      intuition. eexists _, _. intuition eauto.
      repeat computes_to_econstructor; eauto.
      simpl. subst. rewrite <- (@mappend_assoc _ ByteStringQueueMonoid).
      rewrite (@mempty_right _ ByteStringQueueMonoid). reflexivity.
      subst. apply Varint_format_some in H4. rewrite mappend_measure in H. omega.
    }
  Qed.

  (* Definition PB_IRElm_body_decoder (desc : PB_Message) *)
  (*   : CorrectDecoderFor (PB_IRElm_OK desc) PB_IRElm_format_body. *)
  (* Proof. *)
  (*   unfold PB_IRElm_OK, PB_IRElm_format_body. *)
  (*   eapply Start_CorrectDecoderFor; simpl. *)
  (*   - decode_step idtac. *)
  (*     apply Varint_decode_correct. *)
  (*     decode_step idtac. *)
  (*     decode_step idtac. *)
  (*     decode_step idtac. *)
  (*     intros. eapply (PB_IRVal_decode_correct desc) *)
  (*               with (t := N.shiftr proj 3) *)
  (*                    (w := N.land proj 7). *)
  (*     intros ? [? ?]. repeat split; eauto; subst. *)
  (*     apply N_shiftr_lor_shiftl. apply PB_WireType_val_3bits. *)
  (*     apply N_land_lor_shiftl. apply PB_WireType_val_3bits. *)
  (*     decode_step idtac. *)
  (*     decode_step idtac. *)
  (*   - cbv beta; synthesize_cache_invariant. *)
  (*   - cbv beta; optimize_decoder_impl. *)
  (* Defined. *)

  (* Definition PB_IRElm_decode_body (desc : PB_Message) := *)
  (*   Eval simpl in fst (proj1_sig (PB_IRElm_body_decoder desc)). *)

  (* Definition PB_IRElm_decode_body_correct (desc : PB_Message) *)
  (*   : CorrectDecoder' _ *)
  (*                    (PB_IRElm_OK desc) *)
  (*                    (fun _ _ => True) *)
  (*                    PB_IRElm_format_body (PB_IRElm_decode_body desc) P b. *)
  (* Proof. *)
  (*   destruct (proj2_sig (PB_IRElm_body_decoder desc)) as [? [? ?]]. *)
  (*   apply H. simpl in *. auto. *)
  (* Qed. *)

End PB_IRElm_body.

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

Definition PB_IRElm_format
  : FormatM PB_IRElm ByteString :=
    LeastFixedPoint PB_IRElm_format_body.

Definition PB_IRElm_decode (desc : PB_Message)
  : DecodeM PB_IRElm ByteString :=
  FueledFixP PB_IRElm_decode_body desc.

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

(* :TODO: generalize this and put it to SizedList module. *)
Lemma SizedList_decode_continous_pres
      {A B C} {monoid : Monoid B}
      (decode_body : (C -> B -> CacheDecode -> option (A * B * CacheDecode)) ->
                     C -> B -> CacheDecode -> option (A * B * CacheDecode))
  : forall decode : C -> B -> CacheDecode -> option (A * B * CacheDecode),
    (forall c b cd a b' cd',
        decode c b cd = Some (a, b', cd') -> decode_body decode c b cd = Some (a, b', cd')) ->
    forall sz c b cd a b' cd',
      SizedList_decode (decode c) sz b cd = Some (a, b', cd') ->
      SizedList_decode (decode_body decode c) sz b cd = Some (a, b', cd').
Proof.
  unfold SizedList_decode, SizedList_decode_body, FueledFixP in *.
  intros ? ? ? ? ?. revert sz c. generalize (bin_measure b). intro. revert b.
  induction n; simpl; intros. destruct sz; auto. decode_opt_to_inv.
  apply H in H0. rewrite H0. simpl. auto.
  destruct sz. auto.
  decode_opt_to_inv. apply H in H0. rewrite H0. simpl.
  destruct lt_dec. auto.
  decode_opt_to_inv. apply IHn in H1. subst. simpl in *. rewrite H1.
  simpl. auto.
Qed.

Local Transparent PB_LengthDelimited_decode.
Lemma PB_LengthDelimited_decode_continous_pres
      {A B C} {monoid : Monoid B} {monoidUnit : QueueMonoidOpt monoid bool}
      (decode_body : (C -> B -> CacheDecode -> option (A * B * CacheDecode)) ->
                     C -> B -> CacheDecode -> option (A * B * CacheDecode))
  : forall decode : C -> B -> CacheDecode -> option (A * B * CacheDecode),
    (forall c b cd a b' cd',
        decode c b cd = Some (a, b', cd') -> decode_body decode c b cd = Some (a, b', cd')) ->
    forall c b cd a b' cd',
      PB_LengthDelimited_decode (decode c) b cd = Some (a, b', cd') ->
      PB_LengthDelimited_decode (decode_body decode c) b cd = Some (a, b', cd').
Proof.
  unfold PB_LengthDelimited_decode. intros.
  decode_opt_to_inv. rewrite H0. simpl. subst.
  apply SizedList_decode_continous_pres; eauto.
Qed.

Local Opaque PB_LengthDelimited_decode.
Definition PB_IRElm_decode_correct (desc : PB_Message)
           {P : CacheDecode -> Prop}
           (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (PB_IRElm_OK desc)
                   (fun _ _ => True)
                   PB_IRElm_format (PB_IRElm_decode desc) P.
Proof.
  unfold PB_IRElm_format, PB_IRElm_decode.
  eapply fix_format_correctP; eauto. apply PB_IRElm_format_body_monotone.
  intros _. intros.
  eapply PB_IRElm_decode_body_correct;
    eauto using PB_IRElm_format_some, PB_IRElm_format_byte, PB_IRElm_format_sz_eq.

  intros.
  unfold PB_IRElm_decode_body at 1.
  decode_opt_to_inv. rewrite H0. simpl.
  unfold PB_IRVal_decode.
  unfold PB_IRVal_decode in *.
  destruct PB_WireType_val_inv; [| easy].
  destruct PB_Message_boundedTag. {
    destruct PB_Message_tagToType; destruct p0.
    - rewrite H1. simpl. auto.
    - destruct PB_WireType_eq_dec; [| easy].
      decode_opt_to_inv. eapply PB_LengthDelimited_decode_continous_pres in H1; eauto.
      rewrite H1. simpl. subst. auto.
    - rewrite H1. auto.
    - destruct PB_WireType_eq_dec; [| easy].
      decode_opt_to_inv. eapply PB_LengthDelimited_decode_continous_pres in H1; eauto.
      rewrite H1. simpl. subst. auto.
  } {
    rewrite H1. simpl. auto.
  }
Qed.
Local Transparent Varint_decode.
Local Transparent PB_LengthDelimited_decode.

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
        PB_FieldTag_OK (uindex t) ->
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

Definition PB_Message_IR_format_body
           (format : funType_dep [PB_Message_denote; PB_Message_denote; fun _ => CacheFormat]
                                 (PB_IR * CacheFormat))
  : funType_dep [PB_Message_denote; PB_Message_denote; fun _ => CacheFormat]
                (PB_IR * CacheFormat) :=
  fun desc msg' msg _ b =>
    let (ir, _) := b in
    (* nil *)
    (msg' = msg /\ ir = nil) \/
    (* singular *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Singular (PB_Primitive pty)))
       (pf : PB_Message_tagToType t = PB_Singular (PB_Primitive pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_PrimitiveType_toWireType pty)
                             (inl (inl v))) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ v pf)) \/
    (* repeated_cons *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Singular (PB_Primitive pty)))
       (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_PrimitiveType_toWireType pty)
                             (inl (inl v))) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r
                                   _
                                   ((eq_rect _ _ (PB_Message_lookup msg1 t) _ pf) ++ [v])
                                   pf)) \/
    (* repeated_app *)
    (exists ir1 msg1 t pty
       (v : PB_Type_denote (PB_Repeated (PB_Primitive pty)))
       (pf : PB_Message_tagToType t = PB_Repeated (PB_Primitive pty)) ce1 ce2,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        PB_PrimitiveType_toWireType pty <> PB_LengthDelimited /\
        ir = (Build_PB_IRElm (bindex t)
                             (PB_PrimitiveType_toWireType pty)
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
    (exists ir1 msg1 t desc' v (msg2 : PB_Message_denote desc')
       (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        eq_rect _ _ (PB_Message_lookup msg1 t) _ pf = None /\
        format _ (PB_Message_default desc') msg2 ce3 (v, ce4) /\
        ir = (Build_PB_IRElm (bindex t)
                             PB_LengthDelimited
                             (inr v)) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ (Some msg2) pf)) \/
    (* embedded_some *)
    (exists ir1 msg1 t desc' v (msg2 msg3 : PB_Message_denote desc')
       (pf : PB_Message_tagToType t = PB_Singular (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        eq_rect _ _ (PB_Message_lookup msg1 t) _ pf = Some msg2 /\
        format _ msg2 msg3 ce3 (v, ce4) /\
        ir = (Build_PB_IRElm (bindex t)
                             PB_LengthDelimited
                             (inr v)) :: ir1 /\
        msg = PB_Message_update msg1 t
                                (eq_rect_r _ (Some msg3) pf)) \/
    (* repeated_embedded *)
    (exists ir1 msg1 t desc' v (msg2 : PB_Message_denote desc')
       (pf : PB_Message_tagToType t = PB_Repeated (PB_Embedded desc')) ce1 ce2 ce3 ce4,
        format _ msg' msg1 ce1 (ir1, ce2) /\
        format _ (PB_Message_default desc') msg2 ce3 (v, ce4) /\
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

Definition PB_Message_IR_format_ref' (desc : PB_Message) msg'
  : FormatM (PB_Message_denote desc) PB_IR :=
  fun msg _ => {b | PB_IR_refine msg' (fst b) msg}.
Arguments PB_Message_IR_format_ref' /.

Definition PB_Message_IR_format_ref (desc : PB_Message)
  : FormatM (PB_Message_denote desc) PB_IR :=
  PB_Message_IR_format_ref' desc (PB_Message_default desc).

Definition PB_Message_IR_format' := LeastFixedPoint_dep PB_Message_IR_format_body.

Definition PB_Message_IR_format (desc : PB_Message)
  : FormatM (PB_Message_denote desc) PB_IR :=
  fun msg =>
    PB_Message_IR_format' _ (PB_Message_default desc) msg.

Theorem PB_Message_IR_format_eq' (desc : PB_Message)
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

Theorem PB_Message_IR_format_eq (desc : PB_Message)
  : forall msg ce,
    refineEquiv (PB_Message_IR_format_ref desc msg ce)
                (PB_Message_IR_format desc msg ce).
Proof.
  apply PB_Message_IR_format_eq'.
Qed.

Definition PB_Message_IR_decode_body
           decode desc (msg : PB_Message_denote desc) ir cd
  : option (PB_Message_denote desc * PB_IR * CacheDecode) :=
  match ir with
  | nil => Some (msg, nil, cd)
  | Build_PB_IRElm t wty v :: ir' =>
    match PB_Message_boundedTag desc t with
    | inl tag =>
      `(msg1, _, cd1) <- decode desc msg ir' cd;
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
                    `(msg3, _, cd2) <- decode desc' msg2 ir2 cd1;
                      Some (f (Some msg3), nil, cd2)
                  | None =>
                    `(msg3, _, cd2) <- decode desc' (PB_Message_default desc') ir2 cd1;
                      Some (f (Some msg3), nil, cd2)
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
                  `(msg2, _, cd2) <- decode desc' (PB_Message_default desc') ir2 cd1;
                    Some (f (a ++ [msg2]), nil, cd2)
              | _ => fun _ => None
              end decode
            | _ => None
            end
        end (PB_Message_update msg1 tag) (PB_Message_lookup msg1 tag)
    | inr tag =>
      if PB_FieldTag_OK_dec (uindex tag) then
        match v with
        | inl (inl _) => decode desc msg ir' cd
        | _ => None
        end
      else None
    end
  end.

Definition PB_Message_IR_decode' (desc : PB_Message) (init : PB_Message_denote desc)
  : DecodeM (PB_Message_denote desc) PB_IR :=
  FueledFix_dep PB_Message_IR_decode_body desc init.

Definition PB_Message_IR_decode (desc : PB_Message)
  : DecodeM (PB_Message_denote desc) PB_IR :=
  PB_Message_IR_decode' desc (PB_Message_default desc).

Lemma PB_Message_IR_Elm_OK (desc : PB_Message)
      (HP : PB_Message_OK desc)
      (msg : PB_Message_denote desc) (ir : PB_IR)
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
      destruct PB_Message_boundedTag eqn:Hb; auto;
        repeat match goal with
            | H : PB_Message_boundedTag _ (uindex _) = inl _ |- _ =>
              exfalso; eapply PB_Message_boundedTag_notl; eauto
            | H : PB_Message_boundedTag _ (bindex _) = inr _ |- _ =>
              exfalso; eapply PB_Message_boundedTag_notr; eauto
            end;
        try (apply PB_Message_boundedTag_correct in Hb;
             apply BoundedTag_inj in Hb; auto; subst;
             rewrite pf; intuition;
             apply PB_IRElm_OK_equiv in IHPB_IR_refine2; eauto using PB_Message_OK_sub_tagToType).
  apply PB_Message_boundedTag_correct' in Hb.
  destruct u, t.
  simpl in Hb. subst. auto.
Qed.

Lemma PB_Message_IR_decode_nil' (desc : PB_Message)
      (init msg : PB_Message_denote desc) (ir ir' : PB_IR)
      (cd cd' : CacheDecode)
  : forall n, FueledFix_dep' PB_Message_IR_decode_body n desc init ir cd = Some (msg, ir', cd') -> ir' = nil.
Proof.
  intro. generalize dependent ir. induction n. easy.
  simpl. unfold PB_Message_IR_decode_body.
  destruct ir; intros. injections. eauto.
  destruct p. destruct PB_Message_boundedTag eqn:?. {
    decode_opt_to_inv.
    revert H0. generalize (PB_Message_update x b) as update, (PB_Message_lookup x b) as lookup.
    destruct PB_Message_tagToType eqn:?; destruct p; intros;
      destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
    destruct lookup; decode_opt_to_inv; easy.
    destruct PB_WireType_eq_dec; injections; try easy.
    destruct lookup; decode_opt_to_inv; easy.
  } {
    destruct PB_FieldTag_OK_dec eqn:?; try easy.
    repeat destruct s; try easy.
    eapply IHn; eauto.
  }
Qed.

Lemma PB_Message_IR_decode_nil (desc : PB_Message)
      (init msg : PB_Message_denote desc) (ir ir' : PB_IR)
      (cd cd' : CacheDecode)
  : PB_Message_IR_decode' desc init ir cd = Some (msg, ir', cd') -> ir' = nil.
Proof.
  eapply PB_Message_IR_decode_nil'.
Qed.

Theorem PB_Message_IR_decode_correct' (desc : PB_Message) (init : PB_Message_denote desc)
        (HP : PB_Message_OK desc)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (fun _ => True)
                   (fun _ ext => ext = mempty)
                   (PB_Message_IR_format' desc init) (PB_Message_IR_decode' desc init) P.
Proof.
  eapply (fix_format_correct_dep _ _ PB_Message_IR_format_body_monotone (fun _ _ => True) (fun _ _ ext => ext = mempty));
    eauto. intros _. intros.
  unfold PB_Message_IR_format_body at 1.
  unfold PB_Message_IR_decode_body at 1.
  split; intros. {
    subst ext. unfold computes_to in H5. unfold Pick in H5.
    destruct_many; subst; simpl in *. {
      eexists. repeat split; eauto.
    } {
      destruct PB_Message_boundedTag eqn:Heq. {
        eapply H in H4; eauto. 2 : omega. destruct_many.
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x4. intros.
        destruct PB_WireType_eq_dec; try easy.
        eexists. repeat split; intros; eauto.
        repeat f_equal. unfold eq_rect_r. simpl.
        rewrite <- eq_rect_eq_dec. eauto. apply PB_WireType_eq_dec.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x4. intros.
        destruct PB_WireType_eq_dec; try easy.
        eexists. repeat split; intros; eauto.
        simpl. repeat f_equal. unfold eq_rect_r. simpl.
        rewrite <- eq_rect_eq_dec. eauto. apply PB_WireType_eq_dec.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x4. intros.
        destruct PB_WireType_eq_dec; try easy.
        eexists. repeat split; intros; eauto.
        repeat f_equal. rewrite <- eq_rect_eq_dec. destruct PB_WireType_eq_dec; auto. congruence.
        apply PB_WireType_eq_dec.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        exfalso. eapply PB_Message_boundedTag_notl; eauto.
      } {
        eexists.
        destruct PB_FieldTag_OK_dec eqn:?.
        repeat split; intros; eauto.
        apply PB_FieldTag_OK_false_iff in Heqb.
        apply PB_Message_boundedTag_correct' in Heq.
        destruct u, x0. simpl in Heq. subst. easy.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H6; eauto using PB_Message_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        revert H5.
        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x5. intros.
        match goal with
        | H : ?a = None |-
          context [match ?b with _ => _ end] => replace b with a; [rewrite H |]
        end.
        rewrite app_nil_r in H6. rewrite H6. clear H6. simpl.
        eexists. repeat split; intros; eauto.
        simpl. reflexivity.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H6; eauto using PB_Message_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        revert H5.
        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x6. intros.
        match goal with
        | H : ?a = Some _ |-
          context [match ?b with _ => _ end] => replace b with a; [rewrite H |]
        end.
        rewrite app_nil_r in H6. rewrite H6. clear H6. simpl.
        eexists. repeat split; intros; eauto.
        simpl. reflexivity.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H5; eauto using PB_Message_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Message_boundedTag eqn:Heq. {
        apply PB_Message_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x5. intros.
        rewrite app_nil_r in H5. rewrite H5. clear H5. simpl.
        eexists. repeat split; intros; eauto.
      } {
        exfalso. eapply PB_Message_boundedTag_notr; eauto.
      }
    }
  } {
    unfold computes_to in *. unfold Pick in *.
    destruct b. {
      injections. split; auto.
      exists [], env. repeat split; eauto.
    } {
      destruct p.
      destruct PB_Message_boundedTag eqn:Heq; simpl in *. {
        decode_opt_to_inv.
        pose proof H4 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
        (* :TODO: better solution? ? ?@ *)
        assert (exists (msg : PB_Message_denote d) (t : BoundedTag d) pf,
                   PB_Message_lookup x b0 = (eq_rect _ _ (PB_Message_lookup msg t) _ pf) /\
                   x = msg /\ b0 = t /\ forall pf', pf = pf') as L1. {
          eexists _, _, eq_refl. intuition eauto.
          apply UIP_dec. apply PB_Type_eq_dec.
        }
        assert (forall a1,
                   exists (msg : PB_Message_denote d) (t : BoundedTag d) pf,
                     PB_Message_update x b0 a1 = PB_Message_update msg t (eq_rect_r _ a1 pf) /\
                     x = msg /\ b0 = t /\ forall pf', pf = pf') as L2. {
          intros. eexists _, _, eq_refl. intuition eauto.
          apply UIP_dec. apply PB_Type_eq_dec.
        }
        revert L1 L2 H5.
        generalize (PB_Message_update x b0) as update.
        generalize (PB_Message_lookup x b0) as lookup.
        simpl in *. intros.

        destruct PB_Message_tagToType eqn:?; destruct p; intros. {
          apply PB_Message_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
          eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. intuition.
          destruct_many. rewrite app_nil_r in *. subst.
          eexists _, _. repeat split; eauto.
          2 : rewrite app_nil_r; reflexivity.
          choose_br 1.
          match goal with
          | |- context [update ?a] => specialize (L2 a)
          end. destruct_many. subst.
          repeat eexists; eauto.
        } {
          apply PB_Message_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
          destruct lookup eqn:?. {
            decode_opt_to_inv. subst.
            pose proof H5 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
            eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
            eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Message_OK_sub_tagToType.
            2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
            intuition. simpl in *. rewrite app_nil_r in *. subst.
            eexists _, _. repeat split; eauto.
            2 : rewrite app_nil_r; reflexivity.
            choose_br 6.
            match goal with
            | |- context [update ?a] => specialize (L2 a)
            end. destruct_many. subst.
            repeat eexists; eauto.
            match goal with
            | H : update ?a = ?b |- _ => rewrite H
            end. repeat f_equal. eauto.
          } {
            decode_opt_to_inv. subst.
            pose proof H5 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
            eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
            eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Message_OK_sub_tagToType.
            2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
            intuition. simpl in *. rewrite app_nil_r in *. subst.
            eexists _, _. repeat split; eauto.
            2 : rewrite app_nil_r; reflexivity.
            choose_br 5.
            match goal with
            | |- context [update ?a] => specialize (L2 a)
            end. destruct_many. subst.
            repeat eexists; eauto.
            match goal with
            | H : update ?a = ?b |- _ => rewrite H
            end. repeat f_equal. eauto.
          }
        } {
          apply PB_Message_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy. {
            eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
            intuition. simpl in *. rewrite app_nil_r in *. subst.
            eexists _, _. repeat split; eauto.
            2 : rewrite app_nil_r; reflexivity.
            choose_br 2.
            match goal with
            | |- context [update ?a] => specialize (L2 a)
            end. destruct_many. subst.
            repeat eexists; eauto.
            match goal with
            | H : update ?a = ?b |- _ => rewrite H
            end. repeat f_equal. eauto.
          } {
            destruct PB_WireType_eq_dec; [easy |]. injections.
            eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
            intuition. simpl in *. rewrite app_nil_r in *. subst.
            eexists _, _. repeat split; eauto.
            2 : rewrite app_nil_r; reflexivity.
            choose_br 3.
            match goal with
            | |- context [update ?a] => specialize (L2 a)
            end. destruct_many. subst.
            repeat eexists; eauto.
            match goal with
            | H : update ?a = ?b |- _ => rewrite H
            end. repeat f_equal. eauto.
          }
        } {
          apply PB_Message_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
          decode_opt_to_inv. subst.
          pose proof H5 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
          eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
          eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Message_OK_sub_tagToType.
          2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
          intuition. simpl in *. rewrite app_nil_r in *. subst.
          eexists _, _. repeat split; eauto.
          2 : rewrite app_nil_r; reflexivity.
          choose_br 7.
          match goal with
          | |- context [update ?a] => specialize (L2 a)
          end. destruct_many. subst.
          repeat eexists; eauto.
          match goal with
          | H : update ?a = ?b |- _ => rewrite H
          end. repeat f_equal. eauto.
        }
      } {
        apply PB_Message_boundedTag_correct' in Heq. subst.
        destruct PB_FieldTag_OK_dec eqn:?; try easy.
        repeat destruct s; try easy.
        pose proof H4 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
        eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
        intuition. simpl in *. rewrite app_nil_r in *. subst.
        eexists _, _. repeat split; eauto.
        2 : rewrite app_nil_r; reflexivity.
        choose_br 4.
        repeat eexists; eauto. apply PB_FieldTag_OK_true_iff in Heqb0. auto.
      }
    }
  }

  intros. unfold PB_Message_IR_decode_body in H0.  unfold PB_Message_IR_decode_body at 1.
  destruct b; eauto.
  destruct p. destruct PB_Message_boundedTag.
  decode_opt_to_inv. apply H in H0. rewrite H0. simpl.
  revert H1.
  generalize (PB_Message_update x b0) as update. generalize (PB_Message_lookup x b0) as lookup.
  destruct PB_Message_tagToType; intros;
    destruct p; destruct PB_WireType_eq_dec; destruct s; eauto;
      destruct lookup; decode_opt_to_inv; apply H in H1; rewrite H1; eauto.
  destruct PB_FieldTag_OK_dec eqn:?; try easy.
  destruct s; eauto. destruct s; eauto.

  Grab Existential Variables. all : auto.
Qed.

Theorem PB_Message_IR_decode_correct (desc : PB_Message)
        (HP : PB_Message_OK desc)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (fun _ => True)
                   (fun _ ext => ext = mempty)
                   (PB_Message_IR_format desc) (PB_Message_IR_decode desc) P.
Proof.
  apply PB_Message_IR_decode_correct'; eauto.
Qed.

Definition PB_Message_format (desc : PB_Message)
  : FormatM (PB_Message_denote desc) ByteString :=
  (fun msg ce =>
     `(ir, _) <- PB_Message_IR_format desc msg ce; SizedList_format PB_IRElm_format (rev ir) ce)%comp.

Definition PB_Message_decode (desc : PB_Message)
  : DecodeM (PB_Message_denote desc) ByteString :=
  fun b cd =>
    `(ir, b', cd') <- SizedList_decode (PB_IRElm_decode desc) (bin_measure b) b cd;
      `(msg, _, _) <- PB_Message_IR_decode desc (rev ir) cd;
      Some (msg, b', cd').

Theorem PB_Message_decode_correct (desc : PB_Message)
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
    pose proof H2.
    eapply (PB_Message_IR_decode_correct desc HP P_OK) in H2; eauto. destruct_many.
    clear H3 H4.
    eapply (SizedList_decode_correct _ _ _ _ P) in H2';
      eauto using PB_IRElm_decode_correct, PB_IRElm_format_sz_eq, PB_IRElm_format_some.
    3 : apply SizedList_predicate_rest_True.
    2 : {
      split. intros; eapply (SizedList_format_sz_eq _ PB_IRElm_format_sz_eq); eauto.
      intros. rewrite <- in_rev in *.
      eapply PB_Message_IR_Elm_OK; eauto.
    }
    destruct_many.
    eexists. repeat split; eauto.
    rewrite @mempty_right in *.
    rewrite H3. simpl. rewrite rev_involutive.
    rewrite H2. eauto.
  } {
    decode_opt_to_inv. subst.
    eapply (SizedList_decode_correct _ _ _ _ P) in H1;
      eauto using PB_IRElm_decode_correct, PB_IRElm_format_sz_eq, PB_IRElm_format_some.
    destruct_many.
    pose proof H2 as Hnil. apply PB_Message_IR_decode_nil in Hnil. subst.
    eapply (PB_Message_IR_decode_correct desc HP P_OK) in H2; eauto. destruct_many.
    subst. split; eauto. eexists _, _. repeat split; eauto.
    computes_to_econstructor; eauto. simpl.
    rewrite @mempty_right in *. subst.
    rewrite rev_involutive. eauto.
  }
Qed.

Print Assumptions PB_Message_decode_correct.