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
        Fiat.Common.Tactics.CacheStringConstant
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
        Fiat.Narcissus.Automation.Solver
        Fiat.Narcissus.Examples.ProtobufLengthDelimited
        Fiat.Narcissus.Examples.ProtobufSpec.

Import FixComp.LeastFixedPointFun.

(* :TODO: is this available in the library? *)
Lemma refineEquiv_DoneC E B
      (monoid : Monoid B)
      (format : E -> Comp (B * E))
  : forall ctx,
    refineEquiv (format DoneC ctx)
                (format ctx).
Proof.
  unfold compose; simpl; intros.
  split; unfold Bind2; intros v Comp_v.
  - computes_to_econstructor; eauto; destruct v; simpl.
    computes_to_econstructor; eauto; simpl.
    rewrite mempty_right; eauto.
  - computes_to_inv2.
    rewrite mempty_right; eauto.
Qed.

Lemma refineEquiv_mempty_vector E
  : forall e : E,
    refineEquiv (ret (mempty, e))
           (ret (build_aligned_ByteString (Vector.nil _), e)).
Proof.
  simpl.
  intros; replace ByteString_id
            with (build_aligned_ByteString (Vector.nil _)).
  reflexivity.
  unfold build_aligned_ByteString.
  unfold ByteString_id.
  f_equal.
  apply le_uniqueness_proof.
Qed.

Ltac simpl_rewrite T :=
  let H := fresh in
  pose proof T as H;
  simpl in H; rewrite H; clear H.

Lemma naive_format_list
      {A}
      (A_OK : A -> Prop)
      (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
      (A_encode : A -> CacheFormat -> (ByteString * CacheFormat))
      (A_format_OK :
         forall a ce,
           A_OK a
           -> refine (A_format a ce)
                    (ret (A_encode a ce)))
  : forall (As : list A)
      (ce : CacheFormat),
    (forall a, In a As -> A_OK a)
    -> refine (format_list A_format As ce)
             (ret (encode_list A_encode As ce)).
Proof.
  induction As; intros. easy.
  simpl.
  unfold Bind2. rewrite A_format_OK.
  simplify with monad laws. rewrite IHAs.
  simplify with monad laws. destruct A_encode, encode_list. reflexivity.
  all : intuition.
Qed.

Definition PB_LengthDelimited_encode'
           {A}
           (A_OK : A -> Prop)
           (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
  : { impl : _ |
      forall (A_encode : A -> CacheFormat -> (ByteString * CacheFormat))
        (As : list A)
        (ce : CacheFormat),
        (forall a ce,
             A_OK a
             -> refine (A_format a ce)
                      (ret (A_encode a ce))) ->
        (forall a, In a As -> A_OK a) ->
        refine (PB_LengthDelimited_format A_format As ce)
               (ret (impl A_encode As ce)) }.
Proof.
  eexists. intros.
  unfold PB_LengthDelimited_format.
  unfold Bind2. rewrite SizedList_format_eq_format_list.
  rewrite naive_format_list.
  simplify with monad laws.
  simpl_rewrite (proj2_sig Varint_encode').
  simplify with monad laws.
  higher_order_reflexivity.
  all : eauto.
Defined.

Lemma PB_LengthDelimited_encode_correct
      {A}
      (A_OK : A -> Prop)
      (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
  : forall (A_encode : A -> CacheFormat -> (ByteString * CacheFormat))
      (As : list A)
      (ce : CacheFormat),
    (forall a ce,
        A_OK a
        -> refine (A_format a ce)
                 (ret (A_encode a ce))) ->
    (forall a, In a As -> A_OK a) ->
    refine (PB_LengthDelimited_format A_format As ce)
           (ret ((proj1_sig (PB_LengthDelimited_encode' A_OK A_format)) A_encode As ce)).
Proof.
  apply (proj2_sig (PB_LengthDelimited_encode' A_OK A_format)).
Qed.

Section encode_list'.
  Context {A : Type}.
  Context {B : Type}.
  Context {monoid : Monoid B}.

  Fixpoint encode_list'
           (xs0 : list A)
           (encode_A : forall a : A, In a xs0 -> CacheFormat -> B * CacheFormat)
           (ce : CacheFormat)
    : B * CacheFormat.
    refine
      (match xs0 return (forall a : A, In a xs0 -> CacheFormat -> B * CacheFormat) -> _ with
       | nil => fun _ => (mempty, ce)
       | x :: xs' =>
         fun encode_A =>
           let (b1, env1) := encode_A x _ ce in
           let (b2, env2) := encode_list' xs' (fun a _ ce => encode_A a _ ce) env1 in
           (mappend b1 b2, env2)
       end encode_A); abstract intuition.
  Defined.
End encode_list'.

Lemma naive_format_list'
      {A}
      (A_OK : A -> Prop)
      (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
  : forall (As : list A)
      (A_encode : forall a : A, In a As -> CacheFormat -> (ByteString * CacheFormat))
      (ce : CacheFormat),
    (forall a pf ce,
        A_OK a
        -> refine (A_format a ce)
                 (ret (A_encode a pf ce))) ->
    (forall a, In a As -> A_OK a) ->
    refine (format_list A_format As ce)
             (ret (encode_list' As A_encode ce)).
Proof.
  induction As; intros. easy.
  simpl.
  unfold Bind2. rewrite H.
  simplify with monad laws. rewrite IHAs.
  simplify with monad laws.
  2 : intros; apply H; eauto.
  2-3 : intuition.
  destruct A_encode eqn:Heq1. rewrite Heq1.
  destruct encode_list' eqn:Heq2. rewrite Heq2.
  reflexivity.
Qed.

Definition PB_LengthDelimited_encode''
           {A}
           (A_OK : A -> Prop)
           (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
  : { impl : _ |
      forall (As : list A)
        (A_encode : forall a : A, In a As -> CacheFormat -> (ByteString * CacheFormat))
        (ce : CacheFormat),
        (forall a pf ce,
            A_OK a
            -> refine (A_format a ce)
                     (ret (A_encode a pf ce))) ->
        (forall a, In a As -> A_OK a) ->
        refine (PB_LengthDelimited_format A_format As ce)
               (ret (impl As A_encode ce))}.
Proof.
  eexists. intros.
  unfold PB_LengthDelimited_format.
  unfold Bind2. rewrite SizedList_format_eq_format_list.
  rewrite naive_format_list'.
  simplify with monad laws.
  simpl_rewrite (proj2_sig Varint_encode').
  simplify with monad laws.
  higher_order_reflexivity.
  all : eauto.
Defined.

Lemma PB_LengthDelimited_encode_correct'
      {A}
      (A_OK : A -> Prop)
      (A_format : A -> CacheFormat -> Comp (ByteString * CacheFormat))
  : forall (As : list A)
      (A_encode : forall a : A, In a As -> CacheFormat -> (ByteString * CacheFormat))
      (ce : CacheFormat),
    (forall a pf ce,
        A_OK a
        -> refine (A_format a ce)
                 (ret (A_encode a pf ce))) ->
    (forall a, In a As -> A_OK a) ->
    refine (PB_LengthDelimited_format A_format As ce)
           (ret ((proj1_sig (PB_LengthDelimited_encode'' A_OK A_format)) As A_encode ce)).
Proof.
  apply (proj2_sig (PB_LengthDelimited_encode'' A_OK A_format)).
Qed.

Definition PB_WireType_encode' (wty : PB_WireType)
  : {impl : _ |
     forall (x : PB_WireType_denote wty) (ce : CacheFormat),
        refine (PB_WireType_format wty x ce)
               (ret (impl x ce)) }.
Proof.
  let d := fill_ind_h
             (PB_WireType_rect
                (fun t => PB_WireType_denote t -> CacheFormat -> ByteString * CacheFormat)) in
  refine (exist _ (d wty) _).
  intros. unfold PB_WireType_format.
  destruct wty; simpl in *.
  apply Varint_encode_correct.
  rewrite <- refineEquiv_DoneC.
  etransitivity. apply AlignedFormat32Char; auto.
  simpl. apply refineEquiv_mempty_vector.
  higher_order_reflexivity.
  etransitivity.
  erewrite (format_words _ (n:=32) x).
  apply AlignedFormat32Char; auto.
  rewrite <- refineEquiv_DoneC.
  apply AlignedFormat32Char; auto.
  simpl. apply refineEquiv_mempty_vector.
  higher_order_reflexivity.

  unfold PB_LengthDelimited_format.
  etransitivity.
  unfold Bind2. rewrite SizedList_format_eq_format_list.
  rewrite <- refineEquiv_DoneC.
  rewrite AlignedFormatListDoneC with (A_OK := fun _ => True); intros; eauto.
  simpl. simplify with monad laws.

  apply refine_bind. apply Varint_encode_correct. intro.
  higher_order_reflexivity.
  rewrite aligned_format_char_eq. encoder_reflexivity.

  simpl. simplify with monad laws.
  higher_order_reflexivity.

  Grab Existential Variables.
  auto.
Defined.

Definition PB_WireType_encode_correct (wty : PB_WireType)
  : forall (x : PB_WireType_denote wty) (ce : CacheFormat),
        refine (PB_WireType_format wty x ce)
               (ret ((proj1_sig (PB_WireType_encode' wty)) x ce)).
Proof.
  apply (proj2_sig (PB_WireType_encode' wty)).
Qed.

Lemma PB_IRElm_measure_eq (elm : PB_IRElm)
  : PB_IRElm_measure elm = PB_IR_measure [elm].
Proof.
  simpl. omega.
Qed.

Lemma PB_IRElm_well_founded
  : well_founded (fun e1 e2 => lt (PB_IRElm_measure e1) (PB_IRElm_measure e2)).
Proof.
  apply well_founded_ltof.
Qed.

Arguments proj1_sig : simpl never.

Definition PB_IRElm_encode'
  : {impl : _ | refineFun (fDom:=[PB_IRElm; CacheFormat]) PB_IRElm_format (Lift_cfunType _ _ impl)}.
Proof.
  eexists.
  etransitivity.
  - eapply Finish_refining_LeastFixedPoint with (wf_P := PB_IRElm_well_founded);
      unfold PB_IRElm_format_body, PB_IRVal_format; simpl; intros.
    apply PB_IRElm_format_body_monotone. auto.
    unfold respectful_hetero; simpl; intros.
    unfold compose; intros. unfold Bind2.

    simpl_rewrite Varint_encode_correct. simplify with monad laws.
    instantiate (1:=fun r y t =>
                      match r return _ -> _ with
                      | Build_PB_IRElm _ ty val =>
                        match val with
                        | inl (inl v) => fun _ => _
                        | inl (inr l) => fun _ => _
                        | inr ir => fun _ => _
                        end
                      end y).
    simpl.
    destruct r. repeat destruct s; simpl.
    rewrite PB_WireType_encode_correct. simplify with monad laws. higher_order_reflexivity.
    rewrite PB_LengthDelimited_encode_correct with (A_OK:=fun _ => True); intros; auto.
    simplify with monad laws.
    2 : apply PB_WireType_encode_correct.
    higher_order_reflexivity.

    rewrite PB_LengthDelimited_encode_correct' with (A_OK:=fun _ => True); intros; auto.
    simplify with monad laws. simpl.
    2 : {
      rewrite H.
      match goal with
      | |- context [y ?a ?b] =>
        match type of b with
        | ?H =>
          let L := fresh in
          assert H as L; [| clear L]
        end
      end. {
        revert pf.
        clear. intros.
        abstract (rewrite <- in_rev in pf;
                  induction l; destruct pf; subst; simpl in *; try specialize (IHl H); omega)
                 using PB_IRElm_encode'_subproof.
      }
      instantiate (2:=PB_IRElm_encode'_subproof n PB_IRType l a pf).
      simpl.
      higher_order_reflexivity.
    }
    higher_order_reflexivity.
  - simpl. intros. higher_order_reflexivity.
Defined.

Definition PB_Message_IR_encode' (PB_Message_IR_encode : forall desc, PB_Message_denote desc -> PB_IR)
  : forall {n} (desc : PB_Desc n), PB_Message_denote (Build_PB_Message desc) -> PB_IR.
Proof.
  refine
    (fix PB_Message_IR_encode' {n} (desc : PB_Desc n) (msg : PB_Message_denote (Build_PB_Message desc)) :=
       match desc return PB_Message_denote (Build_PB_Message desc) -> _ with
       | Vector.nil => fun _ => nil
       | Vector.cons fld _ desc' =>
         match fld with
         | Build_PB_Field ty _ t =>
           fun msg =>
             let ir := PB_Message_IR_encode' desc' (ilist2_tl msg) in
             match ty with
             | PB_Singular (PB_Primitive pty) =>
               fun a =>
                 (Build_PB_IRElm t (PB_PrimitiveType_toWireType pty)
                                 (inl (inl _))) :: ir
             | PB_Repeated (PB_Primitive pty) =>
               fun a =>
                 if PB_WireType_eq_dec PB_LengthDelimited (PB_PrimitiveType_toWireType pty) then
                   List.rev (List.map (fun v =>
                                         Build_PB_IRElm t (PB_PrimitiveType_toWireType pty)
                                                        (inl (inl v)))
                                      _)
                            ++ ir
                 else
                   (Build_PB_IRElm t (PB_PrimitiveType_toWireType pty)
                                   (inl (inr _))) :: ir
             | PB_Singular (PB_Embedded desc') =>
               fun a =>
                 match _ with
                 | Some msg' =>
                   (Build_PB_IRElm t PB_LengthDelimited
                                   (inr (PB_Message_IR_encode desc' msg'))) :: ir
                 | None => ir
                 end
             | PB_Repeated (PB_Embedded desc') =>
               fun a =>
                 List.rev (List.map (fun v =>
                                       Build_PB_IRElm t PB_LengthDelimited
                                                      (inr (PB_Message_IR_encode desc' v)))
                                    _)
                          ++ ir
             end (ilist2_hd msg)
         end
       end msg); exact a.
Defined.

Fixpoint PB_Message_IR_encode (desc : PB_Message)
         (msg : PB_Message_denote desc) {struct desc}
  : PB_IR :=
  match desc return _ -> _ with
  | Build_PB_Message _ desc =>
    fun msg => PB_Message_IR_encode' PB_Message_IR_encode desc msg
  end msg.

Local Transparent computes_to.
Local Transparent Pick.
Local Arguments PB_Message_OK : simpl never.

Lemma PB_Message_boundedTag_hd'
  : forall ty name t n (desc' : PB_Desc n),
    exists tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')),
      t = bindex tag /\ ibound (indexb tag) = Fin.F1.
Proof.
  intros. exists ({| bindex := t |}). auto.
Qed.

Lemma PB_Message_boundedTag_hd
  : forall ty name t n (desc' : PB_Desc n),
    exists tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')),
      t = bindex tag.
Proof.
  intros. edestruct PB_Message_boundedTag_hd'; eauto. destruct_many. eauto.
Qed.

Lemma PB_Message_boundedTag_tl'
  : forall ty name t n (desc' : PB_Desc n)
      (tag' : BoundedTag (Build_PB_Message desc')),
    exists (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))),
      bindex tag = bindex tag' /\ ibound (indexb tag) = Fin.FS (ibound (indexb tag')).
Proof.
  intros. destruct tag'. destruct indexb.
  eexists ({| bindex := bindex; indexb := {| ibound := Fin.FS ibound |} |}).
  simpl. intuition.
  Grab Existential Variables.
  auto.
Qed.

Lemma PB_Message_boundedTag_tl
  : forall ty name t n (desc' : PB_Desc n)
      (tag' : BoundedTag (Build_PB_Message desc')),
    exists (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))),
      bindex tag = bindex tag'.
Proof.
  intros. edestruct PB_Message_boundedTag_tl'; eauto. destruct_many. eauto.
Qed.

Lemma PB_Message_boundedTag_hd_index
  : forall ty name t n (desc' : PB_Desc n),
    PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')) ->
    forall tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')),
      t = bindex tag ->
      ibound (indexb tag) = Fin.F1.
Proof.
  intros.
  edestruct PB_Message_boundedTag_hd'. destruct_many.
  replace tag with x. auto.
  eapply BoundedTag_inj; congruence.
Qed.

Lemma PB_Message_boundedTag_tl_index
  : forall ty name t n (desc' : PB_Desc n),
      PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')) ->
    forall (tag' : BoundedTag (Build_PB_Message desc'))
      (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))),
    bindex tag = bindex tag' ->
    ibound (indexb tag) = Fin.FS (ibound (indexb tag')).
Proof.
  intros.
  edestruct PB_Message_boundedTag_tl'. destruct_many.
  replace tag with x. eauto.
  eapply BoundedTag_inj; congruence.
Qed.

Lemma PB_Message_tagToType_cons
     : forall ty name t n (desc' : PB_Desc n),
       PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')) ->
       forall tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')),
       t = bindex tag ->
       PB_Message_tagToType tag = ty.
Proof.
  intros.
  erewrite <- PB_Message_tagToType_correct;
    eauto using Vector.In_cons_hd; eauto.
Qed.

Lemma PB_Message_update_hd
  : forall ty name t n (desc' : PB_Desc n)
      (HOK : PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))),
    t = bindex tag ->
    forall (msg : PB_Message_denote (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))) v v' pf,
      ilist2_hd msg = v' ->
      msg = PB_Message_update
              (desc:=Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))
              (icons2 v (ilist2_tl msg)) tag (eq_rect_r PB_Type_denote v' pf).
Proof.
  intros.
  apply PB_Message_boundedTag_hd_index in H; eauto.

  destruct msg. destruct tag. destruct indexb. simpl in *. subst.
  unfold PB_Message_update'. unfold SetAttributeRaw. simpl in *.
  unfold icons2. f_equal. unfold eq_rect_r.
  rewrite <- eq_rect_eq_dec by apply PB_Type_eq_dec. reflexivity.
Qed.

Lemma PB_Message_update_tl
  : forall ty name t n (desc' : PB_Desc n)
      (HOK : PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag' : BoundedTag (Build_PB_Message desc')),
    bindex tag = bindex tag' ->
    forall (msg : PB_Message_denote (Build_PB_Message desc')) ty' v (v' : PB_Type_denote ty') pf pf',
      icons2 v (PB_Message_update msg tag' (eq_rect_r PB_Type_denote v' pf))
      = PB_Message_update
          (desc:=Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))
          (icons2 v msg) tag (eq_rect_r PB_Type_denote v' pf').
Proof.
  intros.
  apply PB_Message_boundedTag_tl_index in H; eauto.
  destruct tag. destruct indexb.
  destruct tag'. destruct indexb.
  simpl in *. subst.
  unfold PB_Message_update'. unfold SetAttributeRaw.
  unfold type_cast, eq_rect_r.
  rewrite <- !eq_rect_eq_dec by apply PB_Type_eq_dec. reflexivity.
Qed.

Lemma PB_Message_lookup_hd
  : forall ty name t n (desc' : PB_Desc n)
      (HOK : PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))),
      t = bindex tag ->
    forall (msg : PB_Message_denote (Build_PB_Message desc')) v pf,
      eq_rect _ PB_Type_denote
              (PB_Message_lookup
                 (desc:=Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))
                 (icons2 v msg) tag)
              _ pf = v.
Proof.
  intros.
  apply PB_Message_boundedTag_hd_index in H; eauto.
  destruct tag. destruct indexb. simpl in *. subst.
  unfold PB_Message_lookup'. unfold GetAttributeRaw. simpl in *.
  rewrite <- eq_rect_eq_dec by apply PB_Type_eq_dec. reflexivity.
Qed.

Lemma PB_Message_lookup_tl
  : forall ty name t n (desc' : PB_Desc n)
      (HOK : PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag : BoundedTag (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc')))
      (tag' : BoundedTag (Build_PB_Message desc')),
    bindex tag = bindex tag' ->
    forall (msg : PB_Message_denote (Build_PB_Message desc')) ty' v pf pf',
      eq_rect _ PB_Type_denote
              (PB_Message_lookup msg tag')
              ty' pf
      = eq_rect _ PB_Type_denote
                (PB_Message_lookup
                   (desc:=Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc'))
                   (icons2 v msg) tag)
                ty' pf'.
Proof.
  intros.
  apply PB_Message_boundedTag_tl_index in H; eauto.
  destruct tag. destruct indexb.
  destruct tag'. destruct indexb.
  simpl in *. subst.
  unfold PB_Message_lookup'. unfold GetAttributeRaw.
  rewrite <- !eq_rect_eq_dec by apply PB_Type_eq_dec. reflexivity.
Qed.

Lemma PB_Message_OK_hd
  : forall n (desc : PB_Desc n) fld,
    PB_Message_OK (Build_PB_Message (Vector.cons _ fld _ desc)) ->
    PB_Message_OK (Build_PB_Message (Vector.cons _ fld _ (Vector.nil _))).
Proof.
  unfold PB_Message_OK. simpl.
  intros. destruct_many. intuition.
  constructor. inversion H. auto. constructor.
  unfold PB_Message_tags_nodup. simpl. clear. intros.
  apply Fin.to_nat_inj.
  destruct Fin.to_nat. destruct Fin.to_nat.
  inversion l; [| easy]. inversion l0; [| easy]. subst. reflexivity.
  unfold PB_Message_names_nodup. simpl. clear. intros.
  apply Fin.to_nat_inj.
  destruct Fin.to_nat. destruct Fin.to_nat.
  inversion l; [| easy]. inversion l0; [| easy]. subst. reflexivity.
Qed.

Lemma PB_Message_OK_tl
  : forall n (desc : PB_Desc n) fld,
    PB_Message_OK (Build_PB_Message (Vector.cons _ fld _ desc)) ->
    PB_Message_OK (Build_PB_Message desc).
Proof.
  unfold PB_Message_OK. simpl.
  intros. destruct_many. intuition.
  inversion H. existT_eq_dec. subst. auto.
  unfold PB_Message_tags_nodup. simpl. intros.
  eapply vec_nodup_cons; eauto. apply H0.
  unfold PB_Message_names_nodup. simpl. intros.
  eapply vec_nodup_cons; eauto. apply H1.
Qed.

Lemma PB_Message_IR_format_pres
  : forall {n} (desc : PB_Desc n) msg1 msg2 ir ce1 ce2,
    PB_Message_IR_format' (Build_PB_Message desc) msg1 msg2 ce1 ↝ (ir, ce2) ->
    forall ty name t v,
      PB_Message_OK (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc)) ->
      (forall t' ty' v', In (Build_PB_IRElm t' ty' v') ir -> Vector.In t' (PB_Message_tags' desc)) ->
      PB_Message_IR_format' (Build_PB_Message (Vector.cons _ (Build_PB_Field ty name t) _ desc))
                           (icons2 v msg1) (icons2 v msg2) ce1 ↝ (ir, ce2).
Proof.
  intros. rename H0 into HOK. apply PB_Message_IR_format_eq'.
  apply (proj1 (PB_Message_IR_format_eq' _ _ _ _)) in H.
  simpl PB_Message_IR_format_ref' in *. unfold computes_to, Pick in *. simpl fst in *.

  generalize dependent msg1.
  generalize dependent msg2.
  induction ir; intros; inversion H; repeat (existT_eq_dec; [| apply PB_Message_eq_dec]); subst;
    try match goal with
    | H : BoundedTag (Build_PB_Message desc) |- _ =>
      edestruct PB_Message_boundedTag_tl with (tag' := H)
    end;
    repeat match goal with
           | |- context [icons2 ?v (PB_Message_update _ ?t _)] =>
             erewrite PB_Message_update_tl with (v := v) (tag' := t); eauto
           | |- context [PB_Message_lookup ?x ?t] =>
             match x with
             | icons2 _ _ => fail 1
             | _ => erewrite PB_Message_lookup_tl with (tag' := t); eauto
             end
           | H : bindex ?a = bindex ?b |- _ => simpl in H; rewrite <- H
           end; try solve [constructor; eauto with datatypes; erewrite <- PB_Message_lookup_tl; eauto].
  - destruct t0. simpl in *.
    exfalso. eauto.
  - eapply PB_IR_embedded_some; eauto with datatypes.
    erewrite <- PB_Message_lookup_tl; eauto.
    Grab Existential Variables.
    all : rewrite <- pf; apply PB_Message_boundedTag_tl_index in H0; eauto;
      unfold PB_Message_tagToType; simpl in *; rewrite H0; reflexivity.
Qed.

Lemma PB_Message_IR_encode_in_tags
  : forall t ty v n (desc : PB_Desc n) msg,
    In (Build_PB_IRElm t ty v) (PB_Message_IR_encode (Build_PB_Message desc) msg) ->
    Vector.In t (PB_Message_tags' desc).
Proof.
  intros.
  induction desc. easy.
  simpl in *.
  destruct h as [ty' ? t'].
  destruct ty' as [sty | sty]; destruct sty as [pty | desc']; simpl in *. {
    destruct H. inversion H. constructor. constructor. eauto.
  } {
    destruct ilist.prim_fst.
    destruct H. inversion H. constructor. constructor. eauto.
    constructor. eauto.
  } {
    destruct PB_WireType_eq_dec.
    apply in_app_iff in H.
    destruct H. apply in_rev in H.
    apply in_map_iff in H.
    destruct_many. inversion H. constructor.
    constructor. eauto.
    destruct H. inversion H. constructor. constructor. eauto.
  } {
    apply in_app_iff in H.
    destruct H. apply in_rev in H.
    apply in_map_iff in H.
    destruct_many. inversion H. constructor.
    constructor. eauto.
  }
Qed.

Lemma PB_Message_IR_encode_correct
  : forall desc,
    PB_Message_OK desc ->
    forall (msg : PB_Message_denote desc),
    refine (PB_Message_IR_format desc msg ())
           (ret (PB_Message_IR_encode desc msg, ())).
Proof.
  intros ? HOK ?. intros [ir ce] H.
  apply Return_inv in H. injections.

  remember (PB_Message_IR_encode desc msg) as ir.
  revert desc HOK msg Heqir.
  induction ir as [ir IH] using (well_founded_ind well_founded_lt_b).
  intros.
  destruct desc as [n desc].
  induction desc; intros;
    unfold PB_Message_IR_format, PB_Message_IR_format'.
  apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
  choose_br 0. destruct msg. eauto.
  destruct h as [ty ? t].
  destruct ty as [sty | sty]; destruct sty as [pty | desc'];
    simpl in Heqir. {
    apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
    destruct ir. easy.
    edestruct PB_Message_boundedTag_hd.
    injections.
    choose_br 1. repeat eexists.
    2 : f_equal; f_equal; eauto.
    2 : apply PB_Message_update_hd; auto.
    simpl. apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
    apply IH; eauto using PB_Message_OK_tl, PB_IR_measure_cons_lt.
  } {
    edestruct PB_Message_boundedTag_hd.
    destruct ilist.prim_fst eqn:?.
    apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
    destruct ir. easy.
    injections.
    choose_br 5. repeat eexists.
    2 : apply PB_Message_lookup_hd; eauto.
    3 : f_equal; f_equal; eauto.
    simpl. apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
    apply IH; eauto using PB_Message_OK_tl, PB_IR_measure_cons_lt. reflexivity.
    apply IH. apply PB_IR_measure_embedded_lt.
    eapply PB_Message_OK_sub_tagToType; eauto using PB_Message_tagToType_cons.
    reflexivity.
    apply PB_Message_update_hd; eauto.
    simpl.
    replace msg with (icons2 (ilist2_hd msg) (ilist2_tl msg)).
    rewrite <- Heqp. subst.
    apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
    apply IHdesc; eauto using PB_Message_OK_tl.
    destruct msg. reflexivity.
  } {
    destruct PB_WireType_eq_dec. simpl.
    replace msg with (icons2 (ilist2_hd msg) (ilist2_tl msg)) by (destruct msg; auto).
    subst.
    simpl. destruct msg as [v ?]. simpl in *. intros. {
      induction v using rev_ind; intros.
      simpl. apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
      apply IHdesc; eauto using PB_Message_OK_tl.
      rewrite <- !map_rev in *. rewrite rev_app_distr in *. simpl in *.
      unfold lt_B in *.

      apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
      edestruct PB_Message_boundedTag_hd.
      choose_br 2. repeat eexists.
      apply IHv; eauto. intros. apply IH; eauto. simpl in *. omega.

      repeat f_equal. apply H.

      apply PB_Message_update_hd; eauto using PB_Message_OK_hd.
      simpl. f_equal.
      simpl_rewrite PB_Message_lookup_hd; eauto using PB_Message_OK_hd.
    }

    apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
    destruct ir. easy.
    edestruct PB_Message_boundedTag_hd.
    injections.
    choose_br 3. repeat eexists.
    2 : eauto.
    2 : f_equal; f_equal; eauto.
    2 : apply PB_Message_update_hd; auto.
    simpl. apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
    apply IH; eauto using PB_Message_OK_tl, PB_IR_measure_cons_lt.
    simpl. simpl_rewrite PB_Message_lookup_hd; eauto using PB_Message_OK_hd.
  } {
    replace msg with (icons2 (ilist2_hd msg) (ilist2_tl msg)) by (destruct msg; auto).
    subst.
    simpl. destruct msg as [v ?]. simpl in *. intros. {
      induction v using rev_ind; intros.
      simpl. apply PB_Message_IR_format_pres; eauto using PB_Message_IR_encode_in_tags.
      apply IHdesc; eauto using PB_Message_OK_tl.
      rewrite <- !map_rev in *. rewrite rev_app_distr in *. simpl in *.
      unfold lt_B in *.

      apply (unroll_LeastFixedPoint_dep' PB_Message_IR_format_body_monotone).
      edestruct PB_Message_boundedTag_hd.
      choose_br 7. repeat eexists.
      apply IHv; eauto. intros. apply IH; eauto. simpl in *. omega.
      intros. apply IH; eauto. simpl in *. omega.
      3 : {
        apply PB_Message_update_hd; eauto using PB_Message_OK_hd.
        simpl. f_equal.
        simpl_rewrite PB_Message_lookup_hd; eauto using PB_Message_OK_hd.
      }
      2 : {
        repeat f_equal. apply H.
      }
      apply IH; eauto.
      apply PB_IR_measure_embedded_lt.
      clear H x0.
      edestruct PB_Message_boundedTag_hd.
      eapply PB_Message_OK_sub_tagToType; eauto using PB_Message_tagToType_cons.
    }
  }
  Grab Existential Variables.
  all : apply PB_Message_tagToType_cons; eauto using PB_Message_OK_hd.
Qed.

Print Assumptions PB_Message_IR_encode_correct.