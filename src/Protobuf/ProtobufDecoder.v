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
        Fiat.Protobuf.ProtobufLengthDelimited
        Fiat.Protobuf.ProtobufSpec.

Import FixComp.LeastFixedPointFun.

Local Arguments natToWord : simpl never.
Local Arguments NToWord : simpl never.
Local Arguments wordToN : simpl never.
Local Arguments pow2 : simpl never.
Local Arguments weqb : simpl never.
Local Arguments split1 : simpl never.
Local Arguments split2 : simpl never.
Local Arguments combine : simpl never.
Local Arguments format_wordLE : simpl never.
Local Arguments decode_wordLE : simpl never.
Local Arguments N.shiftl : simpl never.
Local Arguments N.shiftr : simpl never.
Local Arguments N.lor : simpl never.
Local Arguments N.land : simpl never.
Local Arguments CacheDecode : simpl never.

(* The wire type decoder implementation and its correctness proof. *)
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

(* Wire type decoder always decodes something or fails. *)
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

(* Decode from binary strings to IRs. *)
Section PB_IRElm_body.
  Variable format : funType [PB_IRElm; CacheFormat] (ByteString * CacheFormat).
  Variable decode : PB_Descriptor -> DecodeM PB_IRElm ByteString.
  Variable format_some : forall d b ce ce', format d ce ↝ (b, ce') -> lt 0 (bin_measure b).
  Variable format_sz_eq : forall x b1 b2 ce1 ce1' ce2 ce2', format x ce1 ↝ (b1, ce1') ->
                                                       format x ce2 ↝ (b2, ce2') ->
                                                       bin_measure b1 = bin_measure b2.
  Variable format_byte : forall d b ce ce', format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
  Variable P : CacheDecode -> Prop.
  Variable P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)).
  (* Fuel. *)
  Variable n : nat.
  Variable decode_correct : forall b,
      (* Make sure we have enough fuel. *)
      lt (bin_measure b) n ->
      forall desc', CorrectDecoder' _ (PB_IRElm_OK desc') (fun _ _ => True) format (decode desc') P b.

  (* Decode a single IR Element given the tag and wire type. *)
  Definition PB_IRVal_decode
             (desc : PB_Descriptor)
             (t : N) (w : N)
    : DecodeM PB_IRElm ByteString :=
    fun b cd =>
      match PB_WireType_val_inv w with
      | inleft wty =>
        match PB_Descriptor_boundedTag desc t with
        | inl tag =>
          match PB_Descriptor_tagToType tag with
          | PB_Singular (PB_Base pty) =>
            if PB_WireType_eq_dec (PB_BaseType_toWireType pty) wty then
              `(v, b', cd') <- PB_WireType_decode wty b cd;
                Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
            else None
          | PB_Repeated (PB_Base pty) =>
            if PB_WireType_eq_dec (PB_BaseType_toWireType pty) wty then
              `(v, b', cd') <- PB_WireType_decode wty b cd;
                Some (Build_PB_IRElm t wty (inl (inl v)), b', cd')
            else if PB_WireType_eq_dec PB_LengthDelimited wty then
                   let wty := (PB_BaseType_toWireType pty) in
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
          (desc : PB_Descriptor)
    : forall (t : N) (w : N) b,
      lt (bin_measure b) (S n) ->
      CorrectDecoder' _
                     (fun elm => PB_IRTag elm = t /\
                              PB_WireType_val (PB_IRElm_toWireType elm) = w /\
                              PB_IRElm_OK desc elm)
                     (fun _ _ => True)
                     (PB_IRVal_format format) (PB_IRVal_decode desc t w) P b.
  Proof.
    unfold PB_IRElm_OK, PB_IRVal_format, PB_IRVal_decode, PB_IRElm_toWireType. simpl.
    destruct desc as [n' desc].
    intros ? ? ? pf. split; intros.
    - intuition. destruct data as [tag wty val].
      destruct PB_WireType_val_inv eqn:?; subst;
        rewrite PB_WireType_val_inv_correct in Heqs; [| easy].
      simpl in *. subst.
      destruct PB_Descriptor_boundedTag eqn:?. {
        destruct PB_Descriptor_tagToType eqn:?; destruct p0.
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
            edestruct (PB_LengthDelimited_decode_correct (A:=(PB_WireType_denote (PB_BaseType_toWireType p0))))
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
      destruct PB_Descriptor_boundedTag eqn:?. {
        destruct PB_Descriptor_tagToType eqn:?; destruct p0.
        - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intuition. eexists _, _. intuition; eauto.
          rewrite Heqs0.
          destruct PB_Descriptor_tagToType; destruct p; injections; easy.
        - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intros. apply decode_correct. auto.
          intuition. eexists _, _. intuition; eauto. rewrite rev_involutive. eauto. rewrite Heqs0.
          destruct PB_Descriptor_tagToType; destruct p; injections; try easy.
          intuition. apply (PB_IRElm_OK_equiv p0). intro. rewrite <- in_rev. eauto.
        - destruct PB_WireType_eq_dec. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct PB_WireType_decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
          destruct PB_Descriptor_tagToType; destruct p; injections; easy.
          destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct (PB_LengthDelimited_decode_correct (A:=(PB_WireType_denote (PB_BaseType_toWireType p0))))
            as [_ [? [? [? [? [? [? ?]]]]]]];
            eauto using PB_WireType_format_sz_eq, PB_WireType_format_byte,
            PB_WireType_format_some, PB_WireType_decode_correct.
          intuition. eexists _, _. intuition; eauto. rewrite Heqs0.
          destruct PB_Descriptor_tagToType; destruct p; injections; easy.
        - destruct PB_WireType_eq_dec; [| easy]. decode_opt_to_inv.
          subst. existT_eq_dec; try apply PB_WireType_eq_dec.
          subst. simpl.
          edestruct (PB_LengthDelimited_decode_correct' (A:=PB_IRElm)) as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
          intros. apply decode_correct. auto.
          intuition. eexists _, _. intuition; eauto. rewrite rev_involutive; eauto. rewrite Heqs0.
          destruct PB_Descriptor_tagToType; destruct p; injections; try easy.
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

  (* Decode the whole IR element. *)
  Definition PB_IRElm_decode_body (desc : PB_Descriptor) :=
    fun (b : ByteString) (cd : CacheDecode) =>
      `(tw, b1, cd1) <- Varint_decode b cd;
        `(elm, b2, cd2) <- PB_IRVal_decode desc (N.shiftr tw 3) (N.land tw 7) b1 cd1;
        (if (N.lor (N.shiftl (PB_IRTag elm) 3) (PB_WireType_val (PB_IRElm_toWireType elm)) =? tw)%N
         then Some (elm, b2, cd2)
         else None).

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

  Definition PB_IRElm_decode_body_correct (desc : PB_Descriptor)
    : forall b,
      lt (bin_measure b) (S n) ->
      CorrectDecoder' _ (PB_IRElm_OK desc) (fun _ _ => True) (PB_IRElm_format_body format) (PB_IRElm_decode_body desc) P b.
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

End PB_IRElm_body.

Definition PB_IRElm_decode (desc : PB_Descriptor)
  : DecodeM PB_IRElm ByteString :=
  FueledFixP PB_IRElm_decode_body desc.

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

Local Opaque Varint_decode.
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
Definition PB_IRElm_decode_correct (desc : PB_Descriptor)
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
  destruct PB_Descriptor_boundedTag. {
    destruct PB_Descriptor_tagToType; destruct p0.
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

(* Decode from IRs to structured messages. *)
Definition PB_Message_IR_decode_body
           decode desc (msg : PB_Descriptor_denote desc) ir cd
  : option (PB_Descriptor_denote desc * PB_IR * CacheDecode) :=
  match ir with
  | nil => Some (msg, nil, cd)
  | Build_PB_IRElm t wty v :: ir' =>
    match PB_Descriptor_boundedTag desc t with
    | inl tag =>
      `(msg1, _, cd1) <- decode desc msg ir' cd;
        match PB_Descriptor_tagToType tag as x
              return (PB_Type_denote x -> PB_Descriptor_denote desc) ->
                     (PB_Type_denote x) ->
                     _ with
        | PB_Singular (PB_Base pty) =>
          fun f a =>
            match PB_WireType_eq_dec wty (PB_BaseType_toWireType pty) with
            | left pf =>
              match v with
              | inl (inl v') =>
                Some (f (eq_rect _ _ v' _ pf), nil, cd1)
              | _ => None
              end
            | _ => None
            end
        | PB_Repeated (PB_Base pty) =>
          fun f a =>
            match PB_WireType_eq_dec wty (PB_BaseType_toWireType pty) with
            | left pf =>
              match v with
              | inl (inl v') =>
                Some (f (a ++ [(eq_rect _ _ v' _ pf)]), nil, cd1)
              | inl (inr l) =>
                if PB_WireType_eq_dec PB_LengthDelimited (PB_BaseType_toWireType pty) then None
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
                    `(msg3, _, cd2) <- decode desc' (PB_Descriptor_default desc') ir2 cd1;
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
                  `(msg2, _, cd2) <- decode desc' (PB_Descriptor_default desc') ir2 cd1;
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

Definition PB_Message_IR_decode' (desc : PB_Descriptor) (init : PB_Descriptor_denote desc)
  : DecodeM (PB_Descriptor_denote desc) PB_IR :=
  FueledFix_dep PB_Message_IR_decode_body desc init.

Definition PB_Message_IR_decode (desc : PB_Descriptor)
  : DecodeM (PB_Descriptor_denote desc) PB_IR :=
  PB_Message_IR_decode' desc (PB_Descriptor_default desc).

(* We alwasy consume all elements in IR. *)
Lemma PB_Message_IR_decode_nil' (desc : PB_Descriptor)
      (init msg : PB_Descriptor_denote desc) (ir ir' : PB_IR)
      (cd cd' : CacheDecode)
  : forall n, FueledFix_dep' PB_Message_IR_decode_body n desc init ir cd = Some (msg, ir', cd') -> ir' = nil.
Proof.
  intro. generalize dependent ir. induction n. easy.
  simpl. unfold PB_Message_IR_decode_body.
  destruct ir; intros. injections. eauto.
  destruct p. destruct PB_Descriptor_boundedTag eqn:?. {
    decode_opt_to_inv.
    revert H0. generalize (PB_Message_update x b) as update, (PB_Message_lookup x b) as lookup.
    destruct PB_Descriptor_tagToType eqn:?; destruct p; intros;
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

Lemma PB_Message_IR_decode_nil (desc : PB_Descriptor)
      (init msg : PB_Descriptor_denote desc) (ir ir' : PB_IR)
      (cd cd' : CacheDecode)
  : PB_Message_IR_decode' desc init ir cd = Some (msg, ir', cd') -> ir' = nil.
Proof.
  eapply PB_Message_IR_decode_nil'.
Qed.

Local Transparent computes_to.
Local Transparent Pick.
Theorem PB_Message_IR_decode_correct' (desc : PB_Descriptor) (init : PB_Descriptor_denote desc)
        (HP : PB_Descriptor_OK desc)
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
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        eapply H in H4; eauto. 2 : omega. destruct_many.
        apply PB_Descriptor_boundedTag_correct in Heq.
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
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        apply PB_Descriptor_boundedTag_correct in Heq.
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
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        apply PB_Descriptor_boundedTag_correct in Heq.
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
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        exfalso. eapply PB_Descriptor_boundedTag_notl; eauto.
      } {
        eexists.
        destruct PB_FieldTag_OK_dec eqn:?.
        repeat split; intros; eauto.
        apply PB_FieldTag_OK_false_iff in Heqb.
        apply PB_Descriptor_boundedTag_correct' in Heq.
        destruct u, x0. simpl in Heq. subst. easy.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H6; eauto using PB_Descriptor_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        apply PB_Descriptor_boundedTag_correct in Heq.
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
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H6; eauto using PB_Descriptor_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        apply PB_Descriptor_boundedTag_correct in Heq.
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
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    } {
      eapply H in H4; eauto. 2 : omega. destruct_many.
      eapply H in H5; eauto using PB_Descriptor_OK_sub_tagToType.
      2 : unfold PB_IR_measure, PB_IR_measure'; omega. destruct_many.
      destruct PB_Descriptor_boundedTag eqn:Heq. {
        apply PB_Descriptor_boundedTag_correct in Heq.
        apply BoundedTag_inj in Heq; eauto. subst.
        rewrite H4. simpl. clear H4.

        generalize (PB_Message_update x0 x1) as update.
        generalize (PB_Message_lookup x0 x1) as lookup.
        rewrite x5. intros.
        rewrite app_nil_r in H5. rewrite H5. clear H5. simpl.
        eexists. repeat split; intros; eauto.
      } {
        exfalso. eapply PB_Descriptor_boundedTag_notr; eauto.
      }
    }
  } {
    unfold computes_to in *. unfold Pick in *.
    destruct b. {
      injections. split; auto.
      exists [], env. repeat split; eauto.
    } {
      destruct p.
      destruct PB_Descriptor_boundedTag eqn:Heq; simpl in *. {
        decode_opt_to_inv.
        pose proof H4 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
        (* :TODO: better solution? ? ?@ *)
        assert (exists (msg : PB_Descriptor_denote d) (t : BoundedTag d) pf,
                   PB_Message_lookup x b0 = (eq_rect _ _ (PB_Message_lookup msg t) _ pf) /\
                   x = msg /\ b0 = t /\ forall pf', pf = pf') as L1. {
          eexists _, _, eq_refl. intuition eauto.
          apply UIP_dec. apply PB_Type_eq_dec.
        }
        assert (forall a1,
                   exists (msg : PB_Descriptor_denote d) (t : BoundedTag d) pf,
                     PB_Message_update x b0 a1 = PB_Message_update msg t (eq_rect_r _ a1 pf) /\
                     x = msg /\ b0 = t /\ forall pf', pf = pf') as L2. {
          intros. eexists _, _, eq_refl. intuition eauto.
          apply UIP_dec. apply PB_Type_eq_dec.
        }
        revert L1 L2 H5.
        generalize (PB_Message_update x b0) as update.
        generalize (PB_Message_lookup x b0) as lookup.
        simpl in *. intros.

        destruct PB_Descriptor_tagToType eqn:?; destruct p; intros. {
          apply PB_Descriptor_boundedTag_correct in Heq. subst.
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
          apply PB_Descriptor_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
          destruct lookup eqn:?. {
            decode_opt_to_inv. subst.
            pose proof H5 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
            eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
            eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Descriptor_OK_sub_tagToType.
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
            eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Descriptor_OK_sub_tagToType.
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
          apply PB_Descriptor_boundedTag_correct in Heq. subst.
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
          apply PB_Descriptor_boundedTag_correct in Heq. subst.
          destruct PB_WireType_eq_dec; repeat destruct s; injections; try easy.
          decode_opt_to_inv. subst.
          pose proof H5 as Hnil. apply PB_Message_IR_decode_nil' in Hnil. subst.
          eapply H in H4; eauto using PB_IR_measure_cons_lt. 2 : omega. destruct_many.
          eapply H in H5; eauto using PB_IR_measure_embedded_lt, PB_Descriptor_OK_sub_tagToType.
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
        apply PB_Descriptor_boundedTag_correct' in Heq. subst.
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
  destruct p. destruct PB_Descriptor_boundedTag.
  decode_opt_to_inv. apply H in H0. rewrite H0. simpl.
  revert H1.
  generalize (PB_Message_update x b0) as update. generalize (PB_Message_lookup x b0) as lookup.
  destruct PB_Descriptor_tagToType; intros;
    destruct p; destruct PB_WireType_eq_dec; destruct s; eauto;
      destruct lookup; decode_opt_to_inv; apply H in H1; rewrite H1; eauto.
  destruct PB_FieldTag_OK_dec eqn:?; try easy.
  destruct s; eauto. destruct s; eauto.

  Grab Existential Variables. all : auto.
Qed.

Theorem PB_Message_IR_decode_correct (desc : PB_Descriptor)
        (HP : PB_Descriptor_OK desc)
        {P : CacheDecode -> Prop}
        (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
  : CorrectDecoder _
                   (fun _ => True)
                   (fun _ ext => ext = mempty)
                   (PB_Message_IR_format desc) (PB_Message_IR_decode desc) P.
Proof.
  apply PB_Message_IR_decode_correct'; eauto.
Qed.

(* The end-to-end decoder. *)
Definition PB_Message_decode (desc : PB_Descriptor)
  : DecodeM (PB_Descriptor_denote desc) ByteString :=
  fun b cd =>
    `(ir, b', cd') <- SizedList_decode (PB_IRElm_decode desc) (bin_measure b) b cd;
      `(msg, _, _) <- PB_Message_IR_decode desc (rev ir) cd;
      Some (msg, b', cd').

Theorem PB_Message_decode_correct (desc : PB_Descriptor)
        (HP : PB_Descriptor_OK desc)
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
      eapply PB_Message_IR_format_Elm_OK; eauto.
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

(* Our proof is closed. *)
Print Assumptions PB_Message_decode_correct.