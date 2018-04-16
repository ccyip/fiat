Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Coq.Logic.Eqdep_dec
        Fiat.Computation
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.Compose
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.VarintOpt
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignedMonads
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Narcissus.BinLib.AlignedVarint
        Fiat.Narcissus.Examples.ProtobufSpec.

Local Open Scope AlignedDecodeM_scope.
Local Open Scope nat_scope.

Lemma Throw_DecodeMEquivAlignedDecodeM {cache : Cache} {A : Type}
  : DecodeMEquivAlignedDecodeM (C:=A)
      (fun (_ : ByteString) (_ : CacheDecode) => None)
      (fun _ => ThrowAlignedDecodeM).
Proof.
  unfold ThrowAlignedDecodeM.
  unfold DecodeMEquivAlignedDecodeM; intros.
  repeat split; try easy.
Qed.

Lemma Compose_DecodeMEquivAlignedDecodeM {cache : Cache} {A : Type}
      (f : CacheDecode -> option (A * CacheDecode))
    : DecodeMEquivAlignedDecodeM
        (fun (b : ByteString) (cd : CacheDecode) =>
           `(a, cd') <- f cd;
             Some (a, b, cd'))
        (fun numBytes => fun v idx cd => `(a, cd') <- f cd;
                                     Some (a, idx, cd')).
Proof.
  unfold DecodeMEquivAlignedDecodeM; intros.
  split; [| split]; intros; destruct f; try easy; destruct p.
  - intuition.
  - inversion H. omega.
  - simpl. repeat split; try easy; inversion H; subst; clear H; simpl;
             replace (n - n) with 0 by omega; auto.
    exists (@Vector.nil _).
    rewrite <- build_aligned_ByteString_append. auto.
Qed.

Definition AlignedDecodeNChar numBytes
  : forall n, AlignedDecodeM (word (8*n)) numBytes.
Proof.
  refine
    (fix decode n :=
       match n with
       | O => return WO
       | S n' =>
         b <- GetCurrentByte;
         w <- decode n';
         return _ (* append_word w b *)
       end).
  replace (8 * S n') with (8 * n' + 8) by abstract omega.
  exact (append_word w b).
Defined.

(* :TODO: should I? *)
Local Arguments AlignedDecodeNChar : simpl never.
Local Arguments Nat.mul : simpl never.
Local Arguments Nat.add : simpl never.
Local Arguments decode_word' : simpl never.
Local Arguments natToWord : simpl never.
Local Arguments wordToNat : simpl never.
Local Arguments NToWord : simpl never.
Local Arguments wordToN : simpl never.
Local Arguments pow2 : simpl never.
Local Arguments weqb : simpl never.
Local Arguments split1 : simpl never.
Local Arguments split2 : simpl never.
Local Arguments weq : simpl never.
Local Arguments append_word : simpl never.
Lemma AlignedDecodeNCharM (n : nat)
  : DecodeMEquivAlignedDecodeM
      (decode_word (monoidUnit := ByteString_QueueMonoidOpt) (sz := 8*n))
      (fun numBytes => AlignedDecodeNChar numBytes n).
Proof.
  induction n. {
    unfold decode_word. apply Return_DecodeMEquivAlignedDecodeM.
  } {
    unfold AlignedDecodeNChar.
    generalize (AlignedDecodeNChar_subproof n). intros.
    destruct e. simpl.
    eapply DecodeMEquivAlignedDecodeM_trans with
        (bit_decoder1 :=
           (fun (v : ByteString) (cd : CacheDecode) =>
              `(w1, bs, cd') <- decode_word (sz := 8) v cd;
              `(w2, bs, cd') <- decode_word (sz := (8*n)) bs cd';
              Some ((Core.append_word w2 w1), bs, cd'))); intros.
    eapply AlignedDecodeBindCharM; intros.
    eapply Bind_DecodeMEquivAlignedDecodeM; intros. eauto.
    apply Return_DecodeMEquivAlignedDecodeM.
    unfold decode_word.
    rewrite decode_word_plus.
    rewrite decode_word_plus'.
    destruct (decode_word' _ b) as [ [? ?] | ]; eauto. simpl.
    destruct (decode_word' _ b0) as [ [? ?] | ]; eauto. simpl.
    repeat progress f_equal.
    repeat match goal with
    | |- context [Nat.add_comm ?a ?b] => generalize (Nat.add_comm a b); intros
    end.
    destruct e. simpl. rewrite <- eq_rect_eq_dec; eauto using eq_nat_dec.
    reflexivity.
  }
Qed.

Lemma Aligned_PB_SingularType_decodeM'
      (sty : PB_SingularType)
  : {impl : _ | DecodeMEquivAlignedDecodeM (PB_SingularType_decode sty) impl}.
Proof.
  let d := fill_ind_h
             (PB_SingularType_rect
                (fun sty => forall n, AlignedDecodeM (PB_SingularType_denote sty) n)) in
  refine (exist _ (d sty) _).

  destruct sty; simpl.
  apply (AlignedDecodeNCharM 4).
  apply (AlignedDecodeNCharM 8).
  apply Aligned_Varint_decodeM.
  apply Aligned_Varint_decodeM.
Defined.

Definition Aligned_PB_SingularType_decode (sty : PB_SingularType) :=
  Eval simpl in proj1_sig (Aligned_PB_SingularType_decodeM' sty).

Lemma Aligned_PB_SingularType_decodeM
      (sty : PB_SingularType)
  : DecodeMEquivAlignedDecodeM (PB_SingularType_decode sty)
                               (Aligned_PB_SingularType_decode sty).
Proof.
  apply (proj2_sig (Aligned_PB_SingularType_decodeM' sty)).
Qed.

Lemma Aligned_PB_Type_decodeM'
      (ty : PB_Type)
  : {impl : _ | DecodeMEquivAlignedDecodeM (PB_Type_decode ty) impl}.
Proof.
  let d := fill_ind_h
             (PB_Type_rect
                (fun ty => forall n, AlignedDecodeM (PB_Type_denote ty) n)) in
  refine (exist _ (d ty) _).

  destruct ty; simpl.
  apply Aligned_PB_SingularType_decodeM.
Defined.

Definition Aligned_PB_Type_decode (ty : PB_Type) :=
  Eval simpl in proj1_sig (Aligned_PB_Type_decodeM' ty).

Lemma Aligned_PB_Type_decodeM
      (ty : PB_Type)
  : DecodeMEquivAlignedDecodeM (PB_Type_decode ty)
                               (Aligned_PB_Type_decode ty).
Proof.
  apply (proj2_sig (Aligned_PB_Type_decodeM' ty)).
Qed.

Lemma Aligned_PB_IRVal_decodeM' {n} (desc : PB_Message n)
      (t : N) (wty : N)
  : {impl : _ | DecodeMEquivAlignedDecodeM (PB_IRVal_decode desc t wty) impl}.
Proof.
  unfold PB_IRVal_decode.
  refine (exist _ (fun numBytes => match PB_Message_boundedTag desc t with
                                | inleft tag => _
                                | inright _ => _
                                end) _).
  destruct PB_Message_boundedTag eqn:?.
  - eapply Bind_DecodeMEquivAlignedDecodeM; intros.
    apply Aligned_PB_Type_decodeM. apply Return_DecodeMEquivAlignedDecodeM.
  - apply Throw_DecodeMEquivAlignedDecodeM.
Defined.

Definition Aligned_PB_IRVal_decode {n} (desc : PB_Message n)
      (t : N) (wty : N) :=
  Eval simpl in proj1_sig (Aligned_PB_IRVal_decodeM' desc t wty).

Lemma Aligned_PB_IRVal_decodeM {n} (desc : PB_Message n)
      (t : N) (wty : N)
  : DecodeMEquivAlignedDecodeM (PB_IRVal_decode desc t wty)
                               (Aligned_PB_IRVal_decode desc t wty).
Proof.
  apply (proj2_sig (Aligned_PB_IRVal_decodeM' desc t wty)).
Qed.

Definition Aligned_PB_IRElm_decodeM' {n} (desc : PB_Message n)
  : {impl : _ | DecodeMEquivAlignedDecodeM (PB_IRElm_decode desc) impl}.
Proof.
  unfold PB_IRElm_decode. eexists.
  eapply Bind_DecodeMEquivAlignedDecodeM; intros.
  apply Aligned_Varint_decodeM.
  eapply Bind_DecodeMEquivAlignedDecodeM; intros.
  match goal with
  | |- context [PB_IRVal_decode _ ?t ?w] => apply (Aligned_PB_IRVal_decodeM _ t w)
  end.
  instantiate
    (1:= fun a0 =>
           if ((N.lor (N.shiftl (PB_IRTag a0) 3)
                      (PB_WireType_denote
                         (PB_Type_toWireType (PB_IRType a0))) =? a)%N)%bool
           then _ else _).
  destruct N.eqb eqn:?; destruct N.eqb eqn:?; try easy.
  - apply Return_DecodeMEquivAlignedDecodeM.
  - apply Throw_DecodeMEquivAlignedDecodeM.
Defined.

Definition Aligned_PB_IRElm_decode {n} (desc : PB_Message n) :=
  Eval simpl in proj1_sig (Aligned_PB_IRElm_decodeM' desc).

Lemma Aligned_PB_IRElm_decodeM {n} (desc : PB_Message n)
  : DecodeMEquivAlignedDecodeM (PB_IRElm_decode desc)
                               (Aligned_PB_IRElm_decode desc).
Proof.
  apply (proj2_sig (Aligned_PB_IRElm_decodeM' desc)).
Qed.

(* :TODO: move this somewhere else. *)
Lemma DecodeMEquivAlignedDecodeM_lt {cache : Cache} {C}
  : forall f f',
    DecodeMEquivAlignedDecodeM (C:=C) f f' ->
    (* :Q: should we include this (stronger version) in equiv relation? *)
    (forall idx cd, f' 0 (Vector.nil char) (S idx) cd = None) ->
    (forall b cd a b' cd',
        f b cd = Some (a, b', cd') -> lt_B b' b) ->
    forall n (v : Vector.t char n) idx cd a idx' cd',
      f' n v idx cd = Some (a, idx', cd') ->
      idx < idx'.
Proof.
  intros f f' Heq Ha Hlt n v idx. generalize dependent n.
  induction idx; intros. {
    destruct Heq as [? [_ [? ?]]].
    destruct (f (build_aligned_ByteString v) cd) eqn:?;
             [ | apply H1 in Heqo; congruence].
    repeat destruct p.
    specialize (Hlt _ _ _ _ _ Heqo).
    specialize (H2 _ _ _ Heqo). destruct H2 as [? _].
    rewrite H2 in H. inversion H; subst; clear H.
    unfold lt_B in *. simpl in *. unfold length_ByteString in *.
    simpl in *. omega.
  } {
    destruct Heq as [? [_ _]].
    destruct v. {
      rewrite Ha in H. easy.
    } {
      rewrite H0 in H. simpl in H.
      destruct (f' n v idx cd) eqn:?; try easy.
      repeat destruct p. simpl in H. inversion H; subst; clear H.
      apply IHidx in Heqo. omega.
    }
  }
Qed.

Lemma Aligned_PB_IRElm_decode_lt {n} (desc : PB_Message n) numBytes
  : forall (v : Vector.t char numBytes) (idx1 : nat) (c1 c2 : CacheDecode) 
      (elm : PB_IRElm) (idx2 : nat),
    Aligned_PB_IRElm_decode desc numBytes v idx1 c1 = Some (elm, idx2, c2) ->
    idx1 < idx2.
Proof.
  intros.
  eapply DecodeMEquivAlignedDecodeM_lt; eauto.
  - apply Aligned_PB_IRElm_decodeM.
  - intros. unfold Aligned_PB_IRElm_decode.
    unfold Aligned_Varint_decode.
    unfold BindAlignedDecodeM.
    rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
    auto.
  - apply PB_IRElm_decode_lt.
Qed.

Definition Aligned_PB_IR_decode {n} (desc : PB_Message n)
  : nat -> forall {numBytes}, AlignedDecodeM PB_IR numBytes.
Proof.
  refine
    (Fix lt_wf (fun _ => forall {numBytes}, AlignedDecodeM PB_IR numBytes)
         (fun sz decode numBytes =>
              match sz return AlignedDecodeM PB_IR numBytes with
              | O => return nil
              | S sz' =>
                fun v idx1 c1 =>
                  match Aligned_PB_IRElm_decode desc numBytes v idx1 c1 as x
                        return (_ = x -> _) with
                  | Some (elm, idx2, c2) => fun _ =>
                    if lt_dec sz (idx2 - idx1) then
                      None
                    else
                      match decode (sz - (idx2 - idx1)) _ numBytes v idx2 c2 with
                      | Some (ir, idx3, c3) =>
                        Some (elm :: ir, idx3, c3)
                      | None => None
                      end
                  | None => fun _ => None
                  end eq_refl
              end)).
  assert (idx1 < idx2). eapply Aligned_PB_IRElm_decode_lt; eauto.
  abstract omega.
Defined.

Local Arguments Nat.sub : simpl never.
Local Arguments Nat.modulo : simpl never.
(* :TODO: move it to ProtobufSpec.v. *)
Theorem PB_IR_decode_le {n} (desc : PB_Message n) sz
  : forall b cd ir b' cd',
    PB_IR_decode desc sz b cd = Some (ir, b', cd') -> le_B b' b.
Proof.
  unfold PB_IR_decode. unfold le_B.
  induction sz using (well_founded_ind lt_wf). intros.
  rewrite Coq.Init.Wf.Fix_eq in H0 by solve_extensionality.
  destruct sz eqn:?. inversion H0. omega.
  decode_opt_to_inv.
  destruct x0. apply Decode_w_Measure_lt_eq_inv in H0. simpl in H0.
  destruct lt_dec; try easy.
  decode_opt_to_inv. subst.
  simpl in H1.
  unfold lt_B in l. simpl in l.
  apply H in H1. simpl in *. omega.
  omega.
Qed.

(* :TODO: move it somewhere else *)
Lemma ByteString_byte_padding0
  : forall b, bin_measure b mod 8 = 0 ->
         padding b = 0.
Proof.
  simpl bin_measure. unfold length_ByteString.
  intros. rewrite Nat.mul_comm in H. rewrite Nat.mod_add in H by auto.
  destruct b. simpl in *. apply Nat.mod_small in paddingOK.
  intuition.
Qed.

Lemma ByteString_vector_byte
  : forall {n} (v : Vector.t char n),
    bin_measure (build_aligned_ByteString v) mod 8 = 0.
Proof.
  intros.
  simpl. unfold length_ByteString. simpl.
  unfold Nat.add. rewrite Nat.mul_comm. apply Nat.mod_mul. auto.
Qed.

(* :TODO: generalize this. *)
Theorem PB_IRElm_decode_byte {n} (desc : PB_Message n)
  : forall b cd elm b' cd',
    PB_IRElm_decode desc b cd = Some (elm, b', cd') ->
    bin_measure b mod 8 = 0 ->
    bin_measure b' mod 8 = 0.
Proof.
  intros. destruct (PB_IRElm_decode_correct desc)
            with (P := fun _ : CacheDecode => True) as [_ ?].
  compute. intuition.
  simpl in *.
  edestruct H1 as [? [? [? [? [? _]]]]]; eauto.
  apply PB_IRElm_format_byte in H3. clear H1.
  subst. rewrite (@mappend_measure _ ByteStringQueueMonoid) in H0.
  rewrite Nat.add_mod in H0 by auto. rewrite H3 in H0.
  simpl in H0. unfold Nat.add in H0. rewrite Nat.mod_mod in H0 by auto.
  auto.
  Grab Existential Variables.
  auto.
Qed.

Theorem PB_IRElm_decode_byte' {n} (desc : PB_Message n)
  : forall {m} (v : Vector.t char m) cd elm b' cd',
    PB_IRElm_decode desc (build_aligned_ByteString v) cd = Some (elm, b', cd') ->
    bin_measure b' mod 8 = 0.
Proof.
  intros.
  eapply PB_IRElm_decode_byte; eauto.
  apply ByteString_vector_byte.
Qed.

Lemma Aligned_PB_IR_decodeM1 {n} (desc : PB_Message n) sz
  : forall numBytes_hd n (v : Vector.t _ (S numBytes_hd)) cd,
    Aligned_PB_IR_decode desc sz v (S n) cd =
    Ifopt Aligned_PB_IR_decode desc sz (Vector.tl v) n cd as a
    Then Some (fst (fst a), S (snd (fst a)), snd a) Else None.
Proof.
  unfold Aligned_PB_IR_decode.
  induction sz using (well_founded_ind lt_wf); intros.
  destruct (Aligned_PB_IRElm_decodeM desc) as [? _].
  rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
  destruct sz eqn:?; auto.
  repeat match goal with
         | |- context [Aligned_PB_IRElm_decode ?a ?b ?c ?d ?e] =>
           destruct (Aligned_PB_IRElm_decode a b c d e) eqn:?
         end.
  do 2 destruct p; do 2 destruct p0.
  specialize (Aligned_PB_IRElm_decode_lt desc _ _ _ _ _ _ _ Heqo).
  specialize (Aligned_PB_IRElm_decode_lt desc _ _ _ _ _ _ _ Heqo0).
  intros.
  all : rewrite H0, Heqo0 in Heqo; clear Heqo0 H0; try easy.
  inversion Heqo; clear Heqo; subst.
  destruct lt_dec eqn:?; auto.
  rewrite (H (S n1 - (n3 - n0))) by omega.
  destruct Fix eqn:?; try do 2 destruct p0; auto.
Qed.

Lemma Aligned_PB_IR_decodeM {n} (desc : PB_Message n) sz
  : DecodeMEquivAlignedDecodeM
      (PB_IR_decode desc (8*sz)) (fun numBytes => Aligned_PB_IR_decode desc sz).
Proof.
  unfold DecodeMEquivAlignedDecodeM, Aligned_PB_IR_decode.
  induction sz using (well_founded_ind lt_wf).
  split; [| split]; intros.
  - apply (Aligned_PB_IR_decodeM1 desc).
  - eapply (PB_IR_decode_le desc); eauto.
  - unfold PB_IR_decode in *.
    rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
    rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
    destruct sz eqn:?. { 
      assert (n0 - n0 = 0) as L by omega.
      repeat split; try easy;
        inversion H0; subst; clear H0; simpl.
      unfold ReturnAlignedDecodeM. repeat progress f_equal. auto.
      rewrite L. exists (Vector.nil char).
      rewrite <- build_aligned_ByteString_append. auto.
    } {
      simpl.
      destruct (Aligned_PB_IRElm_decodeM desc) as [_ [_ [? ?]]].
      destruct Aligned_PB_IRElm_decode eqn:?;
        destruct (PB_IRElm_decode desc (build_aligned_ByteString v) cd) eqn:?;
        [ |
          apply H0 in Heqo; easy |
          rewrite (proj2 H0) in Heqo; easy |]. {
        do 2 destruct p. do 2 destruct p0.
        rewrite Heqa.
        edestruct (Decode_w_Measure_lt_eq (PB_IRElm_decode desc)); eauto.
        rewrite H2. simpl.
          repeat match goal with
          | |- context [lt_dec ?a ?b] => destruct (lt_dec a b) eqn:?
          end. {
          split; try easy.
        } {
          exfalso.
          unfold lt_B in x. simpl in x.
          edestruct H1; eauto. inversion H3. clear H3.
          unfold length_ByteString in l. simpl in l. omega.
        } {
          exfalso.
          unfold lt_B in x. simpl in x.
          edestruct H1; eauto. inversion H3. clear H3.
          unfold length_ByteString in n3. simpl in n3. 
          apply PB_IRElm_decode_byte' in Heqo.
          apply ByteString_byte_padding0 in Heqo. omega.
        } {
          assert (numBytes b < n0) as L0. {
            apply PB_IRElm_decode_lt in Heqo. unfold lt_B in Heqo.
            simpl in Heqo. unfold length_ByteString in Heqo. 
            simpl in Heqo. omega.
          }
          assert (0 < n2) as L1. {
            eapply Aligned_PB_IRElm_decode_lt; eauto.
          }
          assert (n0 = (n0 - numBytes b) + numBytes b) as L2. {
            omega.
          }
          assert (padding b = 0) as L3. {
            apply PB_IRElm_decode_byte' in Heqo.
            apply ByteString_byte_padding0 in Heqo.
            auto.
          }
          assert (b = build_aligned_ByteString (byteString b)) as L. {
            destruct b. simpl in *.
            destruct front; try easy.
            unfold build_aligned_ByteString.
            repeat progress f_equal.
            apply le_uniqueness_proof.
          }
          destruct (H (S n1 - n2)) as [_ [_ [? ?]]].
          omega.
          repeat match goal with
          | |- context [Fix ?a ?b ?c ?d ?e] => destruct (Fix a b c d e) eqn:?
          end; try do 2 destruct p2; try do 2 destruct p1;
            simpl. {
            split. split; easy.
            intros. inversion H5; clear H5; subst.
            edestruct H1; eauto. inversion H5; clear H5; subst.
            assert (numBytes bs' <= numBytes b) as L4. {
              apply PB_IR_decode_le in Heqo0.
              unfold le_B in Heqo0. simpl in Heqo0.
              unfold length_ByteString in Heqo0.
              omega.
            }
            rewrite L in Heqo0.
            edestruct H4; eauto. simpl.
            match goal with
            | H : Fix _ _ _ ?a1 _ _ = _ |- Fix _ _ _ ?a2 _ _ = _ =>
               replace a2 with a1
            end.
            apply Heqo0. unfold length_ByteString. simpl. omega.
            (* :Q: very slow omega. *)
            destruct H6, H7.
            eapply (proper_consumer_t_Some _ (Aligned_PB_IR_decodeM1 desc _)
                                           (eq_rect _ _ v _ L2))
              in H5.
            unfold Aligned_PB_IR_decode in H5. simpl in H5.
            rewrite <- L2 in H5. simpl in H5.
            rewrite Nat.sub_0_r in Heqa0.
            rewrite Heqa0 in H5. inversion H5; clear H5; subst.
            split.
            - do 3 f_equal. omega.
            - assert (n0 - numBytes b + (numBytes b - numBytes bs') =
                      n0 - numBytes bs') as L5. {
                omega.
              }
              exists (eq_rect _ _ (Vector.append x0 x1) _ L5).
              rewrite <- L5. simpl. rewrite build_aligned_ByteString_append.
              rewrite H6. rewrite <- (@mappend_assoc _ ByteStringQueueMonoid).
              simpl. rewrite <- H7. rewrite <- L. auto.
            - rewrite <- L2. simpl. instantiate (1 := x0).
              pose proof H6. apply build_aligned_ByteString_split' in H8.
              destruct H8. rewrite H6. rewrite L at 2.
              rewrite build_aligned_ByteString_append. auto.
          } {
            exfalso.
          }
        }
      } {
      }
    }


Lemma Aligned_PB_Message_M' {n} (desc : PB_Message n)
  : {impl : _ | DecodeMEquivAlignedDecodeM (PB_Message_decode desc) impl}.
Proof.
  eexists; intros.
  unfold PB_Message_decode.
  apply Bind_DecodeMEquivAlignedDecodeM.
  (* { *)
  (*   admit. *)
  (* } { *)
  Focus 2.
    intros.
    match goal with
    | |- _ (fun b c => @?p b c) _ => idtac p
    end.
    (* :TODO: trans *)
    let f := constr:
             (fun cd =>
                match PB_Message_IR_decode desc (rev a) cd with
                | Some (msg, _, cd') => Some (msg, cd')
                | None => None
                end)
    in
    let g := constr:(fun (b : ByteString) c => `(a, cd') <- f c; Some (a, b, cd')) in
    match goal with
    | |- _ ?a _ => replace a with g
    end.
    apply Compose_DecodeMEquivAlignedDecodeM.
    solve_by_extensionality. destruct PB_Message_IR_decode; eauto.
    repeat destruct p; eauto.
  }
Qed.