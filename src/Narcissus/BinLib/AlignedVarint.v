Require Import
        Coq.Vectors.Vector
        Coq.omega.Omega.

Require Import
        Coq.Logic.Eqdep_dec
        Fiat.CommonEx
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
        Fiat.Narcissus.BinLib.AlignWord.

Section AlignedVarint.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.

  Local Open Scope AlignedDecodeM_scope.
  Local Open Scope N.

  (* :TODO: <+- -> bitwise operations *)

  Lemma nth_opt_lt {A : Set} {n} (v : Vector.t A n) m (a : A)
    : nth_opt v m = Some a -> (m < n)%nat.
  Proof.
    generalize dependent n.
    induction m; intros; destruct v; inversion H.
    omega. apply lt_n_S. eapply IHm. eauto.
  Qed.

  Lemma GetCurrentByte_lt {n} (v : Vector.t char n) idx idx' w cd cd'
    : GetCurrentByte v idx cd = Some (w, idx', cd') -> (idx < idx' <= n)%nat.
  Proof.
    unfold GetCurrentByte. intros.
    destruct nth_opt eqn:?; simpl in H; try easy.
    inversion H. pose proof (nth_opt_lt _ _ _ Heqo). omega.
  Qed.

  Definition Aligned_Varint_decode
             {n : nat}
    : AlignedDecodeM N n.
  Proof.
    refine
      (fun v =>
         Fix (Nat.gt_wf n) _
             (fun idx decode cd =>
                match GetCurrentByte v idx cd as x
                      return _ = x -> _ with
                | Some (w, idx1, cd1) =>
                  fun _ =>
                    let r' := wordToN w in
                    if r' <? (2^7) then
                      Some (r', idx1, cd1)
                    else
                      let r := r' - (2^7) in
                      match decode idx1 _ cd1 with
                      | Some (q, idx2, cd2) =>
                        match q with
                        | N0 => None
                        | _ => Some ((2^7) * q + r, idx2, cd2)
                        end
                      | None => None
                      end
                | None => fun _ => None
                end eq_refl)).
    eapply GetCurrentByte_lt; eauto.
  Defined.

  Lemma Aligned_Varint_decodeM1
    : forall numBytes_hd n (v : Vector.t _ (S numBytes_hd)) cd,
      Aligned_Varint_decode v (S n) cd =
      Ifopt Aligned_Varint_decode (Vector.tl v) n cd as a
      Then Some (fst (fst a), S (snd (fst a)), snd a) Else None.
  Proof.
    intros.
    unfold Aligned_Varint_decode.
    generalize dependent numBytes_hd; eapply Vector.caseS; simpl; intros.
    generalize dependent cd.
    induction n using (well_founded_ind (Nat.gt_wf n0)); intros.
    rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
    rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
    unfold GetCurrentByte; simpl.
    destruct nth_opt eqn:?; simpl; eauto. destruct wordToN; eauto.
    destruct N.ltb; eauto.
    unfold GetCurrentByte in H; simpl in H.
    rewrite H. destruct Fix; eauto. repeat destruct p0. destruct n1; eauto.
    pose proof (nth_opt_lt _ _ _ Heqo). omega.
  Qed.

  Local Arguments N.add : simpl never.
  Local Arguments N.mul : simpl never.
  Local Arguments Nat.sub : simpl never.
  Lemma Aligned_Varint_decodeM
    : DecodeMEquivAlignedDecodeM
        Varint_decode (fun numBytes => Aligned_Varint_decode).
  Proof.
    unfold DecodeMEquivAlignedDecodeM.
    split; [| split]; intros.
    - apply Aligned_Varint_decodeM1.
    - apply Varint_decode_lt in H. unfold lt_B in H. simpl in H.
      omega.
    - unfold Varint_decode.
      unfold Aligned_Varint_decode.
      generalize dependent cd.
      induction v; intros. {
        split. {
          rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
          rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
          simpl. intuition.
        } {
          rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
          rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
          simpl. intros. easy.
        }
      } {
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
        destruct AlignedDecodeCharM as [_ [_ [? ?]]].
        destruct Decode_w_Measure_lt eqn:?. Focus 2.
        apply Decode_w_Measure_lt_eq'' in Heqo.
        apply H in Heqo. rewrite Heqo. simpl. intuition; easy.
        repeat destruct p. destruct s.
        apply Decode_w_Measure_lt_eq_inv in Heqo.
        simpl in Heqo. simpl.
        destruct (H0 _ _ _ Heqo). inversion H1. subst.
        rewrite <- H5 in H2.
        destruct N.ltb eqn:?. {
          split; try easy.
          intros. inversion H3. subst. rewrite <- H5. auto.
        } {
          edestruct IHv.
          pose proof Aligned_Varint_decodeM1. unfold Aligned_Varint_decode in H6.
          rewrite H6. simpl.
          unfold decode_word in Heqo.
          destruct decode_word' eqn:?; try easy.
          simpl in Heqo. destruct p.
          rewrite aligned_decode_char_eq in Heqo0.
          inversion Heqo0. inversion Heqo. subst.
          match goal with
          | |- context [Fix ?a ?b ?c ?d ?e] => destruct (Fix a b c d e) eqn:?
          end; simpl in *. {
            repeat destruct p.
            assert (numBytes b <= n)%nat as L. {
              specialize (Varint_decode_lt _ _ _ _ _ Heqo1).
              unfold lt_B. simpl. unfold length_ByteString.
              simpl. omega.
            }
            apply H4 in Heqo1. destruct Heqo1.
            rewrite H7. destruct n0 eqn:?; simpl; split; try easy.
            intros. inversion H9. subst. split.
            - repeat progress f_equal. omega.
            - destruct H8.
              rewrite build_aligned_ByteString_cons.
              simpl. rewrite H8.
              rewrite (@mappend_assoc _ ByteStringQueueMonoid). simpl.
              rewrite <- build_aligned_ByteString_append. simpl.
              assert (S n - numBytes bs' = S (n - numBytes bs'))%nat.
              omega. rewrite H11.
              eexists. reflexivity.
          } {
            apply H3 in Heqo1. rewrite Heqo1. simpl.
            split; try easy.
          }
        }
      }
  Qed.

End AlignedVarint.