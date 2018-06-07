Require Import
        Coq.Lists.List
        Coq.omega.Omega.

Require Import
        Fiat.CommonEx
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt.

Section SizedList.
  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.

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

  Variable Wf_bound : B.
  Variable Wf_decode : forall b, lt_B b Wf_bound -> CacheDecode -> option (A * B * CacheDecode).
  Variable Wf_decode_lt : forall b pf cd x b' cd', Wf_decode b pf cd = Some (x, b', cd') -> lt_B b' b.
  Variable Wf_decode_correct : CorrectDecoderWf monoid A_predicate A_predicate_rest A_format Wf_decode A_cache_inv.

  Definition SizedList_format : FormatM (list A) B :=
    fix format xs ce :=
      match xs with
      | nil => ret (mempty, ce)
      | x :: xs' =>
        `(b1, ce1) <- A_format x ce;
          `(b2, ce2) <- format xs' ce1;
          ret (mappend b1 b2, ce2)
      end%comp.

  Definition SizedList_decode : nat -> DecodeM (list A) B.
  Proof.
    refine
      (Fix lt_wf _
           (fun sz decode b cd =>
              match sz with
              | O => Some (nil, b, cd)
              | _ =>
                `(x, b1, cd1) <- Decode_w_Measure_lt A_decode b cd A_decode_lt;
                if lt_dec sz (bin_measure b - bin_measure (proj1_sig b1)) then
                  None
                else
                  `(xs, b2, cd2) <- decode (sz - (bin_measure b - bin_measure (proj1_sig b1))) _ (proj1_sig b1) cd1;
                Some (x :: xs, b2, cd2)
              end)).
    abstract (destruct b1; unfold lt_B in *; simpl in *; omega).
  Defined.

  Definition Decode_w_Measure_lt_wf
             (b : B)
             (pf : lt_B b Wf_bound)
             (cd : CacheDecode)
    : option (A * {b' : B | lt_B b' b} * CacheDecode).
    generalize (Wf_decode_lt b pf cd); clear.
    destruct (Wf_decode b pf cd) as [ [ [ a b' ] cd' ] | ]; intros;
      [ refine (Some (a, exist _ b' (H _ _ _ eq_refl), cd'))
      | exact None ].
  Defined.

  Lemma Decode_w_Measure_lt_eq_wf
        (b : B)
        (pf : lt_B b Wf_bound)
        (cd : CacheDecode)
    : forall a' b' cd',
      Wf_decode b pf cd = Some (a', b', cd')
      -> exists pf',
        Decode_w_Measure_lt_wf b pf cd =
        Some (a', exist _ b' pf', cd').
  Proof.
    clear; intros; unfold Decode_w_Measure_lt_wf.
    remember (Wf_decode_lt b pf cd); clear Heql.
    destruct (Wf_decode b pf cd) as [ [ [? ?] ? ] | ].
    injections; eauto.
    discriminate.
  Qed.

  Lemma Decode_w_Measure_lt_eq_inv_wf
        (b : B)
        (pf : lt_B b Wf_bound)
        (cd : CacheDecode)
    : forall (a' : A) (cd' : CacheDecode)
        pf',
      Decode_w_Measure_lt_wf b pf cd = Some (a', pf', cd')
      -> Wf_decode b pf cd = Some (a', `pf' , cd').
  Proof.
    unfold Decode_w_Measure_lt_wf; intros.
    revert pf' H.
    generalize (Wf_decode_lt b pf cd).
    destruct (Wf_decode b pf cd) as [ [ [? ?] ?] | ]; simpl; intros;
      try discriminate.
    injections; reflexivity.
  Qed.

  Definition SizedListWf_decode : nat -> forall b, lt_B b Wf_bound -> CacheDecode -> option (list A * B * CacheDecode).
  Proof.
    refine
      (Fix lt_wf _
           (fun sz decode b pf cd =>
              match sz with
              | O => Some (nil, b, cd)
              | _ =>
                `(x, b1, cd1) <- Decode_w_Measure_lt_wf b _ cd;
                if lt_dec sz (bin_measure b - bin_measure (proj1_sig b1)) then
                  None
                else
                  `(xs, b2, cd2) <- decode (sz - (bin_measure b - bin_measure (proj1_sig b1))) _ (proj1_sig b1) _ cd1;
                Some (x :: xs, b2, cd2)
              end)).
    abstract assumption.
    abstract (destruct b1; unfold lt_B in *; simpl in *; omega).
    abstract (destruct b1; unfold lt_B in *; simpl in *; omega).
  Defined.

  Theorem SizedList_decode_le
    : forall sz b cd xs b' cd',
      SizedList_decode sz b cd = Some (xs, b', cd') -> le_B b' b.
  Proof.
    unfold SizedList_decode.
    induction sz using (well_founded_ind lt_wf); intros.
    rewrite Coq.Init.Wf.Fix_eq in H0 by solve_extensionality.
    destruct sz. injections. unfold le_B. easy.
    decode_opt_to_inv. destruct lt_dec. easy.
    decode_opt_to_inv. subst. destruct x0.
    remember (S sz) as sz'.
    unfold lt_B, le_B in *.
    apply H in H1; clear H;
      simpl in *; omega.
  Qed.

  Theorem SizedListWf_decode_le
    : forall sz b pf cd xs b' cd',
      SizedListWf_decode sz b pf cd = Some (xs, b', cd') -> le_B b' b.
  Proof.
    unfold SizedListWf_decode.
    induction sz using (well_founded_ind lt_wf); intros.
    rewrite Coq.Init.Wf.Fix_eq in H0 by solve_extensionality.
    destruct sz. injections. unfold le_B. easy.
    decode_opt_to_inv. destruct lt_dec. easy.
    decode_opt_to_inv. subst. destruct x0.
    remember (S sz) as sz'.
    unfold lt_B, le_B in *.
    apply H in H1; clear H;
      simpl in *; omega.
  Qed.

  Theorem SizedList_format_sz_eq
    : forall xs b1 b2 ce1 ce1' ce2 ce2',
      SizedList_format xs ce1 ↝ (b1, ce1') ->
      SizedList_format xs ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
  Proof.
    unfold SizedList_format. induction xs; intros.
    - inversion H. inversion H0. auto.
    - computes_to_inv2.
      rewrite !mappend_measure.
      erewrite A_format_sz_eq; eauto.
  Qed.

  Theorem SizedList_format_byte
    : forall xs b ce ce',
      SizedList_format xs ce ↝ (b, ce') ->
      bin_measure b mod 8 = 0.
  Proof.
    induction xs; intros.
    - inversion H. rewrite mempty_measure_0. auto.
    - simpl in H. computes_to_inv2. rewrite mappend_measure.
      rewrite <- Nat.add_mod_idemp_r; auto.
      rewrite <- Nat.add_mod_idemp_l; auto.
      erewrite A_format_byte; eauto.
      erewrite IHxs; eauto.
  Qed.

  Fixpoint SizedList_predicate_rest (xs : list A) (b : B) : Prop :=
    match xs with
    | nil => True
    | x :: xs' =>
      (forall b' ce ce',
          SizedList_format xs' ce ↝ (b', ce') ->
          A_predicate_rest x (mappend b' b))
      /\ SizedList_predicate_rest xs' b
    end.

  Theorem SizedList_decode_correct
    : forall sz,
      CorrectDecoder
        monoid
        (fun xs =>
           (forall b ce ce', SizedList_format xs ce ↝ (b, ce') -> bin_measure b = sz) /\
           forall x, In x xs -> A_predicate x)
        SizedList_predicate_rest
        SizedList_format (SizedList_decode sz) A_cache_inv.
  Proof.
    unfold SizedList_format, SizedList_decode.
    split; intros. {
      generalize dependent sz.
      generalize dependent env.
      generalize dependent env'.
      generalize dependent xenv.
      generalize dependent ext.
      generalize dependent bin.
      induction data; intros. {
        eexists.
        destruct H0 as [H3 H4]. specialize (H3 _ _ _ H2).
        inversion H2. clear H2. subst.
        repeat split; eauto.
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
        rewrite mempty_measure_0.
        repeat progress f_equal. rewrite mempty_left. auto.
      } {
        destruct H0 as [H3 H4]. specialize (H3 _ _ _ H2).
        computes_to_inv2.
        destruct A_decode_correct as [He _].
        simpl in H1. destruct H1. specialize (H0 _ _ _ H2').
        edestruct He with (ext:=mappend b ext) as [? [? [? ?]]]; eauto.
        apply H4. intuition.
        rewrite mappend_measure.
        edestruct IHdata with (ext:=ext) as [? [? [? ?]]]; intros; eauto.
        split. intros. eapply SizedList_format_sz_eq; eauto.
        intros. apply H4. intuition. clear IHdata.
        eexists; intuition; eauto.
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality; simpl.
        match goal with
        | _ : _ |- context [match ?a with _ => _ end] => destruct a eqn:?
        end.
        apply A_decode_lt in H3.
        match goal with
        | H : lt_B _ _ |- _ => unfold lt_B in H; repeat rewrite @mappend_measure in H; simpl in H
        end; omega.
        edestruct @Decode_w_Measure_lt_eq with (A_decode_lt:=A_decode_lt); eauto.
        revert x1 H10. rewrite mappend_assoc. intros.
        rewrite H10. simpl. clear x1 H10. destruct lt_dec.
        rewrite !mappend_measure in l. omega.
        rewrite !mappend_measure.
        match goal with
        | _ : _ |- context [Fix _ _ _ ?a _ _] => 
          replace a with (bin_measure b)
        end. simpl in H7. rewrite H7. auto.
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
        exists mempty, env. repeat split; intros; auto.
        - symmetry. apply mempty_left.
        - inversion H1. apply mempty_measure_0.
        - inversion H1.
      } {
        decode_opt_to_inv.
        destruct x0. simpl proj1_sig in H3. simpl proj2_sig in H3.
        apply Decode_w_Measure_lt_eq_inv in H1. simpl in H1.
        destruct A_decode_correct as [_ Hd]; auto.
        edestruct Hd as [? [? [? [? [? [? ?]]]]]]; eauto. clear Hd.
        destruct lt_dec; try congruence.
        decode_opt_to_inv. subst.
        edestruct H; try apply H3; eauto. unfold lt_B in l. omega.
        destruct H9 as [? [? [? [? [[? ?] ?]]]]].
        split; eauto. eexists _, _. repeat split.
        - computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
        - simpl. rewrite <- mappend_assoc. subst. auto.
        - intros. computes_to_inv2.
          specialize (H11 _ _ _ H14'). rewrite !mappend_measure in *.
          assert (bin_measure b1 = bin_measure x2). {
            eapply A_format_sz_eq; eauto.
          } omega.
        - destruct 1; subst; auto.
        - auto.
      }
    }
  Qed.

  Theorem SizedListWf_decode_correct
    : forall sz,
      CorrectDecoderWf
        monoid
        (fun xs =>
           (forall b ce ce', SizedList_format xs ce ↝ (b, ce') -> bin_measure b = sz) /\
           forall x, In x xs -> A_predicate x)
        SizedList_predicate_rest
        SizedList_format (SizedListWf_decode sz) A_cache_inv.
  Proof.
    unfold SizedList_format, SizedListWf_decode.
    split; intros. {
      generalize dependent sz.
      generalize dependent env.
      generalize dependent env'.
      generalize dependent xenv.
      generalize dependent ext.
      generalize dependent bin.
      induction data; intros. {
        eexists.
        destruct H0 as [H3 H4]. specialize (H3 _ _ _ H2).
        inversion H2. clear H2. subst.
        repeat split; eauto.
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality.
        rewrite mempty_measure_0.
        repeat progress f_equal. rewrite mempty_left. auto.
      } {
        destruct H0 as [H3 H4]. specialize (H3 _ _ _ H2).
        computes_to_inv2. revert pf. rewrite <- mappend_assoc. intros.
        assert (lt_B (mappend b ext) Wf_bound) as pf'. {
          unfold lt_B in *. rewrite !mappend_measure in pf. rewrite mappend_measure. omega.
        }
        destruct Wf_decode_correct as [He _].
        simpl in H1. destruct H1. specialize (H0 _ _ _ H2').
        edestruct He with (ext:=mappend b ext) (pf := pf); eauto.
        apply H4. intuition. destruct_many.
        rewrite mappend_measure.
        edestruct IHdata with (ext:=ext) (pf:=pf'); intros; eauto.
        split. intros. eapply SizedList_format_sz_eq; eauto.
        intros. apply H4. intuition. clear IHdata.
        eexists; intuition; eauto.
        rewrite Coq.Init.Wf.Fix_eq by solve_extensionality; simpl.
        match goal with
        | _ : _ |- context [match ?a with _ => _ end] => destruct a eqn:?
        end.
        apply Wf_decode_lt in H3.
        unfold lt_B in *.
        repeat match goal with
               | H : context [bin_measure (mappend _ _)] |- _ => rewrite !mappend_measure in H
               end; omega.
        edestruct @Decode_w_Measure_lt_eq_wf; eauto.
        simpl in *.
        match goal with
        | |- context [Decode_w_Measure_lt_wf _ ?a _] => replace a with pf in * by apply le_uniqueness_proof
        end. rewrite H9. simpl. clear H9. destruct lt_dec.
        repeat match goal with
               | H : context [bin_measure (mappend _ _)] |- _ => rewrite !mappend_measure in H
               end; omega.
        match goal with
        | _ : _ |- context [Fix _ _ _ ?a _ _ _] =>
          replace a with (bin_measure b)
        end. simpl in H8.
        match goal with
        | H : context [Fix _ _ _ _ _ ?p _]
          |- context [Fix _ _ _ _ _ ?p' _] =>
          replace p' with p by apply le_uniqueness_proof
        end.
        rewrite H8. auto.
        unfold lt_B in *. rewrite !mappend_measure in *.
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
        exists mempty, env. repeat split; intros; auto.
        - symmetry. apply mempty_left.
        - inversion H1. apply mempty_measure_0.
        - inversion H1.
      } {
        decode_opt_to_inv.
        destruct x0. simpl proj1_sig in H3. simpl proj2_sig in H3.
        apply Decode_w_Measure_lt_eq_inv_wf in H1. simpl in H1.
        destruct Wf_decode_correct as [_ Hd]; auto.
        edestruct Hd; eauto. clear Hd. destruct_many.
        destruct lt_dec; try congruence.
        decode_opt_to_inv. subst.
        edestruct H; try apply H3; eauto. unfold lt_B in l. omega.
        destruct_many.
        split; eauto. eexists _, _. repeat split.
        - computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
        - simpl. rewrite <- mappend_assoc. subst. auto.
        - intros. computes_to_inv2.
          specialize (H11 _ _ _ H14').
          clear H3.
          repeat match goal with
                 | H : context [bin_measure (mappend _ _)] |- _ => rewrite !mappend_measure in H
                 end. rewrite !mappend_measure.
          assert (bin_measure b1 = bin_measure x2). {
            eapply A_format_sz_eq; eauto.
          } omega.
        - destruct 1; subst; auto.
        - auto.
      }
    }
  Qed.

End SizedList.

Lemma SizedList_predicate_rest_True {A B}
      {cache : Cache}
      {monoid : Monoid B}
      (A_format : FormatM A B)
  : forall (xs : list A) (b : B),
    SizedList_predicate_rest (fun a b => True) A_format xs b.
Proof.
  induction xs; simpl; eauto.
Qed.