Require Import
        Coq.Lists.List
        Coq.omega.Omega.

Require Import
        Fiat.CommonEx
        Fiat.Common.Frame
        Fiat.Computation.FixComp
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.Formats.FixListOpt
        Fiat.Narcissus.Common.Notations
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt.

Import FixComp.LeastFixedPointFun.

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
  Variable A_format_sz_eq : forall x b1 b2 ce1 ce1' ce2 ce2',
      A_format x ce1 ↝ (b1, ce1') ->
      A_format x ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
  Variable A_format_byte : forall d b ce ce', A_format d ce ↝ (b, ce') -> bin_measure b mod 8 = 0.
  Variable A_format_some : forall d b ce ce', A_format d ce ↝ (b, ce') -> 0 < bin_measure b.
  (* Could be le. *)
  Variable A_decode_lt : forall b cd x b' cd', A_decode b cd = Some (x, b', cd') -> lt_B b' b.

  Definition SizedList_format_body
             (format : funType [list A; CacheFormat] (B * CacheFormat))
    : funType [list A; CacheFormat] (B * CacheFormat) :=
    fun xs ce =>
      match xs with
      | nil => ret (mempty, ce)
      | x :: xs' =>
        `(b1, ce1) <- A_format x ce;
          `(b2, ce2) <- format xs' ce1;
          ret (mappend b1 b2, ce2)
      end%comp.
  Arguments SizedList_format_body /.

  Definition SizedList_format : FormatM (list A) B :=
    LeastFixedPoint SizedList_format_body.

  Definition SizedList_decode_body
             (decode : nat -> DecodeM (list A) B)
    : nat -> DecodeM (list A) B :=
    fun sz b cd =>
      match sz with
      | O => Some (nil, b, cd)
      | _ =>
        `(x, b1, cd1) <- A_decode b cd;
          if lt_dec sz (bin_measure b - bin_measure b1) then
            None
          else
            `(xs, b2, cd2) <- decode (sz - (bin_measure b - bin_measure b1)) b1 cd1;
          Some (x :: xs, b2, cd2)
      end.
  Arguments SizedList_decode_body /.

  Definition SizedList_decode : nat -> DecodeM (list A) B :=
    FueledFixP SizedList_decode_body.

  Lemma SizedList_format_body_monotone:
    monotonic_function SizedList_format_body.
  Proof.
    unfold monotonic_function. simpl. intros.
    destruct t. reflexivity.
    apply SetoidMorphisms.refine_bind. reflexivity.
    intro.
    apply SetoidMorphisms.refine_bind. apply H.
    intro. reflexivity.
  Qed.

  Lemma SizedList_format_eq_format_list
    : forall xs ce,
      refineEquiv (SizedList_format xs ce) (format_list A_format xs ce).
  Proof.
    clear. unfold refineEquiv, refine.
    induction xs; intros; split; intros; destruct v.
    - apply (unroll_LeastFixedPoint' SizedList_format_body_monotone).
      eauto.
    - apply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H.
      eauto.
    - apply (unroll_LeastFixedPoint' SizedList_format_body_monotone).
      simpl in *. computes_to_inv2.
      eapply IHxs in H'.
      computes_to_econstructor; eauto.
    - apply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H.
      simpl in *. computes_to_inv2.
      eapply IHxs in H'.
      computes_to_econstructor; eauto.
  Qed.

  Theorem SizedList_decode_le
    : forall sz b cd xs b' cd',
      SizedList_decode sz b cd = Some (xs, b', cd') -> le_B b' b.
  Proof.
    unfold SizedList_decode.
    unfold FueledFixP. intros ? ?. generalize (S (bin_measure b)). intro. revert sz b.
    induction n; intros. easy.
    simpl in H.
    destruct sz. injections. unfold le_B. easy.
    decode_opt_to_inv. destruct lt_dec. easy.
    decode_opt_to_inv. subst. apply IHn in H0.
    apply A_decode_lt in H.
    unfold lt_B, le_B in *.
    omega.
  Qed.

  Theorem SizedList_format_sz_eq'
    : forall xs,
      (forall x, In x xs ->
          forall b1 b2 ce1 ce1' ce2 ce2',
          A_format x ce1 ↝ (b1, ce1') ->
          A_format x ce2 ↝ (b2, ce2') ->
          bin_measure b1 = bin_measure b2) ->
      forall b1 b2 ce1 ce1' ce2 ce2',
        SizedList_format xs ce1 ↝ (b1, ce1') ->
        SizedList_format xs ce2 ↝ (b2, ce2') ->
        bin_measure b1 = bin_measure b2.
  Proof.
    clear.
    unfold SizedList_format.
    induction xs; intros;
      apply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H0;
      apply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H1.
    - inversion H0. inversion H1. auto.
    - simpl in H0, H1. computes_to_inv2.
      rewrite !mappend_measure.
      f_equal. eapply H; eauto. intuition.
      eapply IHxs; eauto. intros. eapply H; eauto.
      intuition.
  Qed.

  Theorem SizedList_format_sz_eq
    : forall xs b1 b2 ce1 ce1' ce2 ce2',
      SizedList_format xs ce1 ↝ (b1, ce1') ->
      SizedList_format xs ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
  Proof.
    intros. eapply SizedList_format_sz_eq'; eauto.
  Qed.

  Theorem SizedList_format_byte'
    : forall xs,
      (forall x, In x xs ->
            forall b ce ce',
              A_format x ce ↝ (b, ce') -> bin_measure b mod 8 = 0) ->
      forall b ce ce',
        SizedList_format xs ce ↝ (b, ce') ->
        bin_measure b mod 8 = 0.
  Proof.
    clear.
    unfold SizedList_format.
    induction xs; intros;
      apply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H0.
    - inversion H0. rewrite mempty_measure_0. auto.
    - simpl in H0. computes_to_inv2. rewrite mappend_measure.
      rewrite <- Nat.add_mod_idemp_r; auto.
      rewrite <- Nat.add_mod_idemp_l; auto.
      erewrite H; eauto.
      erewrite IHxs; eauto. intros. eapply H; eauto.
      all : intuition.
  Qed.

  Theorem SizedList_format_byte
    : forall xs b ce ce',
      SizedList_format xs ce ↝ (b, ce') ->
      bin_measure b mod 8 = 0.
  Proof.
    intros. eapply SizedList_format_byte'; eauto.
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

  Definition SizedList_predicate sz xs : Prop :=
    (forall b ce ce', SizedList_format xs ce ↝ (b, ce') -> bin_measure b = sz) /\
    forall x, In x xs -> A_predicate x.

  Local Arguments Nat.add : simpl never.
  Local Arguments Nat.sub : simpl never.

  Theorem SizedList_decode_correct'
          (m : nat)
          (A_decode_correct : forall b',
              bin_measure b' < m ->
              CorrectDecoder' monoid A_predicate A_predicate_rest A_format A_decode A_cache_inv b')
    : forall sz b',
      bin_measure b' < m ->
      CorrectDecoder'
        monoid
        (SizedList_predicate sz)
        SizedList_predicate_rest
        SizedList_format (SizedList_decode sz) A_cache_inv b'.
  Proof.
    unfold SizedList_format, SizedList_decode, SizedList_format_body, SizedList_decode_body.
    eapply fix_format_correctP2; eauto. apply SizedList_format_body_monotone.
    instantiate (1:=fun _ => True). reflexivity.
    unfold SizedList_predicate, SizedList_format, SizedList_format_body in *.
    intros ? ? ? ? HPb.
    split; intros. {
      destruct data. {
        destruct_many.
        assert (bin_measure b = c). {
          eapply H3.
          eapply (unroll_LeastFixedPoint' SizedList_format_body_monotone).
          simpl. eauto.
        }
        inversion H5; clear H5; subst.
        rewrite mempty_measure_0.
        eexists. intuition eauto. repeat f_equal. apply mempty_left.
      } {
        destruct_many. 
        assert (bin_measure b = c). {
          eapply H3.
          eapply (unroll_LeastFixedPoint' SizedList_format_body_monotone).
          simpl. eauto.
        }
        clear H3.
        computes_to_inv2.
        rewrite mappend_measure in HPb.
        rewrite mappend_measure in H1.
        pose proof H5. apply A_format_some in H3.
        assert (0 < bin_measure (mappend b1 b0)). {
          rewrite mappend_measure. omega.
        }
        destruct (bin_measure (mappend b1 b0)) eqn:?. easy.
        pose proof H5. eapply A_decode_correct in H5; eauto.
        destruct_many. rewrite <- mappend_assoc. rewrite H5.
        simpl. rewrite <- Heqn0 in *.
        destruct lt_dec.
        exfalso. rewrite !mappend_measure in l. omega.
        rewrite !mappend_measure.
        match goal with
        | _ : _ |- context [FueledFixP' _ _ ?a _ _] =>
          replace a with (bin_measure b0) by omega
        end.
        eapply H0 in H5'; eauto. destruct_many.
        rewrite H11. simpl. eexists. intuition.
        omega. omega.
        split. intros. eapply SizedList_format_sz_eq; eauto.
        intros. apply H6. intuition. apply H4. omega. apply H6. intuition.
        eapply H4. eauto.
      }
    } {
      destruct c. {
        injections. split; auto.
        exists mempty, env. repeat split; intros; auto.
        - symmetry. apply mempty_left.
        - eapply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H4.
          inversion H4. apply mempty_measure_0.
        - inversion H4.
      } {
        decode_opt_to_inv.
        eapply A_decode_correct in H4; eauto. destruct_many.
        destruct lt_dec; try congruence.
        decode_opt_to_inv. subst.
        rewrite mappend_measure in HPb.
        eapply H0 in H5; eauto. destruct_many.
        split; eauto. eexists _, _. repeat split; eauto.
        - computes_to_econstructor; eauto.
          computes_to_econstructor; eauto.
        - simpl. rewrite <- mappend_assoc. subst. auto.
        - intros. eapply (unroll_LeastFixedPoint SizedList_format_body_monotone) in H14.
          simpl in H14. computes_to_inv2.
          specialize (H11 _ _ _ H14'). rewrite !mappend_measure in *.
          assert (bin_measure b1 = bin_measure x2). {
            eapply A_format_sz_eq; eauto.
          } omega.
        - destruct 1; subst; auto.
        - omega.
        - rewrite mappend_measure in H1.
          apply A_format_some in H6. omega.
      }
    }

    intros. destruct c; eauto.
    decode_opt_to_inv. rewrite H0. simpl.
    destruct lt_dec; eauto.
    decode_opt_to_inv. erewrite H; eauto.
    simpl. auto.
  Qed.

  Theorem SizedList_decode_correct
          (A_decode_correct : CorrectDecoder monoid A_predicate A_predicate_rest A_format A_decode A_cache_inv)
    : forall sz,
      CorrectDecoder
        monoid
        (SizedList_predicate sz)
        SizedList_predicate_rest
        SizedList_format (SizedList_decode sz) A_cache_inv.
  Proof.
    intros. intro. eapply SizedList_decode_correct'; eauto.
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