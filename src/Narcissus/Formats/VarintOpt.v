Require Import
        Coq.Init.Wf
        Coq.ZArith.BinInt
        Coq.omega.Omega
        Fiat.Common
        Fiat.CommonEx
        Fiat.Common.Frame
        Fiat.Computation.Core
        Fiat.Computation.Notations
        Fiat.Computation.FixComp
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.WordFacts
        Fiat.Narcissus.Common.ComposeOpt
        Fiat.Narcissus.Formats.WordOpt
        Fiat.Narcissus.Formats.InternetChecksum.

Require Import NArith NArithRing.
Import FixComp.LeastFixedPointFun.

Local Open Scope N.
Local Open Scope comp_scope.

(* Lemmas for N arithmetic. *)
Lemma div_eucl_mod
  : forall a b q r, N.div_eucl a b = (q, r) -> r = a mod b.
Proof.
  intros.
  unfold N.modulo. rewrite H. auto.
Qed.

Lemma div_eucl_div
  : forall a b q r, N.div_eucl a b = (q, r) -> q = a / b.
Proof.
  intros.
  unfold N.div. rewrite H. auto.
Qed.

Lemma div_quotient_0
  : forall a x b, a <> 0 -> (a * x + b) / a = 0 -> x = 0.
Proof.
  intros.
  apply N.div_small_iff in H0; auto.
  apply N.le_lt_trans with (n:=a * x) in H0. 2 : apply N.le_add_r.
  rewrite N.mul_comm in H0.
  unfold N.lt in H0.
  rewrite N2Nat.inj_compare in H0.
  apply Nat.compare_lt_iff in H0.
  rewrite N2Nat.inj_mul in H0.
  apply N2Nat.inj.
  revert H0. generalize (N.to_nat a). generalize (N.to_nat x). simpl.
  clear. intros.
  destruct n. eauto. simpl in H0.
  exfalso. apply le_not_lt in H0. apply H0. clear.
  apply le_lt_n_Sm.
  apply Nat.le_add_r.
Qed.

Lemma div_quotient_eq
  : forall a x b, a <> 0 -> b < a -> (a * x + b) / a = x.
Proof.
  intros.
  Admitted.

Lemma div_eucl_mod_lt
  : forall a b q r, b <> 0 -> N.div_eucl a b = (q, r) -> r < b.
Proof.
  intros.
  apply div_eucl_mod in H0. subst.
  apply N.mod_lt. easy.
Qed.
Hint Resolve div_eucl_mod_lt.

Lemma div_eucl_div_lt
  : forall a b q r, 0 < a -> 1 < b -> N.div_eucl a b = (q, r) -> q < a.
Proof.
  intros.
  apply div_eucl_div in H1. subst.
  apply N.div_lt; easy.
Qed.
Hint Resolve div_eucl_div_lt.

Lemma Npow2_N
  : forall e, 2^(N.of_nat e) = Npow2 e.
Proof.
  induction e.
  - auto.
  - unfold Npow2. fold Npow2.
    rewrite Nat2N.inj_succ. rewrite N.pow_succ_r'.
    rewrite IHe. auto.
Qed.

Lemma div_eucl_mod_lt_sz
  : forall a sz q r, N.div_eucl a (2^(N.of_nat sz)) = (q, r) ->
                r < Npow2 sz.
Proof.
  intros. rewrite <- Npow2_N.
  apply div_eucl_mod_lt with (a := a) (q := q); auto.
  apply N.pow_nonzero. easy.
Qed.
Hint Resolve div_eucl_mod_lt_sz.

Lemma div_eucl_mod_lt_sz'
  : forall a sz q r, N.div_eucl a (2^(N.of_nat sz)) = (q, r) ->
                r < Npow2 (S sz).
Proof.
  intros. unfold Npow2. fold Npow2.
  apply N.lt_trans with (m := Npow2 sz). eauto.
  rewrite <- Npow2_N.
  apply N_lt_double.
  apply N.le_succ_l.
  replace (N.succ 0) with (2^0) by auto.
  apply N.pow_le_mono_r. easy.
  apply N.le_0_l.
Qed.
Hint Resolve div_eucl_mod_lt_sz'.

Lemma div_eucl_mod_lt_sz_add
  : forall a sz q r, N.div_eucl a (2^(N.of_nat sz)) = (q, r) ->
                r + 2^(N.of_nat sz) < Npow2 (S sz).
Proof.
  intros. unfold Npow2. fold Npow2.
  rewrite Npow2_N.
  pose proof (div_eucl_mod_lt_sz _ _ _ _ H).
  replace 2 with (N.succ 1) by auto.
  rewrite N.mul_succ_l.
  rewrite N.mul_1_l.
  apply N.add_lt_mono_r. auto.
Qed.
Hint Resolve div_eucl_mod_lt_sz_add.

Section Varint.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Definition Varint_split n := N.div_eucl n (2^7).

  Definition Varint_format_step
             (format : funType [N : Type; CacheFormat] (B * CacheFormat)) q r ce :=
    let r' := r + (2^7) in
    `(b1, ce1) <- format_word (NToWord 8 r') ce;
      `(b2, ce2) <- format q ce1;
      ret (mappend b1 b2, ce2).
  Arguments Varint_format_step /.

  Definition Varint_format_body
             (format : funType [N : Type; CacheFormat] (B * CacheFormat))
    : funType [N : Type; CacheFormat] (B * CacheFormat) :=
    fun n ce =>
      let (q, r) := Varint_split n in
      match q with
      | N0 =>
        b <- {b : bool | True};
          if b then
            format_word (NToWord 8 r) ce
          else
            Varint_format_step format q r ce
      | Npos _ =>
        Varint_format_step format q r ce
      end.
  Arguments Varint_format_body /.

  Definition Varint_format : FormatM N B :=
    LeastFixedPoint (fDom := [N : Type; CacheFormat])
                    Varint_format_body.

  Definition Varint_decode_body
             (decode : DecodeM N B)
    : DecodeM N B :=
    fun b cd =>
      `(w, b1, cd1) <- decode_word (sz := 8) b cd;
        let r' := wordToN w in
        if r' <? (2^7) then
          Some (r', b1, cd1)
        else
          let r := r' - (2^7) in
          `(q, b2, cd2) <- decode b1 cd1;
            Some ((2^7) * q + r, b2, cd2).
  Arguments Varint_decode_body /.

  Definition Varint_decode : DecodeM N B :=
    FueledFix Varint_decode_body.

  Lemma Varint_format_body_monotone:
    monotonic_function Varint_format_body.
  Proof.
    unfold monotonic_function. simpl. intros.
    unfold Varint_split. 
    destruct N.div_eucl as [q r] eqn:Hdiv.
    destruct q.
    apply SetoidMorphisms.refine_bind. reflexivity.
    intro.
    destruct a0.
    reflexivity.
    apply SetoidMorphisms.refine_bind. reflexivity.
    intro.
    apply SetoidMorphisms.refine_bind. apply H.
    intro.
    reflexivity.
    apply SetoidMorphisms.refine_bind. reflexivity.
    intro.
    apply SetoidMorphisms.refine_bind. apply H.
    intro.
    reflexivity.
  Qed.

  Local Arguments N.add : simpl never.
  Local Arguments N.mul : simpl never.
  Theorem Varint_decode_correct
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :CorrectDecoder monoid
                    (fun _ => True)
                    (fun _ _ => True)
                    Varint_format Varint_decode P.
  Proof.
    unfold Varint_format, Varint_decode, Varint_format_body, Varint_decode_body, Varint_format_step.
    unfold Varint_split.
    eapply fix_format_correct; eauto. apply Varint_format_body_monotone.
    intros _. intros.
    split; intros. {
      clear H2 H3.
      destruct N.div_eucl as [q r] eqn:Hdiv.
      destruct q. {
        computes_to_inv2. destruct v.
        eapply (Word_decode_correct (sz := 8) (P := P)) in H4; eauto.
        destruct_many.
        eexists. repeat split; eauto.
        rewrite H2. simpl.
        rewrite wordToN_NToWord_idempotent by eauto.
        rewrite (proj2 (N.ltb_lt _ _))
          by (eapply div_eucl_mod_lt; [easy | eauto]).
        repeat progress f_equal.
        pose proof (N.div_eucl_spec data (2^7)).
        rewrite Hdiv in H5. rewrite H5. auto.
        computes_to_inv2.
        pose proof H4'.
        eapply (Word_decode_correct (sz := 8) (P := P)) in H4'; eauto.
        destruct_many.
        edestruct H as [[? [? [? ?]]] _]; eauto.
        rewrite mappend_measure in H0.
        apply format_word_some in H2; omega.
        eexists. repeat split; eauto.
        rewrite <- mappend_assoc. rewrite H3. simpl.
        rewrite wordToN_NToWord_idempotent
          by (eapply div_eucl_mod_lt_sz_add with (sz := 7%nat); eauto).
        rewrite (proj2 (N.ltb_ge _ _))
          by (rewrite N.add_comm; apply N.le_add_r).
        rewrite H7. simpl.
        repeat progress f_equal.
        pose proof (N.div_eucl_spec data (2^7)).
        rewrite Hdiv in H10. rewrite H10.
        rewrite N.add_sub. reflexivity.
      } {
        computes_to_inv2.
        pose proof H4.
        eapply (Word_decode_correct (sz := 8) (P := P)) in H4; eauto.
        destruct_many.
        edestruct H as [[? [? [? ?]]] _]; eauto.
        rewrite mappend_measure in H0. 
        apply format_word_some in H2; omega.
        eexists. repeat split; eauto.
        rewrite <- mappend_assoc. rewrite H3. simpl.
        rewrite wordToN_NToWord_idempotent
          by (eapply div_eucl_mod_lt_sz_add with (sz := 7%nat); eauto).
        rewrite (proj2 (N.ltb_ge _ _))
          by (rewrite N.add_comm; apply N.le_add_r).
        rewrite H6. simpl.
        repeat progress f_equal.
        pose proof (N.div_eucl_spec data (2^7)).
        rewrite Hdiv in H9. rewrite H9.
        rewrite N.add_sub. reflexivity.
      }
    } {
      decode_opt_to_inv.
      eapply (Word_decode_correct (sz := 8) (P := P)) in H3; eauto.
      destruct_many.
      destruct N.ltb eqn:Hlt. {
        injections. split; eauto.
        eexists _, _. repeat split; eauto.
        destruct N.div_eucl as [q r] eqn:Hdiv.
        assert (q = 0) as L1. {
          apply div_eucl_div in Hdiv. subst.
          apply N.div_small.
          apply N.ltb_lt. auto.
        }
        assert (r = wordToN x) as L2. {
          apply div_eucl_mod in Hdiv. subst.
          apply N.mod_small.
          apply N.ltb_lt. auto.
        }
        subst. rewrite NToWord_wordToN.
        computes_to_econstructor; eauto.
        instantiate (1:=true). simpl.
        eauto.
      } {
        decode_opt_to_inv.
        subst.
        edestruct H as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
        rewrite mappend_measure in H0. 
        apply format_word_some in H5; omega.
        subst. split; eauto.
        eexists _, _. repeat split; eauto.
        destruct N.div_eucl as [q r] eqn:Hdiv.
        assert (wordToN x - (2^7) < (2^7)) as L0. {
          apply N.add_lt_mono_r with (p := 2^7).
          rewrite N.sub_add by (apply N.ltb_ge; auto).
          replace (2^7 + 2^7) with (2^(N.of_nat 8)) by auto.
          rewrite Npow2_N. apply wordToN_bound.
        }
        assert (r = (wordToN x - (2^7))) as L2. {
          apply div_eucl_mod in Hdiv. subst.
          symmetry.
          eapply N.mod_unique; eauto.
        }
        destruct q.
        computes_to_econstructor; eauto.
        instantiate (2:=false). simpl.
        subst.
        rewrite N.sub_add by (apply N.ltb_ge; auto).
        rewrite NToWord_wordToN.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        apply div_eucl_div in Hdiv. symmetry in Hdiv.
        apply div_quotient_0 in Hdiv. subst.
        simpl. eassumption. inversion 1.
        eauto.
        subst.
        rewrite N.sub_add by (apply N.ltb_ge; auto).
        rewrite NToWord_wordToN.
        computes_to_econstructor; eauto.
        computes_to_econstructor; eauto.
        simpl.
        replace x4 with (N.pos p) in *.
        eassumption.
        2 : auto. 2 : apply mappend_assoc.
        apply div_eucl_div in Hdiv.
        rewrite div_quotient_eq in Hdiv. auto. inversion 1. auto.
      }
    }

    intros.
    decode_opt_to_inv. rewrite H0. simpl.
    destruct N.ltb; eauto.
    decode_opt_to_inv. erewrite H; eauto.
    auto.
  Qed.

  Lemma Varint_decode_lt
    : forall (b : B) (cd : CacheDecode) (a : N)
        (b' : B) (cd' : CacheDecode),
      Varint_decode b cd = Some (a, b', cd') -> lt_B b' b.
  Proof.
    unfold Varint_decode, Varint_decode_body.
    unfold FueledFix. intro. generalize (S (bin_measure b)). intro. revert b.
    induction n; intros. easy.
    simpl in H.
    decode_opt_to_inv.
    apply decode_word_lt in H.
    destruct N.ltb. {
      injections. auto.
    } {
      decode_opt_to_inv.
      subst.
      apply IHn in H0.
      unfold lt_B in *. omega.
    }
  Qed.

  Theorem word_format_eq
    : forall sz d b1 b2 ce1 ce1' ce2 ce2',
      format_word (sz:=sz) d ce1 ↝ (b1, ce1') ->
      format_word (sz:=sz) d ce2 ↝ (b2, ce2') ->
      b1 = b2.
    Proof.
      intros.
      repeat match goal with
             | H : format_word _  _ ↝ _ |- _ => inversion H; subst; clear H
             end; eauto.
    Qed.

  Theorem word_format_sz_eq
    : forall sz d b1 b2 ce1 ce1' ce2 ce2',
      format_word (sz:=sz) d ce1 ↝ (b1, ce1') ->
      format_word (sz:=sz) d ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
    Proof.
      intros; f_equal; eapply word_format_eq; eauto.
    Qed.

  Theorem Varint_format_eq
    : forall d b1 b2 ce1 ce1' ce2 ce2',
      Varint_format d ce1 ↝ (b1, ce1') ->
      Varint_format d ce2 ↝ (b2, ce2') ->
      b1 = b2.
  Proof.
    unfold Varint_format. simpl.
    induction d using (well_founded_ind N.lt_wf_0); intros.
    apply (unroll_LeastFixedPoint Varint_format_body_monotone) in H0.
    apply (unroll_LeastFixedPoint Varint_format_body_monotone) in H1.
    unfold Varint_format_body in *.
    unfold Varint_split in *.
    destruct N.div_eucl eqn:Hdiv. destruct n. {
      computes_to_inv2. destruct v0.
      eapply word_format_eq; eauto.
    } {
      computes_to_inv2.
      f_equal.
      - eapply word_format_eq; eauto.
      - eapply H; eauto. eapply div_eucl_div_lt; eauto; try easy.
        destruct d; easy.
    }
  Qed.

  Theorem Varint_format_sz_eq
    : forall d b1 b2 ce1 ce1' ce2 ce2',
      Varint_format d ce1 ↝ (b1, ce1') ->
      Varint_format d ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
  Proof.
    intros; f_equal; eapply Varint_format_eq; eauto.
  Qed.

  Theorem Varint_format_some
    : forall d ce b ce',
      Varint_format d ce ↝ (b, ce') ->
      (0 < bin_measure b)%nat.
  Proof.
    unfold Varint_format. simpl. intros.
    apply (unroll_LeastFixedPoint Varint_format_body_monotone) in H. simpl in H.
    unfold Varint_split in *.
    destruct N.div_eucl as [q r]. destruct q.
    eapply format_word_some in H. auto. omega.
    computes_to_inv2.
    eapply format_word_some in H. 2 : omega.
    rewrite mappend_measure. omega.
  Qed.

End Varint.

Require Import
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.Stores.EmptyStore.

Local Open Scope nat.

Lemma word_format_sz n (w : word n)
  : forall ce ce' b,
    format_word w ce ↝ (b, ce') ->
    bin_measure b = n.
Proof.
  induction w; intros; inversion H; subst; clear H.
  - auto.
  - rewrite (@measure_enqueue _ _ _ ByteString_QueueMonoidOpt).
    simpl B_measure. rewrite Nat.add_1_r. f_equal.
    apply (IHw ce' ce'). apply ReturnComputes.
Qed.

Theorem word_format_byte n (w : word n)
  : forall ce ce' b,
    n mod 8 = 0 ->
    format_word w ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  intros. erewrite word_format_sz; eauto.
Qed.

Theorem Varint_format_byte
  : forall d b ce ce',
    Varint_format d ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  induction d using (well_founded_ind N.lt_wf_0); intros.
  apply (unroll_LeastFixedPoint Varint_format_body_monotone) in H0.
  unfold Varint_format_body in *.
  unfold Varint_split in *.
  destruct N.div_eucl eqn:Hdiv. destruct n. {
    eapply word_format_byte; eauto; try easy.
  } {
    computes_to_inv2.
    rewrite @mappend_measure.
    rewrite Nat.add_mod; try easy.
    match goal with
    | _ : _ |- ?a mod _ = 0 => replace a with 0
    end; try easy.
    erewrite word_format_byte; eauto; try easy.
    symmetry. eapply H; eauto.
    eapply div_eucl_div_lt; eauto; try easy.
    destruct d; easy.
  }
Qed.

Require Import
        Fiat.Computation
        Fiat.Computation.SetoidMorphisms
        Fiat.Narcissus.BinLib.AlignWord
        Fiat.Computation.SetoidMorphisms.

Arguments CacheFormat : simpl never.
Definition Varint_encode'
  : {impl : _ | refineFun (fDom:=[N:Type; CacheFormat])
                          Varint_format (Lift_cfunType _ _ impl)}.
Proof.
  eexists.
  etransitivity.
  - eapply Finish_refining_LeastFixedPoint with (wf_P := N.lt_wf_0);
      unfold Varint_format_body; simpl; intros.
    +
      unfold Varint_split.
      destruct N.div_eucl eqn:?. destruct n; try reflexivity.
      apply SetoidMorphisms.refine_bind. reflexivity. intro.
      apply SetoidMorphisms.refine_bind. auto. reflexivity.
    + unfold respectful_hetero; simpl; intros.
      instantiate (1 := fun r y t =>
                          let q := fst (Varint_split r) in
                          let r := snd (Varint_split r) in
                          match q return ((q > 0)%N -> CacheFormat -> (ByteString * CacheFormat)) -> _ with
                          | N0 => fun _ => _
                          | Npos _ =>
                            fun f => _ (f _)
                          end (fun H => y q _)).
      unfold Varint_split in *.
      simpl.
      match goal with
      | |- context [fun H' => y ?a (@?b H')] =>
        match type of b with
        | ?H =>
          let L := fresh in
          assert H as L; [| clear L]
        end
      end. {
        clear. intros.
        abstract (destruct N.div_eucl eqn:?; simpl in *;
                  eapply div_eucl_div_lt; eauto; [| easy];
                  destruct r; injections; easy) using Varint_encode'_subproof.
      }
      instantiate (1:=Varint_encode'_subproof _ H).
      generalize (Varint_encode'_subproof r). intros.
      unfold Varint_split in *.
      destruct N.div_eucl eqn:?.
      simpl in *. destruct n.
      simpl.
      apply aligned_format_char_eq.
      simpl.
      unfold Bind2.
      rewrite aligned_format_char_eq. simplify with monad laws.
      simpl.
      match goal with
      | |- context [y _ ?b] =>
        rewrite (H _ b)
      end.
      simplify with monad laws.
      simpl.
      higher_order_reflexivity.
  - simpl; intros; higher_order_reflexivity.

    Grab Existential Variables.
    easy.
Defined.

Lemma Varint_encode_correct
  : refineFun (fDom:=[N:Type; CacheFormat])
              Varint_format (Lift_cfunType _ _ (proj1_sig Varint_encode')).
Proof.
  apply (proj2_sig Varint_encode').
Qed.

Definition Varint_encode := Eval simpl in (proj1_sig Varint_encode').