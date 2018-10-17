Require Import
        Coq.Init.Wf
        Coq.Arith.Compare_dec
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
        Fiat.Narcissus.Formats.VarintOpt
        Fiat.Narcissus.Formats.InternetChecksum.

Require Import NArith NArithRing.
Import FixComp.LeastFixedPointFun.

Local Open Scope comp_scope.

Arguments split1 : simpl never.
Arguments split2 : simpl never.
Arguments combine : simpl never.

Section WordLE.
  Context {B : Type}.
  Context {cache : Cache}.
  Context {cacheAddNat : CacheAdd cache nat}.
  Context {monoid : Monoid B}.
  Context {monoidUnit : QueueMonoidOpt monoid bool}.

  Fixpoint format_wordLE {n} : FormatM (word n) B :=
    match n with
    | S (S (S (S (S (S (S (S n'))))))) =>
      fun w ce =>
        `(b1, ce1) <- format_word (split1 8 _ w) ce;
        `(b2, ce2) <- format_wordLE (split2 8 _ w) ce1;
        ret (mappend b1 b2, ce2)
    | _ =>
      fun w ce =>
        format_word w ce
    end.

  Fixpoint encode_wordLE {n} : word n -> CacheFormat -> B * CacheFormat :=
    match n with
    | S (S (S (S (S (S (S (S n'))))))) =>
      fun w ce =>
        let (b1, ce1) := encode_word (split1 8 _ w) ce in
        let (b2, ce2) := encode_wordLE (split2 8 _ w) ce1 in
        (mappend b1 b2, ce2)
    | _ =>
      fun w ce =>
        encode_word w ce
    end.

  Fixpoint decode_wordLE n (b : B) (cd : CacheDecode) : option (word n * B * CacheDecode) :=
    match n with
    | S (S (S (S (S (S (S (S n'))))))) =>
      `(lo, b1, cd1) <- decode_word (sz:=8) b cd;
        `(hi, b2, cd2) <- decode_wordLE _ b1 cd1;
        Some (combine lo hi, b2, cd2)
    | _ =>
      decode_word b cd
    end.

  Theorem decode_wordLE_correct n
          {P : CacheDecode -> Prop}
          (P_OK : cache_inv_Property P (fun P => forall b cd, P cd -> P (addD cd b)))
    :
      CorrectDecoder monoid (fun _ => True)
                              (fun _ _ => True)
                              (@format_wordLE n) (decode_wordLE n) P.
  Proof.
    induction n using (well_founded_ind lt_wf).
    do 8 (destruct n; eauto using Word_decode_correct).
    simpl; split; intros. {
      computes_to_inv2.
      eapply Word_decode_correct in H3; eauto. destruct_many.
      eapply H in H3'; eauto. 2 : omega. destruct_many.
      rewrite <- mappend_assoc. rewrite H3. simpl.
      rewrite H6. simpl. eexists. repeat split; eauto.
      repeat f_equal. apply combine_split.
    } {
      decode_opt_to_inv.
      eapply Word_decode_correct in H2; eauto. destruct_many.
      eapply H in H3; eauto. 2 : omega. destruct_many.
      subst. split; eauto. eexists _, _.
      repeat split; eauto using mappend_assoc.
      rewrite split1_combine, split2_combine.
      computes_to_econstructor; eauto.
      computes_to_econstructor; eauto.
    }
  Qed.

  Lemma decode_wordLE_lt
    : forall n (b : B) (cd : CacheDecode) (w : word (S n))
        (b' : B) (cd' : CacheDecode),
      decode_wordLE (S n) b cd = Some (w, b', cd') -> lt_B b' b.
  Proof.
    induction n using (well_founded_ind lt_wf); intros.
    do 7 (destruct n; eauto using decode_word_lt).
    simpl in H0.
    decode_opt_to_inv.
    subst.
    apply decode_word_lt in H0.
    destruct n. simpl in H1.
    apply decode_word_le in H1.
    unfold lt_B, le_B in *. omega.
    apply H in H1; unfold lt_B in *; omega.
  Qed.

  Theorem format_wordLE_eq
    : forall n (w : word n) b1 b2 ce1 ce1' ce2 ce2',
      format_wordLE w ce1 ↝ (b1, ce1') ->
      format_wordLE w ce2 ↝ (b2, ce2') ->
      b1 = b2.
  Proof.
    induction n using (well_founded_ind lt_wf); intros.
    do 8 (destruct n; eauto using word_format_eq).
    simpl in H0, H1.
    computes_to_inv2.
    f_equal.
    eapply word_format_eq; eauto.
    eapply H. 2-3 : eauto.
    omega.
  Qed.

  Theorem format_wordLE_sz_eq
    : forall n (w : word n) b1 b2 ce1 ce1' ce2 ce2',
      format_wordLE w ce1 ↝ (b1, ce1') ->
      format_wordLE w ce2 ↝ (b2, ce2') ->
      bin_measure b1 = bin_measure b2.
  Proof.
    intros; f_equal; eapply format_wordLE_eq; eauto.
  Qed.

  Theorem format_wordLE_some
    : forall n (w : word (S n)) ce b ce',
      format_wordLE w ce ↝ (b, ce') ->
      (0 < bin_measure b)%nat.
  Proof.
    intros.
    do 7 (destruct n; [apply format_word_some in H; omega | ]).
    simpl in H.
    computes_to_inv2.
    eapply format_word_some in H. 2 : omega.
    rewrite mappend_measure. omega.
  Qed.

End WordLE.

Require Import
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.Stores.EmptyStore.

Theorem format_wordLE_byte
  : forall n (w : word n) b ce ce',
    n mod 8 = 0 ->
    format_wordLE w ce ↝ (b, ce') ->
    bin_measure b mod 8 = 0.
Proof.
  induction n using (well_founded_ind lt_wf); intros.
  destruct n; eauto using word_format_byte.
  do 7 (destruct n; [inversion H0 |]).
  simpl in H1.
  computes_to_inv2.
  rewrite @mappend_measure.
  rewrite Nat.add_mod. 2 : omega.
  eapply word_format_byte in H1; auto.
  eapply H in H1'. 2 : omega.
  rewrite H1, H1'. reflexivity.
  assert ((n + 1 * 8) mod 8 = 0). {
    rewrite Nat.add_comm. auto.
  }
  erewrite <- Nat.mod_add; eauto.
Qed.

Require Import
        Fiat.Narcissus.BinLib.Core
        Fiat.Narcissus.BinLib.AlignedByteString
        Fiat.Narcissus.BinLib.AlignWord.

Fixpoint WordLE_encode {n} : word (8*n) -> Vector.t char n.
Proof.
  destruct n; intros w.
  - exact (Vector.nil _).
  - replace (8 * S n) with (8 + (8 * n)) in w by abstract omega.
    exact (Vector.cons _ (split1 8 _ w) _ (WordLE_encode _ (split2 8 _ w))).
Defined.

Lemma WordLE_encode_correct {n}
  : forall (w : word (8*n)) (ce : CacheFormat),
    refine (format_wordLE w ce)
           (ret ((fun w ce => (build_aligned_ByteString (WordLE_encode w), ce)) w ce)).
Proof.
  induction n; intros.
  simpl in *. unfold format_wordLE.
  shatter_word w.
  unfold format_word. simpl.
  f_equiv. f_equal.
  eapply ByteString_f_equal; simpl.
  instantiate (1 := eq_refl _). reflexivity.
  instantiate (1 := eq_refl _). reflexivity.
  unfold WordLE_encode.
  generalize (WordLE_encode_subproof n). destruct e.
  set (8*n) as n'.
  etransitivity.
  eapply AlignedFormatChar.
  apply IHn.
  reflexivity.
Qed.
