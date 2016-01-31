Require Export Coq.Numbers.BinNums
               Coq.NArith.BinNat.
Require Import Coq.omega.Omega
               Fiat.BinEncoders.Specs
               Fiat.BinEncoders.Libraries.Sig
               Fiat.BinEncoders.Libraries.BinCore.

Set Implicit Arguments.

Section FixIntBinEncoder.
  Variable size : nat.

  Fixpoint exp2' (l : nat) :=
    match l with
      | O    => xH
      | S l' => xO (exp2' l')
    end.

  Definition exp2 (l : nat) := Npos (exp2' l).

  Definition exp2_nat (l : nat) := nat_of_N (exp2 l).

  Fixpoint encode''(pos : positive) (acc : bin_t) :=
    match pos with
      | xI pos' => encode'' pos' (true :: acc)
      | xO pos' => encode'' pos' (false :: acc)
      | xH      => true :: acc
    end.

  Definition encode' (n : N) :=
    match n with
      | N0       => nil
      | Npos pos => encode'' pos nil
    end.

  Fixpoint pad (b : bin_t) (l : nat) :=
    match l with
      | O    => b
      | S l' => false :: pad b l'
    end.

  Definition FixInt_encode_inner (n : {n : N | (n < exp2 size)%N}) :=
    let b := encode' (proj1_sig n)
    in  pad b (size - (length b)).

  Fixpoint decode'' (b : bin_t) (l : nat) (acc : positive) :=
    match l with
      | O    => (acc, b)
      | S l' =>
        match b with
          | nil         => (acc, nil)
          | false :: b' => decode'' b' l' (xO acc)
          | true  :: b' => decode'' b' l' (xI acc)
        end
    end.

  Fixpoint decode' (b : bin_t) (l : nat) {struct l} :=
    match l with
      | O    => (N0, b)
      | S l' =>
        match b with
          | nil         => (N0, nil)
          | false :: b' => decode' b' l'
          | true  :: b' =>
            match decode'' b' l' xH with
              | (pos, b'') => (Npos pos, b'')
            end
        end
    end.

  Lemma decode'_size : forall s b, N.lt (fst (decode'  b s)) (exp2 s).
  Proof.
    induction s; intuition eauto; simpl.
    rewrite <- N.compare_lt_iff; eauto.
    destruct b; simpl.
    - rewrite <- N.compare_lt_iff; eauto.
    - destruct b; simpl.
      + simpl. admit.
      + etransitivity; eauto; unfold exp2.
        admit.
  Qed.

  Definition FixInt_decode (b : bin_t) : {n : N | (n < exp2 size)%N} * bin_t.
    refine (exist _ (fst (decode' b size)) _, snd (decode' b size)).
    eapply decode'_size.
  Defined.

  Lemma encode''_pull : forall pos acc, encode'' pos acc =  encode'' pos nil ++ acc.
  Proof.
    (induction pos; simpl; intuition eauto);
    [ rewrite IHpos; rewrite IHpos with (acc:=(true :: nil));
      rewrite <- app_assoc; reflexivity |
      rewrite IHpos; rewrite IHpos with (acc:=(false :: nil));
      rewrite <- app_assoc; reflexivity ].
  Qed.

  Lemma encode''_size :
    forall p s, BinPos.Pos.lt p (exp2' s) -> length (encode'' p nil) <= s.
  Proof.
    intros p s; generalize dependent p; induction s; intuition.
    - inversion H; destruct p; compute in H1; discriminate.
    - destruct p.
      + simpl; rewrite encode''_pull; rewrite app_length; simpl.
        rewrite Plus.plus_comm; simpl; apply Le.le_n_S.
        apply IHs; unfold BinPos.Pos.lt, BinPos.Pos.compare in H; simpl in *.
        apply BinPos.Pos.compare_cont_Gt_Lt; assumption.
      + simpl; rewrite encode''_pull; rewrite app_length; simpl.
        rewrite Plus.plus_comm; simpl; apply Le.le_n_S.
        apply IHs; unfold BinPos.Pos.lt, BinPos.Pos.compare in *; simpl in *.
        assumption.
      + simpl; auto with arith.
  Qed.

  Lemma encode'_size : forall n s, N.lt n (exp2 s) -> length (encode' n) <= s.
  Proof.
    intros; unfold encode'; destruct n.
    + auto with arith.
    + apply encode''_size. unfold BinPos.Pos.lt, exp2 in H. apply H.
  Qed.

  Lemma decode'_pad :
    forall ls s ext, length ls <= s ->
                     decode' (pad ls (s - length ls) ++ ext) s =
                     decode' (ls ++ ext) (length ls).
  Proof.
    intros ls s; remember (s - length ls) as m;
    generalize dependent s; generalize dependent ls;
    induction m; intuition; simpl.
    destruct s; [ omega | simpl ].
    apply IHm; omega.
  Qed.

  Lemma decode''_length :
    forall ls ext p,
      decode'' (ls ++ ext) (length ls) p =
      (fst (decode'' ls (length ls) p), (snd (decode'' ls (length ls) p) ++ ext)).
  Proof.
    induction ls; intuition eauto; simpl.
    { destruct ext; eauto. }
    { destruct a; eauto. }
  Qed.

  Lemma decode'_length :
    forall ls ext,
      decode' (ls ++ ext) (length ls) =
      (fst (decode' ls (length ls)), (snd (decode' ls (length ls)) ++ ext)).
  Proof.
    induction ls; intuition eauto; simpl.
    destruct a; eauto.
    repeat rewrite decode''_length.
    destruct (decode'' ls (length ls) 1); eauto.
  Qed.

  Lemma decode''_pulltrue :
    forall ls p,
      decode'' (ls ++ true :: nil) (length (ls ++ true :: nil)) p =
      (xI (fst (decode'' ls (length ls) p)), snd (decode'' ls (length ls) p)).
  Proof.
    induction ls; simpl; intuition eauto.
    destruct a; eauto.
  Qed.

  Lemma decode''_pullfalse :
    forall ls p,
      decode'' (ls ++ false :: nil) (length (ls ++ false :: nil)) p =
      (xO (fst (decode'' ls (length ls) p)), snd (decode'' ls (length ls) p)).
  Proof.
    induction ls; simpl; intuition eauto.
    destruct a; eauto.
  Qed.

  Lemma encode_correct' :
    forall p, decode' (encode'' p nil) (length (encode'' p nil)) = (N.pos p, nil).
  Proof.
    induction p; intuition eauto; simpl; rewrite encode''_pull.
    { remember (encode'' p Datatypes.nil) as ls; clear Heqls.
      generalize dependent p; induction ls; intuition eauto; inversion IHp.
      destruct a; simpl in *; eauto.
      clear -IHp; rewrite decode''_pulltrue.
      destruct (decode'' ls (length ls) 1).
      inversion IHp; eauto.
    }
    { remember (encode'' p Datatypes.nil) as ls; clear Heqls.
      generalize dependent p; induction ls; intuition eauto; inversion IHp.
      destruct a; simpl in *; eauto.
      clear -IHp; rewrite decode''_pullfalse.
      destruct (decode'' ls (length ls) 1).
      inversion IHp; eauto.
    }
  Qed.

  Theorem FixInt_encode_correct : bin_encode_correct FixInt_encode_inner FixInt_decode.
  Proof.
    unfold bin_encode_correct, FixInt_encode_inner, FixInt_decode.
    intros [n P] ext; simpl; f_equal;
    [  eapply sig_equivalence; change n with (fst (n, ext)) |
       change ext with (snd (n, ext)) ]; f_equal;
    apply encode'_size in P;
    rewrite decode'_pad; eauto; clear P;
    destruct n; simpl; eauto; rewrite decode'_length;
    rewrite encode_correct'; reflexivity.
  Qed.
End FixIntBinEncoder.

Definition FixInt_eq_dec (size : nat) (n m : {n | (n < exp2 size)%N }) : {n = m} + {n <> m}.
  refine (if N.eq_dec (proj1_sig n) (proj1_sig m) then left _ else right _);
  destruct n; destruct m; [ eapply sig_equivalence; intuition | congruence ].
Defined.

Definition FixInt_encode (size : nat) :=
  bin_encode_transform_pair (FixInt_encode_inner (size:=size)).

Global Instance FixInt_decoder
       (size : nat)
  : decoder (fun _ => True) (FixInt_encode (size:=size)) :=
  bin_encode_transform_pair_decoder (@FixInt_encode_correct size).