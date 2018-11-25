Require Import
        Fiat.Common.ilist
        Fiat.Common.IterateBoundedIndex
        Fiat.Narcissus.Common.SpecsSimpl.

Section UnionFormat.

  Context {S : Type}. (* Source Type *)
  Context {T : Type}. (* Target Type *)

  Definition Union_Format
             (format1 format2 : FormatM S T)
    : FormatM S T :=
    fun s t =>
      format1 s ∋ t \/ format2 s ∋ t.

  Definition Union_Decode
             (decode1 decode2 : DecodeM S T)
             (choose : T -> bool)
    : DecodeM S T := fun t => if choose t then decode1 t else decode2 t.

  Definition Union_Encode
             (encode1 encode2 : EncodeM S T)
             (choose : S -> bool)
    : EncodeM S T := fun s => if choose s then encode1 s else encode2 s.

  Lemma CorrectDecoder_Union
        (format1 format2 : FormatM S T)
        (decode1 decode2 : DecodeM S T)
        (decode1_correct : CorrectDecoder_simpl format1 decode1)
        (decode2_correct : CorrectDecoder_simpl format2 decode2)
        (choose : T -> bool)
        (unique_format :
           forall s t,
             Union_Format format1 format2 s ∋ t ->
             if choose t then format1 s ∋ t else format2 s ∋ t) (* implies target disjoint. *)
    : CorrectDecoder_simpl (Union_Format format1 format2) (Union_Decode decode1 decode2 choose).
  Proof.
    unfold Union_Decode, Union_Format in *; split; intros;
      rewrite @unfold_computes in *.
    - apply (unique_format s t) in H.
      find_if_inside; apply decode1_correct || apply decode2_correct; auto.
    - find_if_inside; apply decode1_correct in H || apply decode2_correct in H; auto.
  Qed.

  Lemma CorrectEncoder_Union
        (format1 format2 : FormatM S T)
        (encode1 encode2 : EncodeM S T)
        (encode1_correct : CorrectEncoder format1 encode1)
        (encode2_correct : CorrectEncoder format2 encode2)
        (choose : S -> bool)
        (unique_format :
           forall s t,
             Union_Format format1 format2 s ∋ t ->
             if choose s then format1 s ∋ t else format2 s ∋ t)
    : CorrectEncoder (Union_Format format1 format2) (Union_Encode encode1 encode2 choose).
  Proof.
    unfold Union_Encode, Union_Format in *; split; intros;
      rewrite @unfold_computes in *.
    - find_if_inside; apply encode1_correct in H || apply encode2_correct in H; auto.
    - intro. apply (unique_format s t) in H0.
      find_if_inside; apply encode1_correct in H0 || apply encode2_correct in H0; eauto.
  Qed.

  (* Expensive but works well as a fallback chooser. *)
  Definition Choose_by_decode (decode : DecodeM S T) :=
    fun t => if decode t then true else false.

  Lemma Choose_by_decode_unique_format
        (format1 format2 : FormatM S T)
        (decode1 decode2 : DecodeM S T)
        (decode1_correct : CorrectDecoder_simpl format1 decode1)
        (decode2_correct : CorrectDecoder_simpl format2 decode2)
        (format_disjoint : DisjointFormat format1 format2)
    : forall s t,
      Union_Format format1 format2 s ∋ t ->
      if Choose_by_decode decode1 t then format1 s ∋ t else format2 s ∋ t.
  Proof.
    unfold Choose_by_decode. intros.
    destruct H.
    - pose proof H. apply decode1_correct in H. rewrite H. auto.
    - destruct (decode1 t) eqn:?; auto.
      apply decode1_correct in Heqo.
      exfalso. eapply format_disjoint; eauto.
  Qed.

End UnionFormat.

Notation "format1 ∪ format2" := (Union_Format format1 format2) (at level 55) : format_scope.
