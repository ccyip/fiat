Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Require Import Lia.

Section Specification_Sequence.

  Variable A : Type.
  Variable T : Type.
  Context {monoid : Monoid T}.

  Record FormatSeg : Type :=
    {
      FS_Fmt : FormatDSL A T;
      FS_Used : bool;
      FS_Known : bool;
    }.

  Record FormatSeq : Type :=
    {
      FS_Segs : list FormatSeg;
      FS_LastKnown : bool;
    }.

  Definition FormatSeq_wellformed (seq : FormatSeq) := 1 <= length (FS_Segs seq).

  Definition FormatSeq_lift (dsls : list (FormatDSL A T))
    : FormatSeq :=
    {| FS_Segs := map (fun fmt => {| FS_Fmt := fmt;
                                  FS_Used := false; FS_Known := false |})
                      dsls;
       FS_LastKnown := false |}.

  Definition FormatSeq_erase (seq : FormatSeq)
    : list (FormatDSL A T) :=
    map (fun seg => FS_Fmt seg) (FS_Segs seq).

  Inductive FormatDSL_Seq_Sim : FormatDSL A T -> list (FormatDSL A T) -> Prop :=
  | FVS_Atomic: forall fmt,
      FormatDSL_atomic fmt = true ->
      FormatDSL_Seq_Sim fmt [fmt]
  | FVS_Sequence: forall fmt1 l1 fmt2 l2,
      FormatDSL_Seq_Sim fmt1 l1 ->
      FormatDSL_Seq_Sim fmt2 l2 ->
      FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) (l1 ++ l2)
  .

  Lemma FormatDSL_seq_atomic
    : forall fmt l, FormatDSL_Seq_Sim fmt l -> forall f, In f l -> FormatDSL_atomic f = true.
  Proof.
    intros. induction H.
    - inversion H0; subst; eauto.
    - apply in_app_or in H0. destruct H0; eauto.
  Qed.

  Lemma FormatDSL_seq_wellformed
    : forall fmt l, FormatDSL_Seq_Sim fmt l -> FormatSeq_wellformed (FormatSeq_lift l).
  Proof.
    intros; induction H.
    - intuition.
    - simpl. unfold FormatSeq_wellformed in *.
      simpl in *. autorewrite with list in *. lia.
  Qed.

End Specification_Sequence.
