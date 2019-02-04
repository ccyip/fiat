Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Require Import Lia.

Open Scope list_scope.

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

  Definition FormatSeq_nodes (seq : FormatSeq) := (map FS_Known (FS_Segs seq)) ++ [FS_LastKnown seq].

  Definition FormatSeq_nodes_num (seq : FormatSeq) := S (length (FS_Segs seq)).

  Definition FormatSeq_nodes_num' (seq : FormatSeq) := length (FormatSeq_nodes seq).

  Lemma FormatSeq_nodes_num_eq (seq : FormatSeq)
    : FormatSeq_nodes_num seq = FormatSeq_nodes_num' seq.
  Proof.
    unfold FormatSeq_nodes_num, FormatSeq_nodes_num', FormatSeq_nodes.
    autorewrite with list. simpl. lia.
  Qed.

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

  Definition FormatSeq_know_first (seq : FormatSeq)
    : option FormatSeq :=
    match seq with
    | {| FS_Segs := segs; FS_LastKnown := lk|} =>
      match segs with
      | [] => None
      | {| FS_Fmt := fmt; FS_Used := u |} :: segs' =>
        Some {| FS_Segs := {| FS_Fmt := fmt; FS_Used := u; FS_Known := true |} :: segs';
                FS_LastKnown := lk |}
      end
    end.

  Definition FormatSeq_know_last (seq : FormatSeq)
    : FormatSeq :=
    match seq with
    | {| FS_Segs := segs |} =>
      {| FS_Segs := segs; FS_LastKnown := true |}
    end.

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

  Fixpoint FormatSeq_prev_known' (l : list FormatSeg)
    : Fin.t (S (length l)) -> option (Fin.t (S (length l))) :=
    match l with
    | [] => fun _ => None
    | {| FS_Known := b |} :: l' =>
      fun i : Fin.t (S (S (length l'))) =>
        Fin.caseS' i _ None
                   (fun i' =>
                      match FormatSeq_prev_known' l' i' with
                      | Some j => Some (Fin.FS j)
                      | None => if b then Some Fin.F1 else None
                      end)
    end.

  Definition FormatSeq_prev_known (seq : FormatSeq) (i : Fin.t (FormatSeq_nodes_num seq))
    : option (Fin.t (FormatSeq_nodes_num seq)) :=
    FormatSeq_prev_known' (FS_Segs seq) i.

  Fixpoint FormatSeq_first_known (l : list FormatSeg) (k : bool)
    : option (Fin.t (S (length l))) :=
    match l with
    | [] => if k then Some Fin.F1 else None
    | {| FS_Known := b |} :: l' =>
      if b then Some Fin.F1 else
        match FormatSeq_first_known l' k with
        | Some j => Some (Fin.FS j)
        | None => None
        end
    end.

  Fixpoint FormatSeq_next_known' (l : list FormatSeg) (k : bool)
    : Fin.t (S (length l)) -> option (Fin.t (S (length l))) :=
    match l with
    | [] => fun _ => None
    | {| FS_Known := b |} :: l' =>
      fun i : Fin.t (S (S (length l'))) =>
        Fin.caseS' i _
                   (match FormatSeq_first_known l' k with
                    | Some j => Some (Fin.FS j)
                    | None => None
                    end)
                   (fun i' =>
                      match FormatSeq_next_known' l' k i' with
                      | Some j => Some (Fin.FS j)
                      | None => None
                      end)
    end.

  Definition FormatSeq_next_known (seq : FormatSeq) (i : Fin.t (FormatSeq_nodes_num seq))
    : option (Fin.t (FormatSeq_nodes_num seq)) :=
    FormatSeq_next_known' (FS_Segs seq) (FS_LastKnown seq) i.

End Specification_Sequence.
