Require Export
        Fiat.Common.Maps
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Require Import Lia.

Section Specification_Sequence.

  Variable A : Type.
  Variable T : Type.
  Context {monoid : Monoid T}.

  Open Scope list_scope.
  Open Scope maps_scope.

  Record FormatSeg : Type :=
    {
      FS_Fmt : FormatDSL A T;
      FS_Used : bool;
      FS_Known : bool;
    }.

  Global Instance EqbDec_nat : Decidable.EqbDec nat :=
    {
      eqb := Nat.eqb;
      eqb_spec := PeanoNat.Nat.eqb_eq
    }.

  (* Maybe I should pack the number of nodes into it *)
  Definition FormatSeq := total_map nat FormatSeg.

  Definition FormatSeq_default := {| FS_Fmt := FL_Arbitrary EmptyFormat;
                                     FS_Used := true;
                                     FS_Known := false |}.

  (* Fixpoint FormatSeq_lift (l : list (FormatDSL A T)) *)
  (*   : FormatSeq := *)
  (*   match l with *)
  (*   | [] => {--> FormatSeq_default } *)
  (*   | fmt :: l' => fun i => *)
  (*                  match i with *)
  (*                  | O => {| FS_Fmt := fmt; FS_Used := false; FS_Known := false |} *)
  (*                  | S i' => FormatSeq_lift l' i' *)
  (*                  end *)
  (*   end. *)

  Fixpoint FormatSeq_lift' (l : list (FormatDSL A T)) (i : nat) (seq : FormatSeq)
    : FormatSeq :=
    match l with
    | [] => seq
    | fmt :: l' =>
      t_update (FormatSeq_lift' l' (S i) seq) i
               {| FS_Fmt := fmt; FS_Used := false; FS_Known := false |}
    end.

  Fixpoint FormatSeq_lift (l : list (FormatDSL A T))
    : FormatSeq :=
    FormatSeq_lift' l 0 {--> FormatSeq_default}.

  Definition FormatSeq_know_nth (seq : FormatSeq) (i : nat)
    : FormatSeq :=
    match seq i with
    | {| FS_Fmt := fmt; FS_Used := u |} => t_update seq i {| FS_Fmt := fmt;
                                                             FS_Used := u;
                                                             FS_Known := true|}
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

  Definition FormatSeq_is_next_known (seq : FormatSeq) (i : nat) (k : nat) :=
    i < k /\ FS_Known (seq k) = true /\
    forall j, i < j -> j < k -> FS_Known (seq j) = false.

  Definition FormatSeq_no_next_known (seq : FormatSeq) (i : nat) :=
    forall k, i < k -> FS_Known (seq k) = false.

  Definition FormatSeq_is_prev_known (seq : FormatSeq) (i : nat) (k : nat) :=
    k < i /\ FS_Known (seq k) = true /\
    forall j, k < j -> j < i -> FS_Known (seq j) = false.

  Definition FormatSeq_no_prev_known (seq : FormatSeq) (i : nat) :=
    forall k, k < i -> FS_Known (seq k) = false.

  Definition FormatSeq_all_done (seq : FormatSeq) :=
    forall i, FS_Known (seq i) = true /\ FS_Used (seq i) = true.

End Specification_Sequence.
