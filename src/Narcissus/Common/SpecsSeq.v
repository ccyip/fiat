Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Require MoreVectors.Vector.
Import Vector.VectorNotations.

Section Specification_Sequence.

  Variable A : Type.
  Variable T : Type.
  Context {monoid : Monoid T}.

  Inductive FormatSeq n : Type :=
  | FS_intro: Vector.t (FormatDSL A T) (S n) ->
              Vector.t bool (S n) ->
              Vector.t bool (S (S n)) ->
              FormatSeq n.

  Definition FormatSeq_lift {n} (dsls : Vector.t (FormatDSL A T) (S n))
    : FormatSeq n :=
    FS_intro dsls (Vector.repeat false (S n)) (Vector.repeat false (S (S n))).

  Definition FormatSeq_erase {n} (seq : FormatSeq n)
    : Vector.t _ _ :=
    match seq with
    | FS_intro dsls _ _ => dsls
    end.

  Inductive FormatDSL_Vec_Sim : FormatDSL A T -> forall {n}, Vector.t (FormatDSL A T) (S n) -> Prop :=
  | FVS_Atomic: forall dsl,
      FormatDSL_Atomic dsl ->
      FormatDSL_Vec_Sim dsl (Vector.cons _ dsl _ (Vector.nil _))
  | FVS_Sequence: forall dsl1 {m} (v1 : Vector.t _ (S m)) dsl2 {n} (v2 : Vector.t _ (S n)),
      FormatDSL_Vec_Sim dsl1 v1 ->
      FormatDSL_Vec_Sim dsl2 v2 ->
      FormatDSL_Vec_Sim (FL_Sequence dsl1 dsl2) (Vector.append v1 v2)
  .

  Lemma FormatDSL_vec_atomic {n}
    : forall dsl (dsls : Vector.t (FormatDSL A T) (S n)),
      FormatDSL_Vec_Sim dsl dsls -> forall d, Vector.In d dsls -> FormatDSL_Atomic d.
  Proof.
    intros. induction H.
    - inversion H0. eauto. inversion H3.
    - destruct (Vector.in_app_or v1 v2 d H0); eauto.
  Qed.

End Specification_Sequence.
