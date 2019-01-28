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

  Inductive SpecsSeq n : Type :=
  | SS_intro: Vector.t (SpecsDSL A T) (S n) ->
              Vector.t bool (S n) ->
              Vector.t bool (S (S n)) ->
              SpecsSeq n.

  Definition SpecsSeq_lift {n} (dsls : Vector.t (SpecsDSL A T) (S n))
    : SpecsSeq n :=
    SS_intro dsls (Vector.repeat false (S n)) (Vector.repeat false (S (S n))).

  Definition SpecsSeq_erase {n} (seq : SpecsSeq n)
    : Vector.t _ _ :=
    match seq with
    | SS_intro dsls _ _ => dsls
    end.

  Inductive SpecsDSL_Vec_Sim : SpecsDSL A T -> forall {n}, Vector.t (SpecsDSL A T) (S n) -> Prop :=
  | SSS_Atomic: forall dsl,
      SpecsDSL_Atomic dsl ->
      SpecsDSL_Vec_Sim dsl (Vector.cons _ dsl _ (Vector.nil _))
  | SSS_Sequence: forall dsl1 {m} (v1 : Vector.t _ (S m)) dsl2 {n} (v2 : Vector.t _ (S n)),
      SpecsDSL_Vec_Sim dsl1 v1 ->
      SpecsDSL_Vec_Sim dsl2 v2 ->
      SpecsDSL_Vec_Sim (SL_Sequence dsl1 dsl2) (Vector.append v1 v2)
  .

  Lemma SpecsDSL_vec_atomic {n}
    : forall dsl (dsls : Vector.t (SpecsDSL A T) (S n)),
      SpecsDSL_Vec_Sim dsl dsls -> forall d, Vector.In d dsls -> SpecsDSL_Atomic d.
  Proof.
    intros. induction H.
    - inversion H0. eauto. inversion H3.
    - destruct (Vector.in_app_or v1 v2 d H0); eauto.
  Qed.

End Specification_Sequence.
