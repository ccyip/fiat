Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL.

Import Vector.VectorNotations.

(* Do we have this definition somewhere in the library? *)
Fixpoint Vector_repeat {A} (a : A) (n : nat) : Vector.t A n :=
  match n with
  | 0 => []
  | S n' => a :: Vector_repeat a n'
  end.

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
    SS_intro dsls (Vector_repeat false (S n)) (Vector_repeat false (S (S n))).

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

End Specification_Sequence.
