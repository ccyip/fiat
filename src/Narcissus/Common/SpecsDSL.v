Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats.

Inductive FormatDSL S T : Type :=
| FL_Arbitrary: FormatM S T -> FormatDSL S T
| FL_Compose {S'}: FormatDSL S' T -> FormatDSL S S' -> FormatDSL S T
| FL_Projection {S'}: FormatDSL S' T -> (S -> S') -> FormatDSL S T
| FL_Restrict: FormatDSL S T -> (S -> Prop) -> FormatDSL S T
| FL_Union: FormatDSL S T -> FormatDSL S T -> FormatDSL S T
| FL_Sequence `{Monoid T}: FormatDSL S T -> FormatDSL S T -> FormatDSL S T
(* | SL_Fixpoint: (FormatM S T -> FormatDSL S T) -> FormatDSL S T *)
.

Fixpoint FormatDSL_denote {S T} (dsl : FormatDSL S T) : FormatM S T :=
  match dsl with
  | FL_Arbitrary fmt => fmt
  | FL_Compose _ fmt1 fmt2 => Compose_Format (FormatDSL_denote fmt1) (FormatDSL_denote fmt2)
  | FL_Projection _ fmt1 f => Projection_Format (FormatDSL_denote fmt1) f
  | FL_Restrict fmt1 P => Restrict_Format P (FormatDSL_denote fmt1)
  | FL_Union fmt1 fmt2 => Union_Format (FormatDSL_denote fmt1) (FormatDSL_denote fmt2)
  | FL_Sequence _ fmt1 fmt2 => Sequence_Format (FormatDSL_denote fmt1) (FormatDSL_denote fmt2)
  (* | SL_Fixpoint F => Fix_Format (fun rec => FormatDSL_denote (F rec)) *)
  end.

Section AnnotatedFormats.

  Variable S : Type.
  Variable T : Type.
  Context `{Monoid T}.

  Inductive AFormatDSL : Type :=
  | AFL_None: FormatDSL S T -> AFormatDSL
  | AFL_Right: FormatDSL S T -> AFormatDSL
  | AFL_Left: FormatDSL S T -> AFormatDSL.

  Fixpoint AFormatDSL_denote (adsl : AFormatDSL) : FormatM (S * T) T :=
    match adsl with
    | AFL_None dsl => fun st t => FormatDSL_denote dsl (fst st) ∋ t /\ (snd st) = mempty
    | AFL_Right dsl => fun st t => exists t1, (FormatDSL_denote dsl) (fst st) ∋ t1 /\ t = mappend t1 (snd st)
    | AFL_Left dsl => fun st t => exists t2, (FormatDSL_denote dsl) (fst st) ∋ t2 /\ t = mappend (snd st) t2
    end.

  (* (SL_Arbitrary IdentityFormat) might not be a good idea, since we do not have
   the eliminator for any arbitrary formats in FormatM, which means we cannot
   pattern match IdentityFormat. We should possibly have a constructor called
   SL_Primitive and collect all the built-in formats there. *)
  Fixpoint AFormatDSL_to_FormatDSL (adsl : AFormatDSL)
    : FormatDSL (S * T) T :=
    match adsl with
    | AFL_None dsl => FL_Restrict (FL_Projection dsl fst)
                                   (fun s => snd s = mempty)
    | AFL_Right dsl => FL_Sequence (FL_Projection dsl fst)
                                    (FL_Projection (FL_Arbitrary IdentityFormat) snd)
    | AFL_Left dsl => FL_Sequence (FL_Projection (FL_Arbitrary IdentityFormat) snd)
                                   (FL_Projection dsl fst)
    end.

  Lemma AFormatDSL_to_FormatDSL_denote_equiv (adsl : AFormatDSL)
    : EquivFormat (FormatDSL_denote (AFormatDSL_to_FormatDSL adsl))
                  (AFormatDSL_denote adsl).
  Proof.
    destruct adsl; simpl; rewrite !Projection_Format_equiv.
    - rewrite Restrict_Format_equiv. reflexivity.
    - rewrite Sequence_Format_equiv. unfold Sequence_Format'. unfold IdentityFormat.
      split; intros ? ?; rewrite unfold_computes in *;
        destruct_ex; split_and; subst;
          repeat econstructor; eauto.
      f_equal; auto.
    - rewrite Sequence_Format_equiv. unfold Sequence_Format'. unfold IdentityFormat.
      split; intros ? ?; rewrite unfold_computes in *;
        destruct_ex; split_and; subst;
          repeat econstructor; eauto.
      f_equal; auto.
  Qed.

End AnnotatedFormats.

Section AtomicFormats.

  Variable S : Type.
  Variable T : Type.

  Definition FormatDSL_atomic (dsl : FormatDSL S T) : bool :=
    match dsl with
    | FL_Sequence _ _ _ => false
    | _ => true
    end.

  Lemma FormatDSL_Atomic_not_iff (dsl : FormatDSL S T)
    : FormatDSL_atomic dsl = false <-> exists `(Monoid T) dsl1 dsl2, dsl = FL_Sequence dsl1 dsl2.
  Proof.
    destruct dsl; split; intros; destruct_ex; try easy; eauto.
  Qed.

End AtomicFormats.