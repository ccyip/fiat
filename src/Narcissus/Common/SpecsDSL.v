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

(* Annotated formats *)
Inductive AFormatDSL S T : Type :=
| AFL_None `{Monoid T}: FormatDSL S T -> AFormatDSL S T
| AFL_Right `{Monoid T}: FormatDSL S T -> AFormatDSL S T
| AFL_Left `{Monoid T}: FormatDSL S T -> AFormatDSL S T.

Fixpoint AFormatDSL_denote {S T} (adsl : AFormatDSL S T) : FormatM (S * T) T :=
  match adsl with
  | AFL_None _ dsl => fun st t => FormatDSL_denote dsl (fst st) ∋ t /\ (snd st) = mempty
  | AFL_Right _ dsl => fun st t => exists t1, (FormatDSL_denote dsl) (fst st) ∋ t1 /\ t = mappend t1 (snd st)
  | AFL_Left _ dsl => fun st t => exists t2, (FormatDSL_denote dsl) (fst st) ∋ t2 /\ t = mappend (snd st) t2
  end.

(* (SL_Arbitrary IdentityFormat) might not be a good idea, since we do not have
   the eliminator for any arbitrary formats in FormatM, which means we cannot
   pattern match IdentityFormat. We should possibly have a constructor called
   SL_Primitive and collect all the built-in formats there. *)
Fixpoint AFormatDSL_to_FormatDSL {S T} (adsl : AFormatDSL S T)
  : FormatDSL (S * T) T :=
  match adsl with
  | AFL_None _ dsl => FL_Restrict (FL_Projection dsl fst)
                                 (fun s => snd s = mempty)
  | AFL_Right _ dsl => FL_Sequence (FL_Projection dsl fst)
                                  (FL_Projection (FL_Arbitrary IdentityFormat) snd)
  | AFL_Left _ dsl => FL_Sequence (FL_Projection (FL_Arbitrary IdentityFormat) snd)
                                 (FL_Projection dsl fst)
  end.

Lemma AFormatDSL_to_FormatDSL_denote_equiv {S T} (adsl : AFormatDSL S T)
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

Inductive FormatDSL_Atomic {S T} : FormatDSL S T -> Prop :=
| FA_Arbitrary: forall fmt, FormatDSL_Atomic (FL_Arbitrary fmt)
| FA_Compose: forall S' (dsl1 : FormatDSL S' T) (dsl2 : FormatDSL S S'),
    FormatDSL_Atomic (FL_Compose dsl1 dsl2)
| FA_Projection: forall S' (dsl : FormatDSL S' T) (f : S -> S'),
    FormatDSL_Atomic (FL_Projection dsl f)
| FA_Restrict: forall dsl P, FormatDSL_Atomic (FL_Restrict dsl P)
| FA_Union: forall dsl1 dsl2, FormatDSL_Atomic (FL_Union dsl1 dsl2)
.

Definition FormatDSL_atomic {S T} (dsl : FormatDSL S T)
  : {FormatDSL_Atomic dsl} + {~ FormatDSL_Atomic dsl}.
Proof.
  refine (match dsl with
          | FL_Sequence _ dsl1 dsl2 => right _
          | _ => left _
          end); abstract (constructor || inversion 1).
Defined.

Lemma FormatDSL_Atomic_not_iff {S T} (dsl : FormatDSL S T)
  : ~ FormatDSL_Atomic dsl <-> exists `(Monoid T) dsl1 dsl2, dsl = FL_Sequence dsl1 dsl2.
Proof.
  destruct dsl; split; intros; destruct_ex; try easy; eauto.
  all : exfalso; apply H; constructor.
Qed.