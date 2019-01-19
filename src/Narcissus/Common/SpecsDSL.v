Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats.

Inductive SpecsDSL S T : Type :=
| SL_Arbitrary: FormatM S T -> SpecsDSL S T
| SL_Compose {S'}: SpecsDSL S' T -> SpecsDSL S S' -> SpecsDSL S T
| SL_Projection {S'}: SpecsDSL S' T -> (S -> S') -> SpecsDSL S T
| SL_Restrict: SpecsDSL S T -> (S -> Prop) -> SpecsDSL S T
| SL_Union: SpecsDSL S T -> SpecsDSL S T -> SpecsDSL S T
| SL_Sequence `{Monoid T}: SpecsDSL S T -> SpecsDSL S T -> SpecsDSL S T
(* | SL_Fixpoint: (FormatM S T -> SpecsDSL S T) -> SpecsDSL S T *)
.

Fixpoint SpecsDSL_denote {S T} (dsl : SpecsDSL S T) : FormatM S T :=
  match dsl with
  | SL_Arbitrary fmt => fmt
  | SL_Compose _ fmt1 fmt2 => Compose_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  | SL_Projection _ fmt1 f => Projection_Format (SpecsDSL_denote fmt1) f
  | SL_Restrict fmt1 P => Restrict_Format P (SpecsDSL_denote fmt1)
  | SL_Union fmt1 fmt2 => Union_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  | SL_Sequence _ fmt1 fmt2 => Sequence_Format (SpecsDSL_denote fmt1) (SpecsDSL_denote fmt2)
  (* | SL_Fixpoint F => Fix_Format (fun rec => SpecsDSL_denote (F rec)) *)
  end.

(* Annotated formats *)
Inductive ASpecsDSL S T : Type :=
| ASL_None `{Monoid T}: SpecsDSL S T -> ASpecsDSL S T
| ASL_Right `{Monoid T}: SpecsDSL S T -> ASpecsDSL S T
| ASL_Left `{Monoid T}: SpecsDSL S T -> ASpecsDSL S T.

Definition ASpecsDSL_denote_source_type {S T} (adsl : ASpecsDSL S T) : Type :=
  match adsl with
  | ASL_None _ _ => S
  | _ => S * T
  end.

Definition ASpecsDSL_denote_type {S T} (adsl : ASpecsDSL S T) : Type :=
  FormatM (ASpecsDSL_denote_source_type adsl) T.

Fixpoint ASpecsDSL_denote {S T} (adsl : ASpecsDSL S T) : ASpecsDSL_denote_type adsl :=
  match adsl with
  | ASL_None _ dsl => SpecsDSL_denote dsl
  | ASL_Right _ dsl => fun st t => exists t1, (SpecsDSL_denote dsl) (fst st) ∋ t1 /\ t = mappend t1 (snd st)
  | ASL_Left _ dsl => fun st t => exists t2, (SpecsDSL_denote dsl) (fst st) ∋ t2 /\ t = mappend (snd st) t2
  end.

(* (SL_Arbitrary IdentityFormat) might not be a good idea, since we do not have
   the eliminator for any arbitrary formats in FormatM, which means we cannot
   pattern match IdentityFormat. We should possibly have a constructor called
   SL_Primitive and collect all the built-in formats there. *)
Fixpoint ASpecsDSL_to_SpecsDSL {S T} (adsl : ASpecsDSL S T)
  : SpecsDSL (ASpecsDSL_denote_source_type adsl) T :=
  match adsl with
  | ASL_None _ dsl => dsl
  | ASL_Right _ dsl => SL_Sequence (SL_Projection dsl fst)
                                  (SL_Projection (SL_Arbitrary IdentityFormat) snd)
  | ASL_Left _ dsl => SL_Sequence (SL_Projection (SL_Arbitrary IdentityFormat) snd)
                                 (SL_Projection dsl fst)
  end.

Lemma ASpecsDSL_to_SpecsDSL_denote_equiv {S T} (adsl : ASpecsDSL S T)
  : EquivFormat (SpecsDSL_denote (ASpecsDSL_to_SpecsDSL adsl))
                (ASpecsDSL_denote adsl).
Proof.
  destruct adsl; simpl.
  - reflexivity.
  - rewrite !Projection_Format_equiv.
    rewrite Sequence_Format_equiv. unfold Sequence_Format'. unfold IdentityFormat.
    split; intros ? ?; rewrite unfold_computes in *;
      destruct_ex; split_and; subst;
        repeat econstructor; eauto.
    f_equal; auto.
  - rewrite !Projection_Format_equiv.
    rewrite Sequence_Format_equiv. unfold Sequence_Format'. unfold IdentityFormat.
    split; intros ? ?; rewrite unfold_computes in *;
      destruct_ex; split_and; subst;
        repeat econstructor; eauto.
    f_equal; auto.
Qed.