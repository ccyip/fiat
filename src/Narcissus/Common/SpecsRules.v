Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL
        Fiat.Narcissus.Common.SpecsSeq
        Fiat.Computation.FixComp.

Require MoreVectors.Vector.

Import LeastFixedPointFun.

Unset Implicit Arguments.

Definition GammaT := list Type.
Definition GammaF (gamma : GammaT) := cfunType gamma.
Definition ConstrT gamma S := GammaF gamma (S -> Prop).
Definition DecT gamma S T := GammaF gamma (DecodeM S T).
Definition DecT' gamma S T n := GammaF gamma (Vector.t nat n -> DecodeM S T).

Definition GammaF_fmap {S T} (f : S -> T)
  : forall {gamma : GammaT}, GammaF gamma S -> GammaF gamma T :=
  fix rec gamma :=
    match gamma with
    | [] => fun s => f s
    | A :: gamma' => fun s => fun a => rec gamma' (s a)
    end.

Definition GammaF_fmap2 {S S' T} (f : S -> S' -> T)
  : forall {gamma : GammaT}, GammaF gamma S -> GammaF gamma S' -> GammaF gamma T :=
  fix rec gamma :=
    match gamma with
    | [] => fun s s' => f s s'
    | A :: gamma' => fun s s' => fun a => rec gamma' (s a) (s' a)
    end.

Definition compose_constr {S A gamma} (fmt : FormatDSL S A) (C : ConstrT gamma S)
  : ConstrT gamma A :=
  GammaF_fmap
    (fun C =>
       fun a => exists s, (FormatDSL_denote fmt) s ∋ a /\ C s) C.

Definition Union_Decode' {S T} P0 dec1 dec2 := @Union_Decode S T dec1 dec2 P0.

Definition Compose_Decode' {S T S'} (dec1 : DecodeM (S'*T) T) (dec2 : DecodeM S S')
  : DecodeM (S*T) T :=
  fun t => st <- dec1 t; a <- dec2 (fst st); Some (a, (snd st)).

Definition Lift_Decode {S T} `{Monoid T} (dec : DecodeM S T) : DecodeM (S*T) T :=
  fun t => s <- dec t; Some (s, mempty).

Inductive FormatSeq_PickOne :
  forall {S T} (seq seq' : FormatSeq S T),
    Fin.t (FormatSeq_nodes_num seq) -> Fin.t (FormatSeq_nodes_num seq) ->
    bool -> FormatDSL S T -> bool -> Prop :=

| PO_Single: forall S T b1 b2 (fmt : FormatDSL S T),
    orb b1 b2 = true ->
    FormatSeq_PickOne {| FS_Segs := [{| FS_Known := b1; FS_Fmt := fmt; FS_Used := false |}];
                         FS_LastKnown := b2 |}
                      {| FS_Segs := [{| FS_Known := true; FS_Fmt := fmt; FS_Used := true |}];
                         FS_LastKnown := true |}
                      Fin.F1 (Fin.FS Fin.F1) b1 fmt b2

| PO_Tail: forall S T b1 b2 (fmt fmt' : FormatDSL S T) segs lk u,
    orb b1 b2 = true ->
    FormatSeq_PickOne {| FS_Segs := {| FS_Known := b1; FS_Fmt := fmt; FS_Used := false |}
                                      :: {| FS_Known := b2; FS_Fmt := fmt'; FS_Used := u |}
                                      :: segs ;
                         FS_LastKnown := lk |}
                      {| FS_Segs := {| FS_Known := true; FS_Fmt := fmt; FS_Used := true |}
                                      :: {| FS_Known := true; FS_Fmt := fmt'; FS_Used := u |}
                                      :: segs ;
                         FS_LastKnown := lk |}
                      Fin.F1 (Fin.FS Fin.F1) b1 fmt b2

| PO_Head: forall S T segs lk segs' lk' i j b1 b2 (fmt : FormatDSL S T) seg,
    FormatSeq_PickOne {| FS_Segs := segs; FS_LastKnown := lk |}
                      {| FS_Segs := segs'; FS_LastKnown := lk' |}
                      i j b1 fmt b2 ->
    FormatSeq_PickOne {| FS_Segs := seg :: segs; FS_LastKnown := lk |}
                      {| FS_Segs := seg :: segs'; FS_LastKnown := lk' |}
                      (Fin.FS i) (Fin.FS j) b1 fmt b2

.

Inductive FormatDSL_CorrectDecoder :
  forall {S T A} (gamma : GammaT), ConstrT gamma S -> FormatDSL S A ->
                    FormatDSL S T -> DecT gamma A T -> Prop :=

| CD_Union: forall S T A gamma C fmt1 fmt2 dec1 dec2
              (R : FormatDSL S A)
              (P0 : T -> bool),
    FormatDSL_CorrectDecoder gamma C R fmt1 dec1 ->
    FormatDSL_CorrectDecoder gamma C R fmt2 dec2 ->
    (forall s t,
        FormatDSL_denote (FL_Union fmt1 fmt2) s ∋ t ->
        if P0 t then FormatDSL_denote fmt1 s ∋ t
        else FormatDSL_denote fmt2 s ∋ t) ->
    FormatDSL_CorrectDecoder
      gamma C R (FL_Union fmt1 fmt2)
      (GammaF_fmap2 (Union_Decode' P0) dec1 dec2)

| CD_Compose1: forall S A T A' gamma C
                 (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                 dec1 dec2
                 (R : FormatDSL S A'),
    FormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             (FL_Arbitrary IdentityFormat)
                             fmt1 dec1 ->
    FormatDSL_CorrectDecoder gamma C R fmt2 dec2 ->
    FormatDSL_CorrectDecoder gamma C R (FL_Compose fmt1 fmt2)
                             (GammaF_fmap2 Compose_Decode dec1 dec2)

| CD_Compose2: forall S A T A' gamma C
                 (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                 dec1 (R : FormatDSL A A'),
    FormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             R fmt1 dec1 ->
    (* Need a better way to handle this comparison. *)
    ~(R ~= FL_Arbitrary (@IdentityFormat A)) ->
    FormatDSL_CorrectDecoder gamma C (FL_Compose R fmt2) (FL_Compose fmt1 fmt2) dec1

| CD_Sequence: forall S A T `{Monoid T} gamma C
                 (fmt1 fmt2 : FormatDSL S T)
                 seq dec
                 (R : FormatDSL S A) l seq',
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_know_first (FormatSeq_lift l) = Some seq' ->
    FormatSeq_know_last seq' = seq ->
    FormatSeq_CorrectDecoder gamma C R seq dec ->
    FormatDSL_CorrectDecoder gamma C R (FL_Sequence fmt1 fmt2)
                             (GammaF_fmap (fun dec t =>
                                             let v := Vector.repeat (bin_measure t) (FormatSeq_nodes_num seq) in
                                             st <- dec (Vector.replace v Fin.F1 0) t;
                                               Some (fst st))
                                          dec)

with AFormatDSL_CorrectDecoder :
       forall {S T A} (gamma : GammaT), ConstrT gamma S -> FormatDSL S A ->
                         AFormatDSL S T -> DecT gamma (A*T) T -> Prop :=

| CDN_Lift: forall S T `{Monoid T} A gamma C fmt dec (R : FormatDSL S A),
    FormatDSL_CorrectDecoder gamma C R fmt dec ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_None fmt)
                              (GammaF_fmap Lift_Decode dec)

| CDR_Union: forall S T `{Monoid T} A gamma C fmt1 fmt2 dec1 dec2
               (R : FormatDSL S A)
               (P0 : T -> bool),
    AFormatDSL_CorrectDecoder gamma C R (AFL_Right fmt1) dec1 ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Right fmt2) dec2 ->
    (forall s t t',
        FormatDSL_denote (FL_Union fmt1 fmt2) s ∋ t ->
        if P0 (mappend t t') then FormatDSL_denote fmt1 s ∋ t
        else FormatDSL_denote fmt2 s ∋ t) ->
    AFormatDSL_CorrectDecoder
      gamma C R (AFL_Right (FL_Union fmt1 fmt2))
      (GammaF_fmap2 (Union_Decode' P0) dec1 dec2)

| CDL_Union: forall S T `{Monoid T} A gamma C fmt1 fmt2 dec1 dec2
               (R : FormatDSL S A)
               (P0 : T -> bool),
    AFormatDSL_CorrectDecoder gamma C R (AFL_Left fmt1) dec1 ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Left fmt2) dec2 ->
    (forall s t t',
        FormatDSL_denote (FL_Union fmt1 fmt2) s ∋ t ->
        if P0 (mappend t' t) then FormatDSL_denote fmt1 s ∋ t
        else FormatDSL_denote fmt2 s ∋ t) ->
    AFormatDSL_CorrectDecoder
      gamma C R (AFL_Left (FL_Union fmt1 fmt2))
      (GammaF_fmap2 (Union_Decode' P0) dec1 dec2)

| CDR_Compose1: forall S A T A' gamma C
                  (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                  dec1 dec2
                  (R : FormatDSL S A'),
    AFormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             (FL_Arbitrary IdentityFormat)
                             (AFL_Right fmt1) dec1 ->
    FormatDSL_CorrectDecoder gamma C R fmt2 dec2 ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Right (FL_Compose fmt1 fmt2))
                              (GammaF_fmap2 Compose_Decode' dec1 dec2)

| CDL_Compose1: forall S A T A' gamma C
                  (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                  dec1 dec2
                  (R : FormatDSL S A'),
    AFormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             (FL_Arbitrary IdentityFormat)
                             (AFL_Left fmt1) dec1 ->
    FormatDSL_CorrectDecoder gamma C R fmt2 dec2 ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Left (FL_Compose fmt1 fmt2))
                              (GammaF_fmap2 Compose_Decode' dec1 dec2)

| CDR_Compose2: forall S A T A' gamma C
                  (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                  dec1 (R : FormatDSL A A'),
    AFormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             R (AFL_Right fmt1) dec1 ->
    ~(R ~= FL_Arbitrary (@IdentityFormat A)) ->
    AFormatDSL_CorrectDecoder gamma C (FL_Compose R fmt2) (AFL_Right (FL_Compose fmt1 fmt2)) dec1

| CDL_Compose2: forall S A T A' gamma C
                  (fmt1 : FormatDSL A T) (fmt2 : FormatDSL S A)
                  dec1 (R : FormatDSL A A'),
    AFormatDSL_CorrectDecoder gamma (compose_constr fmt2 C)
                             R (AFL_Left fmt1) dec1 ->
    ~(R ~= FL_Arbitrary (@IdentityFormat A)) ->
    AFormatDSL_CorrectDecoder gamma C (FL_Compose R fmt2) (AFL_Left (FL_Compose fmt1 fmt2)) dec1

| CDR_Sequence: forall S A T `{Monoid T} gamma C
                 (fmt1 fmt2 : FormatDSL S T)
                 seq dec
                 (R : FormatDSL S A) l seq',
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_know_first (FormatSeq_lift l) = Some seq' ->
    FormatSeq_know_last seq' = seq ->
    FormatSeq_CorrectDecoder gamma C R seq dec ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Right (FL_Sequence fmt1 fmt2))
                             (GammaF_fmap (fun dec t =>
                                             let v := Vector.repeat 0 (FormatSeq_nodes_num seq) in
                                             dec v t)
                                          dec)

| CDL_Sequence: forall S A T `{Monoid T} gamma C
                 (fmt1 fmt2 : FormatDSL S T)
                 seq dec
                 (R : FormatDSL S A) l seq',
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_know_first (FormatSeq_lift l) = Some seq' ->
    FormatSeq_know_last seq' = seq ->
    FormatSeq_CorrectDecoder gamma C R seq dec ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Left (FL_Sequence fmt1 fmt2))
                             (GammaF_fmap (fun dec t =>
                                             let v := Vector.repeat (bin_measure t) (FormatSeq_nodes_num seq) in
                                             dec v t)
                                          dec)


with FormatSeq_CorrectDecoder :
       forall {S T A} (gamma : GammaT), ConstrT gamma S -> FormatDSL S A ->
                                   forall seq : FormatSeq S T,
                                     DecT' gamma (A*T) T (FormatSeq_nodes_num seq) -> Prop :=
.
