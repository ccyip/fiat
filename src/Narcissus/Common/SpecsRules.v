Require Export
        Fiat.Narcissus.Common.SpecsSimpl
        Fiat.Narcissus.BaseFormats
        Fiat.Narcissus.Common.SpecsDSL
        Fiat.Narcissus.Common.SpecsSeq
        Fiat.Computation.FixComp.

Import LeastFixedPointFun.

Unset Implicit Arguments.

Definition GammaT := list Type.
Definition GammaF (gamma : GammaT) := cfunType gamma.
Definition ConstrT gamma S := GammaF gamma (S -> Prop).
Definition DecT gamma S T := GammaF gamma (DecodeM S T).
Definition OffsetsT := total_map nat nat.
Definition DecT' gamma S T := GammaF gamma (OffsetsT -> DecodeM S T).

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

Definition GammaF_fmap2' {S S' A' T} (f : S -> (A' -> S') -> T)
  : forall {gamma : GammaT}, GammaF gamma S -> GammaF (A' :: gamma) S' -> GammaF gamma T :=
  fix rec gamma :=
    match gamma with
    | [] => fun s s' => f s s'
    | A :: gamma' => fun s s' => fun a => rec gamma' (s a) (fun a' => s' a' a)
    end.

Definition compose_constr {S A gamma} (fmt : FormatDSL S A) (C : ConstrT gamma S)
  : ConstrT gamma A :=
  GammaF_fmap
    (fun C =>
       fun a => exists s, (FormatDSL_denote fmt) s ∋ a /\ C s) C.

Definition conj_constr {S A gamma} (R : FormatDSL S A) (C : ConstrT gamma S)
  : ConstrT (A :: gamma) S :=
  fun a => GammaF_fmap
           (fun C => fun s => C s /\ (FormatDSL_denote R) s ∋ a) C.

Definition Union_Decode' {S T} P0 dec1 dec2 := @Union_Decode S T dec1 dec2 P0.

Definition Compose_Decode' {S T S'} (dec1 : DecodeM (S'*T) T) (dec2 : DecodeM S S')
  : DecodeM (S*T) T :=
  fun t => st <- dec1 t; a <- dec2 (fst st); Some (a, (snd st)).

Definition Lift_Decode {S T} `{Monoid T} (dec : DecodeM S T) : DecodeM (S*T) T :=
  fun t => s <- dec t; Some (s, mempty).


Open Scope maps_scope.

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
                 (R : FormatDSL S A)
                 l dec,
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_CorrectDecoder
      gamma C R
      (FormatSeq_know_nth (FormatSeq_know_nth (FormatSeq_lift l) 0) (length l))
      dec ->
    FormatDSL_CorrectDecoder gamma C R (FL_Sequence fmt1 fmt2)
                             (GammaF_fmap (fun dec t =>
                                             st <- dec (t_update {--> 0} (length l) (bin_measure t)) t;
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
                 (R : FormatDSL S A)
                 l dec,
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_CorrectDecoder
      gamma C R
      (FormatSeq_know_nth (FormatSeq_lift l) 0)
      dec ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Right (FL_Sequence fmt1 fmt2))
                              (GammaF_fmap (fun dec t =>
                                              dec {--> 0} t)
                                           dec)

| CDL_Sequence: forall S A T `{Monoid T} gamma C
                 (fmt1 fmt2 : FormatDSL S T)
                 (R : FormatDSL S A)
                 l dec,
    FormatDSL_Seq_Sim (FL_Sequence fmt1 fmt2) l ->
    FormatSeq_CorrectDecoder
      gamma C R
      (FormatSeq_know_nth (FormatSeq_lift l) (length l))
      dec ->
    AFormatDSL_CorrectDecoder gamma C R (AFL_Left (FL_Sequence fmt1 fmt2))
                              (GammaF_fmap (fun dec t =>
                                              dec (t_update {--> 0} (length l) (bin_measure t)) t)
                                           dec)

with FormatSeq_CorrectDecoder :
       forall {S T A} (gamma : GammaT), ConstrT gamma S -> FormatDSL S A -> FormatSeq S T ->
                                   DecT' gamma (A*T) T -> Prop :=

| CDN_Step: forall A A1 T `{SliceMonoidOpt T} A2 gamma C seq i
              dec1 dec2
              (R1 : FormatDSL A A1) (R2 : FormatDSL A A2),
    FS_Used (seq i) = false ->
    FS_Known (seq i) = true ->
    FS_Known (seq (S i)) = true ->
    AFormatDSL_CorrectDecoder gamma C R1 (AFL_None (FS_Fmt (seq i))) dec1 ->
    FormatSeq_CorrectDecoder (A1 :: gamma) (conj_constr R1 C) R2
                             (t_update
                                seq
                                i {| FS_Fmt := FS_Fmt (seq i);
                                     FS_Used := true;
                                     FS_Known := true |})
                             dec2 ->
    FormatSeq_CorrectDecoder gamma C R2 seq
                             (GammaF_fmap2'
                                (fun dec1 dec2 off t =>
                                   st <- dec1 (mslice t (off i) (off (S i)));
                                     dec2 (fst st) off t)
                                dec1 dec2)

| CDR_Step1: forall A A1 T `{SliceMonoidOpt T} A2 gamma C seq i k
               dec1 dec2
               (R1 : FormatDSL A A1) (R2 : FormatDSL A A2),
    FS_Used (seq i) = false ->
    FS_Known (seq i) = true ->
    FS_Known (seq (S i)) = false ->
    FormatSeq_is_next_known seq i k ->
    AFormatDSL_CorrectDecoder gamma C R1 (AFL_Right (FS_Fmt (seq i))) dec1 ->
    FormatSeq_CorrectDecoder (A1 :: gamma) (conj_constr R1 C) R2
                             (t_update
                                (t_update seq i
                                          {| FS_Fmt := FS_Fmt (seq i);
                                             FS_Used := true;
                                             FS_Known := true |}) (S i)
                                {| FS_Fmt := FS_Fmt (seq (S i));
                                   FS_Used := FS_Used (seq (S i));
                                   FS_Known := true |})
                             dec2 ->
    FormatSeq_CorrectDecoder gamma C R2 seq
                             (GammaF_fmap2'
                                (fun dec1 dec2 off t =>
                                   st <- dec1 (mslice t (off i) (off k));
                                     dec2 (fst st)
                                          (t_update off (S i)
                                                    (off k - bin_measure (snd st)))
                                          t)
                                dec1 dec2)

| CDR_Step2: forall A A1 T `{SliceMonoidOpt T} A2 gamma C seq i
               dec1 dec2
               (R1 : FormatDSL A A1) (R2 : FormatDSL A A2),
    FS_Used (seq i) = false ->
    FS_Known (seq i) = true ->
    FS_Known (seq (S i)) = false ->
    FormatSeq_no_next_known seq i ->
    AFormatDSL_CorrectDecoder gamma C R1 (AFL_Right (FS_Fmt (seq i))) dec1 ->
    FormatSeq_CorrectDecoder (A1 :: gamma) (conj_constr R1 C) R2
                             (t_update
                                (t_update seq i
                                          {| FS_Fmt := FS_Fmt (seq i);
                                             FS_Used := true;
                                             FS_Known := true |}) (S i)
                                {| FS_Fmt := FS_Fmt (seq (S i));
                                   FS_Used := FS_Used (seq (S i));
                                   FS_Known := true |})
                             dec2 ->
    FormatSeq_CorrectDecoder gamma C R2 seq
                             (GammaF_fmap2'
                                (fun dec1 dec2 off t =>
                                   st <- dec1 (mslice t (off i) (bin_measure t));
                                     dec2 (fst st)
                                          (t_update off (S i)
                                                    (bin_measure t - bin_measure (snd st)))
                                          t)
                                dec1 dec2)

| CDL_Step1: forall A A1 T `{SliceMonoidOpt T} A2 gamma C seq i k
               dec1 dec2
               (R1 : FormatDSL A A1) (R2 : FormatDSL A A2),
    FS_Used (seq i) = false ->
    FS_Known (seq i) = false ->
    FS_Known (seq (S i)) = true ->
    FormatSeq_is_prev_known seq (S i) k ->
    AFormatDSL_CorrectDecoder gamma C R1 (AFL_Left (FS_Fmt (seq i))) dec1 ->
    FormatSeq_CorrectDecoder (A1 :: gamma) (conj_constr R1 C) R2
                             (t_update seq i
                                       {| FS_Fmt := FS_Fmt (seq i);
                                          FS_Used := true;
                                          FS_Known := true |})
                             dec2 ->
    FormatSeq_CorrectDecoder gamma C R2 seq
                             (GammaF_fmap2'
                                (fun dec1 dec2 off t =>
                                   st <- dec1 (mslice t (off k) (off (S i)));
                                     dec2 (fst st)
                                          (t_update off i
                                                    (off k + bin_measure (snd st)))
                                          t)
                                dec1 dec2)

| CDL_Step2: forall A A1 T `{SliceMonoidOpt T} A2 gamma C seq i
               dec1 dec2
               (R1 : FormatDSL A A1) (R2 : FormatDSL A A2),
    FS_Used (seq i) = false ->
    FS_Known (seq i) = false ->
    FS_Known (seq (S i)) = true ->
    FormatSeq_no_prev_known seq (S i) ->
    AFormatDSL_CorrectDecoder gamma C R1 (AFL_Left (FS_Fmt (seq i))) dec1 ->
    FormatSeq_CorrectDecoder (A1 :: gamma) (conj_constr R1 C) R2
                             (t_update seq i
                                       {| FS_Fmt := FS_Fmt (seq i);
                                          FS_Used := true;
                                          FS_Known := true |})
                             dec2 ->
    FormatSeq_CorrectDecoder gamma C R2 seq
                             (GammaF_fmap2'
                                (fun dec1 dec2 off t =>
                                   st <- dec1 (mslice t 0 (off (S i)));
                                     dec2 (fst st)
                                          (t_update off i
                                                    (bin_measure (snd st)))
                                          t)
                                dec1 dec2)

| CD_Done: forall S A T `{Monoid T} gamma C seq dec (R : FormatDSL S A),
    FormatDSL_CorrectDecoder gamma C R (FL_Arbitrary UnitFormat) dec ->
    FormatSeq_all_done seq ->
    FormatSeq_CorrectDecoder gamma C R seq
                             (GammaF_fmap
                                (fun dec _ _ => s <- dec tt; Some (s, mempty))
                             dec)

.
