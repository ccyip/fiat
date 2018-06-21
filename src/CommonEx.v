Require Import
        FunctionalExtensionality
        Coq.Sets.Image
        Coq.omega.Omega
        Coq.Logic.Eqdep_dec.

Require Import
        Fiat.Common
        Fiat.Computation
        Fiat.Computation.Core
        Fiat.Computation.FixComp
        Fiat.Narcissus.Common.Specs
        Fiat.Narcissus.Common.ComposeOpt.

Import FixComp.LeastFixedPointFun.

Ltac solve_by_extensionality :=
  repeat let a := fresh in
         extensionality a; auto.

Ltac solve_extensionality' f g :=
  replace g with f by solve_by_extensionality;
  auto.

(* :TODO: make it better *)
Ltac solve_extensionality :=
  intros;
  match goal with
  | H : forall a1, ?f a1 = ?g a1 |- _ => solve_extensionality' f g
  | H : forall a1 a2, ?f a1 a2 = ?g a1 a2 |- _ => solve_extensionality' f g
  | H : forall a1 a2 a3, ?f a1 a2 a3 = ?g a1 a2 a3 |- _ => solve_extensionality' f g
  end.

Ltac decode_opt_to_inv :=
  repeat match goal with
         | H : _ = Some (_, _, _) |- _ =>
           apply DecodeBindOpt2_inv in H; destruct H as [? [? [? [? ?]]]]
         | H : Some (_, _, _) = Some (_, _, _) |- _ => inversion H; clear H
         | H : Some (_, _, _) = _ |- _ => symmetry in H
         end.

Ltac computes_to_inv2 :=
  unfold compose, Bind2 in *; computes_to_inv;
  repeat match goal with
         | v : _ * _ |- _ => destruct v
         end;
  simpl fst in *; simpl snd in *;
  repeat match goal with
         | H : (_, _) = (_, _) |- _ => inversion H; clear H; subst
         end.

Ltac fill_ind_h' t f :=
  match t with
  | (_ -> ?t') => fill_ind_h' t' uconstr:(f _)
  | _ => f
  end.
Ltac fill_ind_h f :=
  let t := type of f in
  fill_ind_h' t f.

Ltac existT_eq_dec :=
    match goal with
    | [ H : existT _ _ _ = existT _ _ _ |- _ ] =>
      apply inj_pair2_eq_dec in H; [| clear H; try apply Nat.eq_dec]
    end.

Ltac gen_eq_rect :=
  match goal with
  | _ : _ |- context [eq_rect _ _ _ _ ?e] => generalize e; try destruct 0
  end.

Ltac choose_br n :=
  match n with
  | O => try left
  | S ?n' => right; choose_br n'
  end.

Ltac destruct_many :=
  repeat first [match goal with
                | H : ?a \/ ?b |- _ => destruct H
                end |
                match goal with
                | [ H : ex _ |- _ ] => destruct H
                end |
                match goal with
                | H : ?a /\ ?b |- _ => destruct H
                end].

Definition type_cast {A B : Type} (pf : A = B) (v : A) : B.
Proof.
  rewrite <- pf.
  exact v.
Defined.

Definition type_cast_r {A B : Type} (pf : B = A) (v : A) : B.
Proof.
  rewrite pf.
  exact v.
Defined.

Import Ensembles.

Lemma fun_compose_format_correct
      {A A' B} {cache : Cache} {monoid : Monoid B}
      {P : CacheDecode -> Prop}
      {P_inv : (CacheDecode -> Prop) -> Prop}
      (f : A -> A') (f_inv : A' -> A)
      (im : A' -> bool)
      (predicate : A -> Prop)
      (predicate' : A' -> Prop)
      (predicate_rest : A -> B -> Prop)
      (predicate_rest' : A' -> B -> Prop)
      (format : FormatM A' B)
      (decode : DecodeM A' B)
      (f_OK : forall a, predicate a -> f_inv (f a) = a)
      (im_OK : forall a', decides (im a') (In _ (Im _ _ predicate f) a'))
      (P_inv_OK : cache_inv_Property P P_inv)
      (decode_correct :
         cache_inv_Property P P_inv
         -> CorrectDecoder
             monoid predicate'
             predicate_rest'
             format decode P)
      (predicate_OK : forall a,
          predicate a ->
          predicate' (f a))
      (predicate_rest_OK : forall a b,
          predicate a ->
          predicate_rest a b ->
          predicate_rest' (f a) b)
  : CorrectDecoder
      monoid
      predicate
      predicate_rest
      (fun a ce => format (f a) ce)
      (fun b cd => `(a', b', cd') <- decode b cd;
                  if im a' then Some (f_inv a', b', cd') else None)
      P.
Proof.
  split; intros. {
    edestruct decode_correct as [[? [? [? ?]]] _]; eauto.
    eexists. repeat split; eauto.
    rewrite H3. simpl.
    specialize (im_OK (f data)).
    destruct im. repeat progress f_equal. auto.
    simpl in im_OK. exfalso. auto with sets.
  } {
    decode_opt_to_inv.
    edestruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
    specialize (im_OK x).
    destruct im; try easy. simpl in im_OK.
    injections.
    apply Im_inv in im_OK. destruct im_OK as [? [? ?]].
    specialize (f_OK _ H2). subst. rewrite f_OK.
    split; eauto. eexists _, _. repeat split; eauto.
  }
Qed.

Lemma shrink_format_correct
      {A B} {cache : Cache} {monoid : Monoid B}
      {P : CacheDecode -> Prop}
      {P_inv : (CacheDecode -> Prop) -> Prop}
      (predicate : A -> Prop) (predicate_rest : A -> B -> Prop)
      (predicate' : A -> Prop) (predicate_rest' : A -> B -> Prop)
      (format : FormatM A B)
      (decode : DecodeM A B)
      (predicate_dec : A -> bool)
      (predicate_dec_OK : forall a, decides (predicate_dec a) (predicate a))
      (P_inv_OK : cache_inv_Property P P_inv)
      (decode_correct :
         cache_inv_Property P P_inv ->
         CorrectDecoder monoid predicate' predicate_rest' format decode P)
      (predicate_OK : forall a, predicate a -> predicate' a)
      (predicate_rest_OK : forall a b, predicate a -> predicate_rest a b -> predicate_rest' a b)
  : CorrectDecoder
      monoid predicate predicate_rest
      format
      (fun b cd => `(a, b', cd') <- decode b cd;
                  if predicate_dec a then Some (a, b', cd') else None)
      P.
Proof.
  split; intros. {
    specialize (predicate_dec_OK data).
    edestruct decode_correct as [[? [? [? ?]]] _]; eauto.
    eexists. rewrite H3. simpl. destruct predicate_dec; eauto.
    congruence.
  } {
    decode_opt_to_inv.
    specialize (predicate_dec_OK x). destruct predicate_dec; try easy.
    injections.
    edestruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
    split; auto. eexists _, _. repeat split; eauto.
  }
Qed.

Lemma shrink_format_correct_True
      {A B} {cache : Cache} {monoid : Monoid B}
      {P : CacheDecode -> Prop}
      {P_inv : (CacheDecode -> Prop) -> Prop}
      (predicate : A -> Prop) (predicate_rest : A -> B -> Prop)
      (predicate' : A -> Prop) (predicate_rest' : A -> B -> Prop)
      (format : FormatM A B)
      (decode : DecodeM A B)
      (P_inv_OK : cache_inv_Property P P_inv)
      (decode_correct :
         cache_inv_Property P P_inv ->
         CorrectDecoder monoid predicate' predicate_rest' format decode P)
      (predicate_OK : forall a, predicate a)
      (predicate_OK' : forall a, predicate' a)
      (predicate_rest_OK : forall a b, predicate_rest a b -> predicate_rest' a b)
  : CorrectDecoder
      monoid predicate predicate_rest format decode P.
Proof.
  split; intros. {
    edestruct decode_correct as [[? [? [? ?]]] _]; eauto.
  } {
    edestruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
    split; auto. eexists _, _. repeat split; eauto.
  }
Qed.

Definition FueledFix'' {A} (F : A -> A) (d : A)
  : nat -> A :=
  fix rec n :=
    match n with
    | O => d
    | S n' => F (rec n')
    end.

Theorem FueledFix_bottom_eq {A} (F : A -> A) (d : A)
  : forall n, FueledFix'' F d (S n) = FueledFix'' F (F d) n.
Proof.
  induction 0; eauto.
  simpl in *. f_equal. eauto.
Qed.

Definition FueledFix' {A B C} (F : (B -> C -> option A) -> B -> C -> option A) :=
  FueledFix'' F (fun _ _ => None).

Definition FueledFix {A B C}
           {monoid : Monoid B}
           (F : (B -> C -> option A) -> B -> C -> option A)
  : B -> C -> option A :=
  fun b => FueledFix' F (S (bin_measure b)) b.

Theorem FueledFix_continuous {A B C} (F : (B -> C -> option A) -> B -> C -> option A)
  : (forall n a b c,
        FueledFix' F n b c = Some a ->
        FueledFix' F (S n) b c = Some a) ->
    forall n n',
      n <= n' ->
      forall a b c,
        FueledFix' F n b c = Some a ->
        FueledFix' F n' b c = Some a.
Proof.
  intros. induction H0; eauto.
Qed.

Definition FueledFixP' {A B C D} (F : (D -> B -> C -> option A) -> D -> B -> C -> option A) :=
  FueledFix'' F (fun _ _ _ => None).

Definition FueledFixP {A B C D}
           {monoid : Monoid B}
           (F : (D -> B -> C -> option A) -> D -> B -> C -> option A)
  : D -> B -> C -> option A :=
  fun d b => FueledFixP' F (S (bin_measure b)) d b.

Theorem FueledFixP_continuous {A B C D} (F : (D -> B -> C -> option A) -> D -> B -> C -> option A)
  : (forall n a b c d,
        FueledFixP' F n d b c = Some a ->
        FueledFixP' F (S n) d b c = Some a) ->
    forall n n',
      n <= n' ->
      forall a b c d,
        FueledFixP' F n d b c = Some a ->
        FueledFixP' F n' d b c = Some a.
Proof.
  intros. induction H0; eauto.
Qed.

Section Fix_format_correct.

  Context {A B : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.
  Context {P : CacheDecode -> Prop}.
  Context {P_inv : (CacheDecode -> Prop) -> Prop}.
  Variable format_body : funType [A; CacheFormat] (B * CacheFormat) ->
                         funType [A; CacheFormat] (B * CacheFormat).
  Variable decode_body : (B -> CacheDecode -> option (A * B * CacheDecode)) ->
                         B -> CacheDecode -> option (A * B * CacheDecode) .
  Variable format_body_OK : Frame.monotonic_function format_body.
  Variable predicate : A -> Prop.
  Variable predicate_rest : A -> B -> Prop.
  Variable P_inv_OK : cache_inv_Property P P_inv.

  Lemma fix_format_correct'
        (bound : B -> nat)         (* bound is usually bin_measure. *)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bound b < n ->
                   CorrectDecoder'
                     monoid predicate predicate_rest
                     (LeastFixedPoint format_body) (FueledFix' decode_body n) P b) ->
             forall b, bound b < S n ->
                  CorrectDecoder'
                    monoid predicate predicate_rest
                    (format_body (LeastFixedPoint format_body)) (decode_body (FueledFix' decode_body n)) P b)
    : forall b n,
      bound b < n ->
      CorrectDecoder'
        monoid predicate predicate_rest
        (LeastFixedPoint format_body) (FueledFix' decode_body n) P b.
  Proof.
    specialize (decode_body_correct P_inv_OK).
    intros.
    generalize dependent b.
    induction n; simpl; intros. {
      inversion H.
    } {
      split; intros. {
        eapply (unroll_LeastFixedPoint format_body_OK) in H3; eauto.
        eapply decode_body_correct; eauto.
      } {
        eapply decode_body_correct in H2; eauto.
        destruct_many.
        eapply (unroll_LeastFixedPoint' format_body_OK) in H3; eauto.
        eauto 8.
      }
    }
  Qed.

  (* :TODO: make it stronger? *)
  Lemma fix_format_correct
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bin_measure b < n ->
                   CorrectDecoder'
                     monoid predicate predicate_rest
                     (LeastFixedPoint format_body) (FueledFix' decode_body n) P b) ->
             forall b, bin_measure b < S n ->
                  CorrectDecoder'
                    monoid predicate predicate_rest
                    (format_body (LeastFixedPoint format_body)) (decode_body (FueledFix' decode_body n)) P b)
        (decode_body_continuous :
           forall decode,
             (forall b cd a b' cd',
                 decode b cd = Some (a, b', cd') ->
                 decode_body decode b cd = Some (a, b', cd')) ->
             forall b cd a b' cd',
               decode_body decode b cd = Some (a, b', cd') ->
               decode_body (decode_body decode) b cd = Some (a, b', cd'))
    : CorrectDecoder
        monoid predicate predicate_rest
        (LeastFixedPoint format_body) (FueledFix decode_body) P.
  Proof.
    split. 2 : eapply fix_format_correct'; eauto.
    edestruct fix_format_correct' as [H _]; eauto.
    intros. edestruct H; eauto. destruct_many.
    eexists. repeat split; eauto.
    eapply FueledFix_continuous.
    3 : eauto. 2 : rewrite mappend_measure; omega.
    destruct a as [[? ?] ?]. revert a b c. induction n. easy.
    intros. simpl in *. eauto.
  Qed.
  
End Fix_format_correct.

Section Fix_format_correctP.

  Context {A B C : Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.
  Context {P : CacheDecode -> Prop}.
  Context {P_inv : (CacheDecode -> Prop) -> Prop}.
  Variable format_body : funType [A; CacheFormat] (B * CacheFormat) ->
                         funType [A; CacheFormat] (B * CacheFormat).
  Variable decode_body : (C -> B -> CacheDecode -> option (A * B * CacheDecode)) ->
                         C -> B -> CacheDecode -> option (A * B * CacheDecode) .
  Variable format_body_OK : Frame.monotonic_function format_body.
  Variable predicate : C -> A -> Prop.
  Variable predicate_rest : A -> B -> Prop.
  Variable P_inv_OK : cache_inv_Property P P_inv.

  Lemma fix_format_correctP'
        (bound : B -> nat)         (* bound is usually bin_measure. *)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bound b < n ->
                   forall c,
                     CorrectDecoder'
                       monoid (predicate c) predicate_rest
                       (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b) ->
             forall b, bound b < S n ->
                  forall c,
                    CorrectDecoder'
                      monoid (predicate c) predicate_rest
                      (format_body (LeastFixedPoint format_body)) (decode_body (FueledFixP' decode_body n) c) P b)
    : forall b n,
      bound b < n ->
      forall c,
        CorrectDecoder'
          monoid (predicate c) predicate_rest
          (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b.
  Proof.
    specialize (decode_body_correct P_inv_OK).
    intros.
    generalize dependent c.
    generalize dependent b.
    induction n; simpl; intros. {
      inversion H.
    } {
      split; intros. {
        eapply (unroll_LeastFixedPoint format_body_OK) in H3; eauto.
        eapply decode_body_correct; eauto.
      } {
        eapply decode_body_correct in H2; eauto.
        destruct_many.
        eapply (unroll_LeastFixedPoint' format_body_OK) in H3; eauto.
        eauto 8.
      }
    }
  Qed.

  (* :TODO: make it stronger? *)
  Lemma fix_format_correctP
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bin_measure b < n ->
                   forall c,
                     CorrectDecoder'
                       monoid (predicate c) predicate_rest
                       (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b) ->
             forall b, bin_measure b < S n ->
                  forall c,
                    CorrectDecoder'
                      monoid (predicate c) predicate_rest
                      (format_body (LeastFixedPoint format_body)) (decode_body (FueledFixP' decode_body n) c) P b)
        (decode_body_continuous :
           forall decode,
             (forall c b cd a b' cd',
                 decode c b cd = Some (a, b', cd') ->
                 decode_body decode c b cd = Some (a, b', cd')) ->
             forall c b cd a b' cd',
               decode_body decode c b cd = Some (a, b', cd') ->
               decode_body (decode_body decode) c b cd = Some (a, b', cd'))
    : forall c,
      CorrectDecoder
        monoid (predicate c) predicate_rest
        (LeastFixedPoint format_body) (FueledFixP decode_body c) P.
  Proof.
    split. 2 : eapply fix_format_correctP'; eauto.
    edestruct fix_format_correctP' as [H _]; eauto.
    intros. edestruct H; eauto. destruct_many.
    eexists. repeat split; eauto.
    eapply FueledFixP_continuous.
    3 : eauto. 2 : rewrite mappend_measure; omega.
    destruct a as [[? ?] ?]. revert a b c0. induction n. easy.
    intros. simpl in *. eauto.
  Qed.

  Lemma fix_format_correctP2'
        (Pb : B -> Prop)
        (bound : B -> nat)         (* bound is usually bin_measure. *)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, Pb b -> bound b < n ->
                   forall c,
                     CorrectDecoder'
                       monoid (predicate c) predicate_rest
                       (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b) ->
             forall b, Pb b -> bound b < S n ->
                  forall c,
                    CorrectDecoder'
                      monoid (predicate c) predicate_rest
                      (format_body (LeastFixedPoint format_body)) (decode_body (FueledFixP' decode_body n) c) P b)
    : forall b,
      Pb b ->
      forall n,
      bound b < n ->
      forall c,
        CorrectDecoder'
          monoid (predicate c) predicate_rest
          (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b.
  Proof.
    specialize (decode_body_correct P_inv_OK).
    intros ? HPb. intros.
    generalize dependent c.
    generalize dependent b.
    induction n; simpl; intros. {
      inversion H.
    } {
      split; intros. {
        eapply (unroll_LeastFixedPoint format_body_OK) in H3; eauto.
        eapply decode_body_correct; eauto.
      } {
        eapply decode_body_correct in H2; eauto.
        destruct_many.
        eapply (unroll_LeastFixedPoint' format_body_OK) in H3; eauto.
        eauto 8.
      }
    }
  Qed.

  (* :TODO: make it stronger? *)
  Lemma fix_format_correctP2
        (Pb : B -> Prop)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, Pb b -> bin_measure b < n ->
                   forall c,
                     CorrectDecoder'
                       monoid (predicate c) predicate_rest
                       (LeastFixedPoint format_body) (FueledFixP' decode_body n c) P b) ->
             forall b, Pb b -> bin_measure b < S n ->
                  forall c,
                    CorrectDecoder'
                      monoid (predicate c) predicate_rest
                      (format_body (LeastFixedPoint format_body)) (decode_body (FueledFixP' decode_body n) c) P b)
        (decode_body_continuous :
           forall decode,
             (forall c b cd a b' cd',
                 decode c b cd = Some (a, b', cd') ->
                 decode_body decode c b cd = Some (a, b', cd')) ->
             forall c b cd a b' cd',
               decode_body decode c b cd = Some (a, b', cd') ->
               decode_body (decode_body decode) c b cd = Some (a, b', cd'))
    : forall c bin,
      Pb bin ->
      CorrectDecoder'
        monoid (predicate c) predicate_rest
        (LeastFixedPoint format_body) (FueledFixP decode_body c) P bin.
  Proof.
    intros ? ? HPb.
    split. 2 : eapply fix_format_correctP2'; eauto.
    edestruct fix_format_correctP2' as [H _]; eauto.
    intros. edestruct H; eauto. destruct_many.
    eexists. repeat split; eauto.
    eapply FueledFixP_continuous.
    3 : eauto. 2 : rewrite mappend_measure; omega.
    destruct a as [[? ?] ?]. revert a b c0. induction n. easy.
    intros. simpl in *. eauto.
  Qed.
  
End Fix_format_correctP.

Definition FueledFix_dep' {B C D} {A E : D -> Type}
           (F : (forall d : D, E d -> B -> C -> option (A d)) -> forall d : D, E d -> B -> C -> option (A d)) :=
  FueledFix'' F (fun _ _ _ _ => None).

Definition FueledFix_dep {B C D} {A E : D -> Type}
           {monoid : Monoid B}
           (F : (forall d : D, E d -> B -> C -> option (A d)) -> forall d : D, E d -> B -> C -> option (A d))
  : forall d : D, E d -> B -> C -> option (A d) :=
  fun d c b => FueledFix_dep' F (S (bin_measure b)) d c b.

Theorem FueledFix_dep_continuous {B C D} {A E : D -> Type}
        (F : (forall d : D, E d -> B -> C -> option (A d)) -> forall d : D, E d -> B -> C -> option (A d))
  : (forall n b c d e a,
        FueledFix_dep' F n d e b c = Some a ->
        FueledFix_dep' F (S n) d e b c = Some a) ->
    forall n n',
      n <= n' ->
      forall b c d e a,
        FueledFix_dep' F n d e b c = Some a ->
        FueledFix_dep' F n' d e b c = Some a.
Proof.
  intros. induction H0; eauto.
Qed.

Section Fix_format_correct_dep.

  Context {B D: Type}.
  Context {A C : D -> Type}.
  Context {cache : Cache}.
  Context {monoid : Monoid B}.
  Context {P : CacheDecode -> Prop}.
  Context {P_inv : (CacheDecode -> Prop) -> Prop}.
  Variable format_body : funType_dep [C; A; fun _ => CacheFormat] (B * CacheFormat) ->
                         funType_dep [C; A; fun _ => CacheFormat] (B * CacheFormat).
  Variable decode_body : (forall d : D, C d -> B -> CacheDecode -> option (A d * B * CacheDecode)) ->
                         forall d : D, C d -> B -> CacheDecode -> option (A d * B * CacheDecode).
  Variable format_body_OK : Frame.monotonic_function format_body.
  Variable predicate : forall d, A d -> Prop.
  Variable predicate_rest : forall d, A d -> B -> Prop.
  Variable P_inv_OK : cache_inv_Property P P_inv.

  Lemma fix_format_correct_dep'
        (Pd : D -> Prop)
        (bound : B -> nat)         (* bound is usually bin_measure. *)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bound b < n ->
                   forall d (c : C d),
                     Pd d ->
                     CorrectDecoder'
                       monoid (predicate d) (predicate_rest d)
                       (LeastFixedPoint_dep format_body d c) (FueledFix_dep' decode_body n d c) P b) ->
             forall b, bound b < S n ->
                  forall d (c : C d),
                    Pd d ->
                    CorrectDecoder'
                      monoid (predicate d) (predicate_rest d)
                      (format_body (LeastFixedPoint_dep format_body) d c) (decode_body (FueledFix_dep' decode_body n) d c) P b)
    : forall b n,
      bound b < n ->
      forall d (c : C d),
        Pd d ->
        CorrectDecoder'
          monoid (predicate d) (predicate_rest d)
          (LeastFixedPoint_dep format_body d c) (FueledFix_dep' decode_body n d c) P b.
  Proof.
    specialize (decode_body_correct P_inv_OK).
    intros ? ? ? ? ? HPd.
    generalize dependent c.
    generalize dependent d.
    generalize dependent b.
    induction n; simpl; intros. {
      inversion H.
    } {
      split; intros. {
        eapply (unroll_LeastFixedPoint_dep format_body_OK) in H3; eauto.
        eapply decode_body_correct; eauto.
      } {
        eapply decode_body_correct in H2; eauto.
        destruct_many.
        eapply (unroll_LeastFixedPoint_dep' format_body_OK) in H3; eauto.
        eauto 8.
      }
    }
  Qed.

  (* :TODO: make it stronger? *)
  Lemma fix_format_correct_dep
        (Pd : D -> Prop)
        (decode_body_correct :
           cache_inv_Property P P_inv ->
           forall n,
             (forall b, bin_measure b < n ->
                   forall d (c : C d),
                     Pd d ->
                     CorrectDecoder'
                       monoid (predicate d) (predicate_rest d)
                       (LeastFixedPoint_dep format_body d c) (FueledFix_dep' decode_body n d c) P b) ->
             forall b, bin_measure b < S n ->
                  forall d (c : C d),
                    Pd d ->
                    CorrectDecoder'
                      monoid (predicate d) (predicate_rest d)
                      (format_body (LeastFixedPoint_dep format_body) d c) (decode_body (FueledFix_dep' decode_body n) d c) P b)
        (decode_body_continuous :
           forall decode,
             (forall d c b cd a b' cd',
                 decode d c b cd = Some (a, b', cd') ->
                 decode_body decode d c b cd = Some (a, b', cd')) ->
             forall d c b cd a b' cd',
               decode_body decode d c b cd = Some (a, b', cd') ->
               decode_body (decode_body decode) d c b cd = Some (a, b', cd'))
    : forall d (c : C d),
      Pd d ->
      CorrectDecoder
        monoid (predicate d) (predicate_rest d)
        (LeastFixedPoint_dep format_body d c) (FueledFix_dep decode_body d c) P.
  Proof.
    intros ? ? HPd. split. 2 : eapply fix_format_correct_dep'; eauto.
    edestruct fix_format_correct_dep' as [H _]; eauto.
    intros. edestruct H; eauto. destruct_many.
    eexists. repeat split; eauto.
    eapply (FueledFix_dep_continuous (A:=fun d => (A d * B * CacheDecode)%type)).
    3 : eauto. 2 : rewrite mappend_measure; omega.
    destruct a as [[? ?] ?]. revert a b b0 c0 c1 e. revert d0. induction n. easy.
    intros. simpl in *. eauto.
  Qed.
  
End Fix_format_correct_dep.