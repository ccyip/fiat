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

Section DecodeWf.

  Context {A : Type}.
  Context {B : Type}.
  Context {cache : Cache}.

  Definition CorrectDecoderWf
             {F : B -> Type}
             (monoid : Monoid B)
             (predicate : A -> Prop)
             (rest_predicate : A -> B -> Prop)
             (format : FormatM A B)
             (decode : forall b, F b -> CacheDecode -> option (A * B * CacheDecode))
             (decode_inv : CacheDecode -> Prop) :=
    (forall env env' xenv data bin ext
       (env_OK : decode_inv env'),
        Equiv env env' ->
        predicate data ->
        rest_predicate data ext ->
        format data env ↝ (bin, xenv) ->
        forall pf,
        exists xenv',
          decode (mappend bin ext) pf env' = Some (data, ext, xenv')
          /\ Equiv xenv xenv' /\ decode_inv xenv') /\
    (forall env env' xenv' data bin ext pf,
        Equiv env env'
        -> decode_inv env'
        -> decode bin pf env' = Some (data, ext, xenv')
        -> decode_inv xenv'
          /\ exists bin' xenv,
            (format data env ↝ (bin', xenv))
            /\ bin = mappend bin' ext
            /\ predicate data
            /\ Equiv xenv xenv').

  Context {monoid : Monoid B}.
  Context {P : CacheDecode -> Prop}.
  Variable predicate : A -> Prop.
  Variable predicate_rest : A -> B -> Prop.
  Variable bound : B.
  Variable decode : DecodeM A B.
  (* :TODO: lt_B to F? *)
  Variable decodeWf : forall b, lt_B b bound -> CacheDecode -> option (A * B * CacheDecode).

  Definition decode_wf_eq
    := forall b cd pf, decode b cd = decodeWf b pf cd.

  Theorem decodeWf_correct
    : decode_wf_eq ->
      forall format,
      CorrectDecoder monoid predicate predicate_rest format decode P ->
      CorrectDecoderWf monoid predicate predicate_rest format decodeWf P.
  Proof.
    intros. unfold decode_wf_eq in *.
    split; intros. {
      destruct H0 as [? _]. edestruct H0; eauto. destruct_many.
      eexists. repeat split; eauto. congruence.
    } {
      destruct H0 as [_ ?]. edestruct H0; eauto. congruence.
    }
  Qed.

  Theorem decodeWf_lt
    : decode_wf_eq ->
      (forall b cd d b' cd',
          decode b cd = Some (d, b', cd') -> lt_B b' b) ->
      forall b pf cd d b' cd',
        decodeWf b pf cd = Some (d, b', cd') -> lt_B b' b.
  Proof.
    intros. unfold decode_wf_eq in *. rewrite <- H in H1. eauto.
  Qed.

  Theorem decodeWf_le
    : decode_wf_eq ->
      (forall b cd d b' cd',
          decode b cd = Some (d, b', cd') -> le_B b' b) ->
      forall b pf cd d b' cd',
        decodeWf b pf cd = Some (d, b', cd') -> le_B b' b.
  Proof.
    intros. unfold decode_wf_eq in *. rewrite <- H in H1. eauto.
  Qed.

End DecodeWf.

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
    destruct decode_correct as [[? [? [? ?]]] _]; eauto.
    eexists. repeat split; eauto.
    rewrite H3. simpl.
    specialize (im_OK (f data)).
    destruct im. repeat progress f_equal. auto.
    simpl in im_OK. exfalso. auto with sets.
  } {
    decode_opt_to_inv.
    destruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
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
    destruct decode_correct as [[? [? [? ?]]] _]; eauto.
    eexists. rewrite H3. simpl. destruct predicate_dec; eauto.
    congruence.
  } {
    decode_opt_to_inv.
    specialize (predicate_dec_OK x). destruct predicate_dec; try easy.
    injections.
    destruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
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
    destruct decode_correct as [[? [? [? ?]]] _]; eauto.
  } {
    destruct decode_correct as [_ [? [? [? [? [? [? ?]]]]]]]; eauto.
    split; auto. eexists _, _. repeat split; eauto.
  }
Qed.

Lemma fix_format_correct
      {A B} {cache : Cache} {monoid : Monoid B}
      {P : CacheDecode -> Prop}
      {P_inv : (CacheDecode -> Prop) -> Prop}
      (predicate : A -> Prop) (predicate_rest : A -> B -> Prop)
      (format_body : funType [A; CacheFormat] (B * CacheFormat) ->
                     funType [A; CacheFormat] (B * CacheFormat))
      (decode_body : forall b : B,
          (forall b' : B, lt_B b' b -> CacheDecode -> option (A * B * CacheDecode)) ->
          CacheDecode -> option (A * B * CacheDecode))
      (format_body_OK : Frame.monotonic_function format_body)
      (P_inv_OK : cache_inv_Property P P_inv)
      (decode_body_correct :
         cache_inv_Property P P_inv ->
         forall (format : funType [A; CacheFormat] (B * CacheFormat)) decode,
           refineEquivFun format (format_body format) ->
           (forall b cd, decode b cd = decode_body b (fun b' _ => decode b') cd) ->
           CorrectDecoder monoid predicate predicate_rest
                          (format_body format)
                          (fun b => decode_body b (fun b' _ => decode b'))
                          P)
  : CorrectDecoder
      monoid predicate predicate_rest
      (LeastFixedPoint format_body) (Fix well_founded_lt_b _ decode_body) P.
Proof.
  specialize (decode_body_correct P_inv_OK).
  split; intros. {
    rewrite Init.Wf.Fix_eq by solve_extensionality.
    eapply decode_body_correct; eauto.
    split.
    eapply (unroll_LeastFixedPoint format_body_OK); eauto.
    eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
    intros; rewrite Init.Wf.Fix_eq by solve_extensionality; eauto.
    eapply (unroll_LeastFixedPoint format_body_OK); eauto.
  } {
    rewrite Init.Wf.Fix_eq in H1 by solve_extensionality.
    eapply decode_body_correct in H1; eauto.
    intuition; destruct_ex; eexists _, _; intuition eauto.
    eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
    split.
    eapply (unroll_LeastFixedPoint format_body_OK); eauto.
    eapply (unroll_LeastFixedPoint' format_body_OK); eauto.
    intros; rewrite Init.Wf.Fix_eq by solve_extensionality; eauto.
  }
Qed.
