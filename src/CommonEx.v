Require Import
        FunctionalExtensionality
        Coq.omega.Omega
        Coq.Logic.Eqdep_dec.

Require Import
        Fiat.Computation
        Fiat.Computation.Core
        Fiat.Narcissus.Common.Specs.

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
         | H : (_, _) = (_, _) |- _ => inversion_clear H; subst
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
      apply inj_pair2_eq_dec in H;
      try apply Nat.eq_dec
    end.

Ltac gen_eq_rect :=
  match goal with
  | _ : _ |- context [eq_rect _ _ _ _ ?e] => generalize e; try destruct 0
  end.

Definition type_cast {A B : Type} (pf : A = B) (v : A) : B.
Proof.
  rewrite <- pf.
  exact v.
Defined.