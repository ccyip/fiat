(** * Maps: Total and Partial Maps *)
(* Adapted from Software Foundations. *)

Require Import Coq.Arith.Arith.
Require Import Coq.Bool.Bool.
Require Export Coq.Strings.String.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List.
Require Import Fiat.Computation.Decidable.
Import ListNotations.

Section TotalMaps.

Context {D : Type}.
Context {A : Type}.
Context {eqdec : EqbDec D}.

Definition total_map := D -> A.

Definition t_empty (v : A) : total_map :=
  (fun _ => v).

Definition t_update (m : total_map)
                    (x : D) (v : A) :=
  fun x' => if eqb x x' then v else m x'.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).


Lemma t_apply_empty:  forall (x: D) (v: A), { --> v } x = v.
Proof.
  intros x v. reflexivity.
Qed.

Lemma t_update_eq : forall (m: total_map) x v,
  (m & {x --> v}) x = v.
Proof.
  intros m x v. unfold t_update. 
  rewrite eqb_refl. reflexivity.
Qed.

Theorem t_update_neq : forall v x1 x2
                         (m : total_map),
  x1 <> x2 ->
  (m & {x1 --> v}) x2 = m x2.
Proof.
  intros v x1 x2 m H. unfold t_update.
  apply eqb_false_iff in H. rewrite -> H.
  reflexivity.
Qed.

Lemma t_update_shadow : forall (m: total_map) v1 v2 x,
    m & {x --> v1 ; x --> v2} = m & {x --> v2}.
Proof.
  intros m v1 v2 x. apply functional_extensionality.
  intros x'. unfold t_update. destruct (eqb x x').
  - reflexivity.
  - reflexivity.
Qed.

Theorem t_update_same : forall x (m : total_map),
    m & { x --> m x } = m.
Proof.
  intros x m. apply functional_extensionality. intros x'.
  destruct (eqbP x x').
  - rewrite <- e. apply t_update_eq.
  - apply t_update_neq. apply n.
Qed.

Theorem t_update_permute : forall v1 v2 x1 x2
                             (m : total_map),
  x2 <> x1 ->
  m & { x2 --> v2 ; x1 --> v1 }
  =  m & { x1 --> v1 ; x2 --> v2 }.
Proof.
  intros v1 v2 x1 x2 m H. apply functional_extensionality. intros x'.
  destruct (eqbP x1 x').
  - subst. rewrite -> t_update_eq. rewrite -> t_update_neq; auto.
    symmetry. apply t_update_eq.
  - rewrite -> t_update_neq; auto. destruct (eqbP x2 x').
    + rewrite <- e. rewrite -> t_update_eq. symmetry. apply t_update_eq.
    + rewrite -> !t_update_neq; auto.
Qed.

End TotalMaps.

Arguments total_map: clear implicits.

Notation "{ --> d }" := (t_empty d) (at level 0).

Notation "m '&' { a --> x }" :=
  (t_update m a x) (at level 20).
Notation "m '&' { a --> x ; b --> y }" :=
  (t_update (m & { a --> x }) b y) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z }" :=
  (t_update (m & { a --> x ; b --> y }) c z) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z }) d t) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t }) e u) (at level 20).
Notation "m '&' { a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }" :=
    (t_update (m & { a --> x ; b --> y ; c --> z ; d --> t ; e --> u }) f v) (at level 20).

Section PartialMaps.

Context {D : Type}.
Context {A : Type}.
Context {eqdec : EqbDec D}.

Definition partial_map := total_map D (option A).

Definition empty : partial_map :=
  t_empty None.

Definition update (m : partial_map)
           (x : D) (v : A) :=
  m & { x --> (Some v) }.

Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) (at level 20).

Lemma apply_empty : forall (x: D),  empty x = None.
Proof.
  intros. unfold empty. rewrite t_apply_empty.
  reflexivity.
Qed.

Lemma update_eq : forall (m: partial_map) x v,
    (m & {{ x --> v }}) x = Some v.
Proof.
  intros. unfold update. rewrite t_update_eq.
  reflexivity.
Qed.

Theorem update_neq : forall v x1 x2
                       (m : partial_map),
  x2 <> x1 ->
  (m & {{ x2 --> v }}) x1 = m x1.
Proof.
  intros v x1 x2 m H.
  unfold update. rewrite t_update_neq. reflexivity.
  apply H. Qed.

Lemma update_shadow : forall (m: partial_map) v1 v2 x,
    m & {{ x --> v1 ; x --> v2 }} = m & {{x --> v2}}.
Proof.
  intros m v1 v2 x1. unfold update. rewrite t_update_shadow.
  reflexivity.
Qed.

Theorem update_same : forall v x (m : partial_map),
  m x = Some v ->
  m & {{x --> v}} = m.
Proof.
  intros v x m H. unfold update. rewrite <- H.
  apply t_update_same.
Qed.

Theorem update_permute : forall v1 v2 x1 x2
                                (m : partial_map),
  x2 <> x1 ->
  m & {{x2 --> v2 ; x1 --> v1}}
  = m & {{x1 --> v1 ; x2 --> v2}}.
Proof.
  intros v1 v2 x1 x2 m. unfold update.
  apply t_update_permute.
Qed.


End PartialMaps.

Arguments partial_map: clear implicits.

Notation "m '&' {{ a --> x }}" :=
  (update m a x) (at level 20).
Notation "m '&' {{ a --> x ; b --> y }}" :=
  (update (m & {{ a --> x }}) b y) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z }}" :=
  (update (m & {{ a --> x ; b --> y }}) c z) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z }}) d t) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t }}) e u) (at level 20).
Notation "m '&' {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u ; f --> v }}" :=
    (update (m & {{ a --> x ; b --> y ; c --> z ; d --> t ; e --> u }}) f v) (at level 20).
