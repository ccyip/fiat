Require Import
        ADTSynthesis.QueryStructure.Specification.Representation.QueryStructureNotations
        ADTSynthesis.QueryStructure.Specification.SearchTerms.ListPrefix
        ADTSynthesis.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms
        ADTSynthesis.QueryStructure.Automation.IndexSelection
        Coq.Strings.Ascii.

(* Instances for building indexes with make simple indexes. *)
(* Every Kind of index is keyed on an inductive type with a single constructor*)
Definition FindPrefixIndex : string := "FindPrefixIndex".

(* This is our search term type. *)
Record FindPrefixSearchTerm
       (heading : Heading)
  :=
    { FindPrefixIndexSearchTerm : option (list ascii);
      FindPrefixItemSearchTerm : @Tuple heading -> bool }.

Global Instance Aascii_eq : Query_eq ascii := {| A_eq_dec := ascii_dec |}.

(* This builds the type of searchterms and the matching function on them *)
Global Instance FindPrefixIndexDenotation
       (heading : Heading)
       (index : @Attributes heading)
       (projection : @Tuple heading -> list ascii)
: @IndexDenotation "FindPrefixIndex" heading index :=
  {| DenoteIndex := FindPrefixSearchTerm heading; (* Pick search term type *)
     MatchIndex search_term item := (* matching function : DenoteIndex -> Tuple heading -> bool *)
       match FindPrefixIndexSearchTerm search_term with
         | Some indexSearchTerm =>
           if IsPrefix_dec (projection item) indexSearchTerm then
             FindPrefixItemSearchTerm search_term item
           else false
         | None =>
           FindPrefixItemSearchTerm search_term item
       end |}.

(* Extra type class magic for prefix indices. *)
Hint Extern 10 (@IndexDenotation "FindPrefixIndex" ?heading ?index) =>
let index_domain := eval hnf in (@Domain heading index) in
match index_domain with
  | list ascii =>
    apply (@FindPrefixIndexDenotation
             heading index
             (fun tup => GetAttribute tup index ))
end
: typeclass_instances.

Ltac matchFindPrefixIndex WhereClause k :=
  match WhereClause with
    | fun tups => IsPrefix (@?C1 tups) _ =>
      let attrs1 := TermAttributes C1 in
      k (map (fun a12 => (FindPrefixIndex, (fst a12, snd a12)))
             (attrs1))
  end.

Ltac PrefixIndexUse SC F indexed_attrs f k :=
     match type of f with
(* FindPrefix Search Terms *)
| forall a, {IsPrefix (_!?fd) ?X} + {_} =>
  let H := fresh in
  assert (List.In {| KindNameKind := "FindPrefixIndex";
                     KindNameName := fd|} indexed_attrs) as H
      by (clear; simpl; intuition eauto); clear H;
  k ({| KindNameKind := "FindPrefixIndex";
        KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
| forall a, {IsPrefix (_``?fd) ?X} + {_} =>
  let H := fresh in
  assert (List.In {| KindNameKind := "FindPrefixIndex";
                     KindNameName := fd|} indexed_attrs) as H
      by (clear; simpl; intuition eauto); clear H;
  k ({| KindNameKind := FindPrefixIndex;
        KindNameName := fd|}, X) (fun _ : @Tuple SC => true)
     end.

      (* FindPrefix Search Terms *)
Ltac PrefixIndexUse_dep SC F indexed_attrs visited_attrs f T k :=
    match type of f with
        | forall a b, {IsPrefix (_!?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "FindPrefixIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto); clear H;
          match eval simpl in
                (in_dec string_dec fd visited_attrs) with
            | right _ => k (fd :: visited_attrs)
                           ({| KindNameKind := "FindPrefixIndex";
                               KindNameName := fd |}, X)
                           (fun (a : T) (_ : @Tuple SC) => true)
            | left _ => k visited_attrs tt F
          end
        | forall a b, {IsPrefix (_``?fd) (@?X a)} + {_} =>
          let H := fresh in
          assert (List.In {| KindNameKind := "FindPrefixIndex";
                             KindNameName := fd|} indexed_attrs) as H
              by (clear; simpl; intuition eauto);
            match eval simpl in
                  (in_dec string_dec fd visited_attrs) with
              | right _ => k (fd :: visited_attrs)
                             ({| KindNameKind := "FindPrefixIndex";
                                 KindNameName := fd |}, X)
                             (fun (a : T) (_ : @Tuple SC) => true)
              | left _ => k visited_attrs tt F
            end
end.

Ltac createLastPrefixTerm f fds tail fs kind s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k {| FindPrefixIndexSearchTerm := Some X;
                             FindPrefixItemSearchTerm := tail |}))
        || k {| FindPrefixIndexSearchTerm := None;
                FindPrefixItemSearchTerm := tail |}
end.

Ltac createLastPrefixTerm_dep dom f fds tail fs kind rest s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (fun x : dom => {| FindPrefixIndexSearchTerm := Some (X x);
                                             FindPrefixItemSearchTerm := tail x |}))
                || k (fun x : dom => {| FindPrefixIndexSearchTerm := None;
                                        FindPrefixItemSearchTerm := tail x |}))
  end.

Ltac createEarlyPrefixTerm f fds tail fs kind EarlyIndex LastIndex rest s k :=
  match kind with
    | "FindPrefixIndex" =>
      (findMatchingTerm
         fds kind s
         ltac:(fun X => k (Some X, rest)))
        || k (@None (list ascii), rest)
  end.
