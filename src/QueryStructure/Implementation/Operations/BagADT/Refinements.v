Require Export Coq.Lists.List Coq.Program.Program
        Fiat.QueryStructure.Specification.Representation.Tuple
        Fiat.QueryStructure.Specification.Representation.Heading
        Fiat.Common.ilist2
        Fiat.Common.i2list
        Fiat.Common.ilist3
        Fiat.Common.i3list.

Require Import Coq.Bool.Bool
        Coq.Strings.String
        Coq.Structures.OrderedTypeEx
        Coq.Arith.Arith
        Fiat.Common.String_as_OT
        Fiat.Common.Ensembles.IndexedEnsembles
        Fiat.Common.DecideableEnsembles
        Fiat.Common.List.ListFacts
        Fiat.QueryStructure.Specification.Operations.FlattenCompList
        Fiat.QueryStructure.Implementation.Operations.General.QueryRefinements
        Fiat.QueryStructure.Implementation.Operations.General.EmptyRefinements
        Fiat.QueryStructure.Specification.Representation.QueryStructureNotations
        Fiat.QueryStructure.Implementation.ListImplementation
        Fiat.Common.List.PermutationFacts
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.BagADT
        Fiat.QueryStructure.Implementation.DataStructures.BagADT.QueryStructureImplementation.

Section BagsQueryStructureRefinements.

  Require Import         Fiat.QueryStructure.Implementation.DataStructures.BagADT.IndexSearchTerms.
  Definition fooT :=
    forall
      (sBOOKS := "Books")
      (sAUTHOR := "Authors")
      (sTITLE := "Title")
      (sISBN := "ISBN")
      (sORDERS := "Orders")
      (sDATE := "Date")
    (BookStoreSchema :=
  Query Structure Schema
    [ relation sBOOKS has
              schema <sAUTHOR :: string,
                      sTITLE :: string,
                      sISBN :: nat>
                      where attributes [sTITLE; sAUTHOR] depend on [sISBN];
      relation sORDERS has
              schema <sISBN :: nat,
                      sDATE :: nat> ]
    enforcing [attribute sISBN for sORDERS references sBOOKS])
  (StringId := "Init" : string)
    (StringId0 := "PlaceOrder" : string)
    (StringId1 := "EqualityIndex" : string)
    m n o mt mt'
    (SearchTerm := BuildIndexSearchTerm (BuildIndexSearchTermT := unit)
                  [{| KindIndexKind := StringId1; KindIndexIndex := m |};
                  {|
                  KindIndexKind := StringId1;
                  KindIndexIndex := n |}] :
            Type)
    (SearchTerm0 := BuildIndexSearchTerm (BuildIndexSearchTermT := unit)
                   [{|
                    KindIndexKind := StringId1;
                    KindIndexIndex := o |}] :
             Type)
    (SearchUpdateTerm := {|
                      BagSearchTermType := SearchTerm;
                      BagMatchSearchTerm := MatchIndexSearchTerm (matcher := mt);
                      BagUpdateTermType := RawTuple -> RawTuple;
                      BagApplyUpdateTerm := fun z : RawTuple -> RawTuple => z |}
                   : SearchUpdateTerms
                       {|
                       NumAttr := 3;
                       AttrList := Vector.cons Type string _ (Vector.cons Type string _ (Vector.cons Type nat _ (Vector.nil _)))|})
    (SearchUpdateTerm0 := {|
                       BagSearchTermType := SearchTerm0;
                       BagMatchSearchTerm := MatchIndexSearchTerm (matcher := mt');
                       BagUpdateTermType := RawTuple -> RawTuple;
                       BagApplyUpdateTerm := fun z : RawTuple -> RawTuple =>
                                             z |}
                    : SearchUpdateTerms
                        {|
                        NumAttr := 2;
                        AttrList := Vector.cons Type nat _ (Vector.cons Type nat _ (Vector.nil _)) |})
    (Index := icons3 SearchUpdateTerm (icons3 SearchUpdateTerm0 inil3)
        : ilist3 (qschemaSchemas BookStoreSchema))
    (foo1 : constructorType (IndexedQueryStructure BookStoreSchema Index)
                            (consDom (Constructor "Init" : () ->rep)%consSig))
    (d : consDom (Constructor StringId : () ->rep)%consSig),
   refine
     (r_o' <- or' <- empty;
              ret (DropQSConstraints or');
      {r_n : IndexedQueryStructure BookStoreSchema Index |
      DelegateToBag_AbsR r_o' r_n}) (foo1 d).


  Import Coq.Vectors.VectorDef.VectorNotations.

  Variable qs_schema : RawQueryStructureSchema.
  Variable BagIndexKeys :
    ilist3 (B := fun ns => SearchUpdateTerms (rawSchemaHeading ns))
          (qschemaSchemas qs_schema).

  Lemma i2th_Bounded_Initialize_IndexedQueryStructure {n}
  : forall ns indices v idx,
      computes_to (@Initialize_IndexedQueryStructure n ns indices) v
      -> i3th v idx = Empty_set _.
  Proof.
    induction ns.
    - intros; inversion idx.
    - intros; revert ns IHns indices v H; pattern n, idx.
      match goal with
        |- ?P n idx => simpl; apply (@Fin.caseS P); intros; simpl in *
      end.
      + unfold CallBagConstructor in H; simpl in H; computes_to_inv.
        subst; simpl in *; eauto.
      + computes_to_inv; subst.
        eapply IHns; eauto.
  Qed.

  Corollary refine_QSEmptySpec_Initialize_IndexedQueryStructure
    : refine {nr' | DelegateToBag_AbsR (imap2 rawRel (Build_EmptyRelations (qschemaSchemas qs_schema))) nr'}
             (@Initialize_IndexedQueryStructure _ (qschemaSchemas qs_schema) BagIndexKeys).
  Proof.
    intros v Comp_v.
    computes_to_econstructor.
    unfold IndexedQueryStructure, DelegateToBag_AbsR, GetIndexedRelation.
    unfold GetUnConstrRelation.
    unfold DropQSConstraints, QSEmptySpec.
    intros; simpl; rewrite <- ith_imap2, ith_Bounded_BuildEmptyRelations,
                   i2th_Bounded_Initialize_IndexedQueryStructure; eauto.
    intros; eexists List.nil; split;
    intros; simpl; try rewrite <- ith_imap2, ith_Bounded_BuildEmptyRelations.
    - split; simpl; intros.
      + exists 0; unfold UnConstrFreshIdx; intros; intuition.
      + eexists List.nil; intuition eauto.
        * inversion H.
        * inversion H.
        * econstructor.
    - split; simpl; intros.
      + exists 0; unfold UnConstrFreshIdx; intros; intuition.
      + eexists List.nil; intuition eauto.
        * inversion H.
        * inversion H.
        * econstructor.
  Qed.

  Definition UpdateIndexedRelation
             (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel
  : IndexedQueryStructure qs_schema BagIndexKeys  :=
    replace3_Index3 _ _ r_n idx newRel.

  Lemma get_update_indexed_eq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx newRel,
      GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx = newRel.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i3th_replace_Index_eq; eauto using string_dec.
  Qed.

  Lemma get_update_indexed_neq :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx idx' newRel,
      idx <> idx'
      -> GetIndexedRelation (UpdateIndexedRelation r_n idx newRel) idx' =
         GetIndexedRelation r_n idx'.
  Proof.
    unfold UpdateIndexedRelation, GetIndexedRelation;
    intros; simpl; rewrite i3th_replace_Index_neq; eauto using string_dec.
  Qed.

  Lemma exists_UnConstrFreshIdx
    : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall idx,
        exists bnd,
          UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd.
  Proof.
    unfold DelegateToBag_AbsR; intros.
    destruct (H idx) as
        [l [[[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]
              [[bnd' fresh_bnd'] [l'' [l''_eq [l''_eqv NoDup_l'']]]]]];
      eauto.
  Qed.

  Lemma refine_Pick_UnConstrFreshIdx
    : forall r_o
             (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall idx bnd,
        UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd
      -> refine { bnd | UnConstrFreshIdx (GetUnConstrRelation r_o idx) bnd}
                (ret bnd).
  Proof.
    intros; refine pick val bnd; eauto.
    reflexivity.
  Qed.

  Lemma refine_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : Fin.t _)
                (resultComp : RawTuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Comp_Lists [ inil2 ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)));
                   (List_Query_In l (fun tup : ilist2 (B := @RawTuple) [ _ ]=> resultComp (ilist2_hd tup)))) .
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod;
    intros; simpl.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl.
    unfold List_Query_In.
    intros v Comp_v;  computes_to_inv;
    unfold EnsembleIndexedListEquivalence,
    UnIndexedEnsembleListEquivalence in *.
    destruct (H idx); intuition; destruct_ex; intuition; subst.
    unfold EnsembleIndexedListEquivalence,
    UnIndexedEnsembleListEquivalence in *;
      intuition; destruct_ex; intuition; subst.
    computes_to_econstructor.
    instantiate (1 := map indexedElement x0);
      computes_to_econstructor; eauto.
    setoid_rewrite H0 in H8.
    setoid_rewrite H4.
    revert H6 H8 H11 H5 H10; clear; intros.
    apply NoDup_Permutation in H8; eauto using NoDup_IndexedElement.
    destruct (@permu_exists _ (map indexedElement x0) x4);
      intuition.
    simpl in *; unfold GetNRelSchema in *; rewrite <- H5.
    eapply Permutation_map; eauto.
    setoid_rewrite <- H1.
    eexists x; intuition eauto.
    eapply Permutation_map_aux in H1.
    symmetry in H1.
    eapply NoDup_Permutation_rewrite; eauto.
    rewrite map_map.
    repeat setoid_rewrite map_app in Comp_v'';
      repeat setoid_rewrite map_map in Comp_v''; simpl in *;
      rewrite app_nil_r in Comp_v''; eauto.
  Qed.

  Local Opaque IndexedQueryStructure.

  Lemma refine_Filtered_Query_In_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : Fin.t _)
                (resultComp : RawTuple -> Comp (list ResultT)),
           refine (UnConstrQuery_In r_o idx resultComp)
                  (l <- Join_Filtered_Comp_Lists [ inil2 ]
                     (fun _ =>
                        l <- CallBagMethod idx BagEnumerate r_n ();
                      (ret (snd l)))
                     (fun _ => true);
                   (List_Query_In l (fun tup : ilist2 (B := @RawTuple) [ _ ]=> resultComp (ilist2_hd tup)))) .
  Proof.
    intros; rewrite refine_Query_In_Enumerate by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Local Transparent Query_For.

  Lemma refine_For_Enumerate
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx : Fin.t _)
                (f : _ -> Comp (list ResultT)),
           refine (For (l <- CallBagMethod idx BagEnumerate r_n ();
                        f l))
                  (l <- CallBagMethod idx BagEnumerate r_n ();
                   For (f l)).
  Proof.
    simpl; intros; unfold Query_For.
    simplify with monad laws.
    unfold CallBagMethod; simpl.
    unfold refine; intros;  computes_to_inv.
    subst; repeat computes_to_econstructor; eauto.
  Qed.

  Lemma refine_Join_Query_In_Enumerate'
        {n}
        headings
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : Fin.t _)
             (resultComp : ilist2 (n := n) (B:= @RawTuple) headings
                           -> RawTuple
                           -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : ilist2 (B := @RawTuple) headings =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- (Join_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                          ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_tl tup_pair) (ilist2_hd tup_pair)))).
  Proof.
    intros.
    unfold List_Query_In; induction l; unfold Join_Comp_Lists; simpl.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - setoid_rewrite IHl; rewrite refine_Query_In_Enumerate; eauto.
      unfold List_Query_In.
      setoid_rewrite refineEquiv_bind_bind at 1.
      setoid_rewrite refineEquiv_bind_bind at 2.
      intros v Comp_v;  computes_to_inv.
      subst.
      rewrite map_app, map_map in Comp_v'; simpl in *.
      computes_to_econstructor; eauto.
      apply flatten_CompList_app_inv' in Comp_v'; destruct_ex; intuition.
      subst; repeat (computes_to_econstructor; eauto).
      unfold Build_single_Tuple_list in *.
      rewrite !map_app, !map_map, app_nil_r; simpl; eauto.
  Qed.

  Corollary refine_Join_Query_In_Enumerate
            (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : Fin.t _)
             (resultComp : RawTuple -> RawTuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist2_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_hd (ilist2_tl tup_pair)) (ilist2_hd tup_pair)))).
  Proof.
    intros.
    f_equiv; simpl; intro.
    eapply refine_Join_Query_In_Enumerate' with
    (l := Build_single_Tuple_list (snd a)); eauto.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate'
            {n}
        headings
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx : Fin.t _)
             (resultComp : ilist2 (n := n) ( B:= @RawTuple) headings
                           -> RawTuple
                           -> Comp (list ResultT))
             l,
        refine (List_Query_In l (fun tup : ilist2 (B:= @RawTuple) headings =>
                                   UnConstrQuery_In r_o idx (resultComp tup)))
               (l' <- (Join_Filtered_Comp_Lists l (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                                   ret (snd l))
                                                (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_tl tup_pair) (ilist2_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate' by eauto.
    rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  Corollary refine_Filtered_Join_Query_In_Enumerate
            (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : Fin.t _)
             (resultComp : RawTuple -> RawTuple -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (Build_single_Tuple_list (snd l))
                              (fun tup =>
                                 UnConstrQuery_In r_o idx' (resultComp (ilist2_hd tup))))
               (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Filtered_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l))
                                       (fun _ => true));
                List_Query_In l' (fun tup_pair => (resultComp (ilist2_hd (ilist2_tl tup_pair)) (ilist2_hd tup_pair)))).
  Proof.
    intros; rewrite refine_Join_Query_In_Enumerate by eauto.
    f_equiv; intro; rewrite Join_Filtered_Comp_Lists_id; reflexivity.
  Qed.

  (*Lemma refine_Join_Enumerate_Swap
        (ResultT : Type) :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx idx' : BoundedString)
             (resultComp : _ -> Comp (list ResultT)),
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx' BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' resultComp)
               (l <- CallBagMethod idx' BagEnumerate r_n ();
                l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd l))
                                       (fun _ => l <- (CallBagMethod idx BagEnumerate r_n ());
                                        ret (snd l)));
                List_Query_In l' (fun tup_pair => (resultComp (icons _ (ilist2_hd (ilist2_tl tup_pair)) (icons _ (ilist2_hd tup_pair) (inil _)))))).
  Proof.
  Admitted. *)

  (* Lemma refine_Join_Enumerate_Swap
        (A B ResultT : Type) :
    forall (c : Comp A) (c' : Comp B)
           (resultComp : _ -> _ -> Comp (list ResultT)),
      refineEquiv (For (l <- c;
                        l' <- c';
                        resultComp l l'))
                  (For (l' <- c';
                        l <- c;
                        resultComp l l')).
  Proof.
    split; simpl; intros; f_equiv; intros v Comp_v;
     computes_to_inv; subst;
    repeat (econstructor; eauto).
  Qed.*)

  Lemma refine_Query_For_In_Find
        (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx : Fin.t _)
             filter_dec
             search_pattern
             (resultComp : RawTuple -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith3 BagIndexKeys idx) search_pattern)
        -> refine (l <- CallBagMethod idx BagEnumerate r_n ();
                   List_Query_In (filter filter_dec (snd l)) resultComp)
                  (l <- CallBagMethod idx BagFind r_n search_pattern;
                   List_Query_In (snd l) resultComp).
  Proof.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod, Query_For;
    intros; simpl.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl; f_equiv; intro.
    unfold List_Query_In.
    rewrite (filter_by_equiv _ _ H0).
    reflexivity.
  Qed.

  Lemma refine_Join_Comp_Lists_To_Find {n}
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist2 (n := n) (B:= @RawTuple) headings))
                (idx : Fin.t _)
                search_pattern,
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith3  BagIndexKeys idx) search_pattern (ilist2_hd a) && true))
                  (Join_Comp_Lists l1
                                   (fun _ =>
                                      l <- CallBagMethod idx BagFind r_n search_pattern;
                                    ret (snd l))) .
  Proof.
    unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; intros; simpl.
    induction l1.
    - simplify with monad laws; reflexivity.
    - Local Transparent CallBagMethod.
      unfold CallBagMethod.
      simpl.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v.
       computes_to_inv; subst.
       generalize (IHl1 _ Comp_v); intros;  computes_to_inv.
       computes_to_econstructor; subst; eauto.
      rewrite filter_app, filter_map.
      simpl.
      erewrite filter_by_equiv; eauto.
      unfold ExtensionalEq; intros; rewrite andb_true_r; auto.
  Qed.

  Lemma refine_Join_Comp_Lists_To_Find_dep {n}
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall {headings}
                (l1 : list (ilist2 (n := n) (B:= @RawTuple) headings))
                (idx :Fin.t _)
                (search_pattern : ilist2 (B:= @RawTuple) headings -> _),
           refine (Join_Filtered_Comp_Lists l1
                                            (fun _ =>
                                               l <- CallBagMethod idx BagEnumerate r_n ();
                                             ret (snd l))
                                            (fun a => BagMatchSearchTerm (ith3  BagIndexKeys idx)
                                                                         (search_pattern (ilist2_tl a)) (ilist2_hd a) && true))
                  (Join_Comp_Lists l1
                                   (fun a =>
                                      l <- CallBagMethod idx BagFind r_n (search_pattern a);
                                    ret (snd l))) .
  Proof.
    unfold Join_Filtered_Comp_Lists, Join_Comp_Lists; intros; simpl.
    induction l1.
    - simplify with monad laws; reflexivity.
    - Local Transparent CallBagMethod.
      unfold CallBagMethod.
      simpl.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
      setoid_rewrite refineEquiv_bind_bind at 1.
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
      intros v Comp_v.
       computes_to_inv; subst.
      generalize (IHl1 _ Comp_v); intros;  computes_to_inv.
      computes_to_econstructor; subst; eauto.
      rewrite filter_app, filter_map.
      simpl.
      erewrite filter_by_equiv; eauto.
      unfold ExtensionalEq; intros; rewrite andb_true_r; auto.
  Qed.


  Instance DecideableEnsemblePair_tail
           {n}
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (ilist2 (n := n) (B := f) As))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist2 (B := f) (a :: As) => P (ilist2_tl ab)) :=
    { dec ab := dec (ilist2_tl ab) }.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist2_tl a0)).
  Defined.

  Instance DecideableEnsemblePair_head
           {n}
           {A}
           {a}
           {As}
           (f : A -> Type)
           (P : Ensemble (f a))
           (P_dec : DecideableEnsemble P)
  : DecideableEnsemble (fun ab : ilist2 (n := S n) (B := f) (a :: As) => P (ilist2_hd ab)) :=
    { dec ab := dec (ilist2_hd ab) }.
  Proof.
    intro; apply (dec_decides_P (DecideableEnsemble := P_dec) (ilist2_hd a0)).
  Defined.

  Lemma Join_Comp_Lists_nil
        {n}
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall (s2 : _ -> Comp (list (f' a))),
      refineEquiv (Join_Comp_Lists (n := n) (As := As) (a := a) (List.nil) s2) (ret (List.nil)).
  Proof.
    unfold Join_Comp_Lists; simpl; try reflexivity.
  Qed.

  Lemma filter_and_join_ilist2_hd
        {n}
        {A}
        {a}
        {As}
        (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist2 (n := n) (B := f') As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest ,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (B := f') (a :: As) => f (ilist2_hd x) && filter_rest x) l))
                  (l <- Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter f l));
                   ret (filter filter_rest l)).
  Proof.
    split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
    - simplify with monad laws; rewrite refineEquiv_bind_unit;
      reflexivity.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHs1 _ (BindComputes _ (fun x => ret (filter filter_rest x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, c'; eauto.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose proof (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      rewrite filter_app, filter_map; simpl; eauto.
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, H'; eauto.
  Qed.

  Corollary filter_join_ilist2_hd
            {n}
            {A}
            {a}
            {As}
            (f' : A -> Type)
  : forall
      (f : f' a -> bool)
      (s1 : list (ilist2 (B := f') As))
      (s2 : _ -> Comp (list (f' a))),
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (n := S n) (B := f') (a :: As) => f (ilist2_hd x)) l))
                  (Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter f l))).
  Proof.
    intros; pose proof (filter_and_join_ilist2_hd f s1 s2 (fun _ => true)).
    setoid_rewrite filter_and in H; setoid_rewrite filter_true in H.
    setoid_rewrite H; eauto; setoid_rewrite refineEquiv_unit_bind; reflexivity.
  Qed.

  Lemma filter_Build_single_Tuple_list
        {heading}
        (l : list (@RawTuple heading))
        (filter_dec : @RawTuple heading -> bool)
  : filter (fun tup : ilist2 (B:= @RawTuple) [_] => filter_dec (ilist2_hd tup)) (Build_single_Tuple_list l) = Build_single_Tuple_list (filter filter_dec l).
  Proof.
    induction l; simpl; eauto.
    destruct (filter_dec a); simpl; eauto.
    f_equal; eauto.
  Qed.

  Corollary refine_Query_For_In_Find_snd'
            (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      ->
      forall (idx :Fin.t _)
             (filter_dec : RawTuple -> bool)
             search_pattern
             (resultComp : _ -> Comp (list ResultT)),
        ExtensionalEq filter_dec
                      (BagMatchSearchTerm (ith3  BagIndexKeys idx) search_pattern)
        -> refine (l <- CallBagMethod idx BagEnumerate r_n ();
                   List_Query_In (filter (fun tup : ilist2 (B:= @RawTuple) [_] => filter_dec (ilist2_hd tup)) (Build_single_Tuple_list (snd l)))
                                 resultComp)
                  (l <- CallBagMethod idx BagFind r_n search_pattern;
                   List_Query_In (Build_single_Tuple_list (snd l)) resultComp).
  Proof.
    simpl; intros.
    setoid_rewrite filter_Build_single_Tuple_list.
    unfold UnConstrQuery_In, QueryResultComp, CallBagMethod, Query_For;
      intros; simpl.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl; f_equiv; intro.
    unfold List_Query_In.
    rewrite (filter_by_equiv _ _ H0).
    reflexivity.
  Qed.

  Corollary refine_Query_For_In_Find_single
            (ResultT : Type)
  : forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n ->
      forall (idx :Fin.t _)
             search_pattern
             (resultComp : _ -> Comp (list ResultT))
             filter_rest,
        refine (l <- CallBagMethod idx BagEnumerate r_n ();
                List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_] => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) (Build_single_Tuple_list (snd l)))
                              resultComp)
               (l <- CallBagMethod idx BagFind r_n search_pattern;
                List_Query_In (filter filter_rest (Build_single_Tuple_list (snd l))) resultComp).
  Proof.
    unfold CallBagMethod; simpl; intros.
    simplify with monad laws.
    setoid_rewrite refineEquiv_bind_bind;
      setoid_rewrite refineEquiv_bind_unit; simpl;
      f_equiv; intro.
    setoid_rewrite <- filter_Build_single_Tuple_list; rewrite filter_and;
    f_equiv.
  Qed.

  Add Parametric Morphism
      (n : nat)
      (A : Type)
      (f : A -> Type)
      (As : Vector.t A n)
      (a : A)
      (l' : list (ilist2 (B := f) As))
  : (@Join_Comp_Lists n A f As a l')
      with signature
      (pointwise_relation _ refineEquiv) ==> refineEquiv
        as refineEquiv_Join_Comp_Lists.
  Proof.
    unfold pointwise_relation; simpl; intros.
    induction l'; unfold Join_Comp_Lists; simpl.
    - reflexivity.
    - rewrite H; setoid_rewrite IHl'; reflexivity.
  Qed.

  Lemma Join_Comp_Lists_apply_f
        {n}
        {A B C : Type}
        {f : A -> Type}
  : forall (As : Vector.t A n)
           (a : A)
           (l : list (ilist2 (B := f) As))
           (c : ilist2 (B := f) As -> Comp (list (f a)))
           (c' : B -> Comp C) (f' : list (ilist2 (B := f) (a :: As)) -> B),
      refineEquiv (l' <- Join_Comp_Lists l c;
                   c' (f' l'))
                  (l' <- (l' <- Join_Comp_Lists l c; ret (f' l'));
                   c' l').
  Proof.
    split; rewrite refineEquiv_bind_bind;
    setoid_rewrite refineEquiv_bind_unit;
    intros v Comp_v;  computes_to_inv;
    try econstructor; eauto.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_snd
        {n}
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           headings
           idx'
           search_pattern
           (resultComp : ilist2 (B:= @RawTuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           cl,
      refine (l' <- (Join_Comp_Lists (n := n) cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) (_ :: headings) => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagFind r_n search_pattern;
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite refineEquiv_unit_bind.
    rewrite (filter_and_join_ilist2_hd
               (As := headings) (f' := @RawTuple)
               (BagMatchSearchTerm _ search_pattern)
               cl
               (fun _ : ilist2 (B:= @RawTuple) headings =>
                  {l : list RawTuple |
                   EnsembleIndexedListEquivalence (GetIndexedRelation r_n idx') l})).
    simplify with monad laws; f_equiv.
  Qed.

  Corollary refine_Join_Comp_Lists_filter_search_term_snd'
            (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           search_pattern
           (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ search_pattern (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagFind r_n search_pattern;
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; f_equiv; intro.
    apply refine_Join_Comp_Lists_filter_search_term_snd.
  Qed.

  Lemma refine_List_Query_In_Return
        (ElementT ResultT : Type):
    forall (l : list ElementT)
           (f : ElementT -> ResultT),
      refine (List_Query_In l (fun el => Query_Return (f el)) ) (ret (map f l)).
  Proof.
    unfold List_Query_In; induction l; intros; simpl.
    - reflexivity.
    - unfold Query_Return; simplify with monad laws;
      setoid_rewrite IHl; simplify with monad laws;
      reflexivity.
  Qed.

  Lemma filter_and_join_ilist2_hd_dep
        {n}
        {A}
        {a}
        {As : Vector.t A n}
        (f' : A -> Type)
  : forall
      (f : ilist2 (B := f') As -> f' a -> bool)
      (s1 : list (ilist2 (B := f') As))
      (s2 : _ -> Comp (list (f' a)))
      filter_rest,
      refineEquiv (l <- (Join_Comp_Lists s1 s2);
                   ret (filter (fun x : ilist2 (B := f') (a :: As) => f (ilist2_tl x) (ilist2_hd x) && filter_rest x) l))
                  (l <- Join_Comp_Lists s1 (fun a => l <- s2 a; ret (filter (f a) l));
                   ret (filter filter_rest l)).
  Proof.
    split; induction s1; unfold Join_Comp_Lists in *; simpl in *; intros; eauto.
    - simplify with monad laws; rewrite refineEquiv_bind_unit; reflexivity.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, c'; eauto.
    - intros v Comp_v;  computes_to_inv; subst; eauto.
    - simplify with monad laws; intros v Comp_v;
       computes_to_inv; subst; computes_to_econstructor; eauto.
      pose proof (IHs1 _ (BindComputes _ (fun x => ret (_ x)) _ _ Comp_v'0 (ReturnComputes _))).
       computes_to_inv; subst.
      repeat (computes_to_econstructor; eauto).
      rewrite filter_app, filter_map; simpl; eauto.
      repeat rewrite filter_app, filter_map; simpl; eauto.
      rewrite <- filter_and, H'; eauto.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_snd_dep
        {n}
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           (headings : Vector.t _ n)
           idx'
           (search_pattern : _ -> _)
           (resultComp : ilist2 (B:= @RawTuple) (_ :: headings) -> Comp (list ResultT))
           filter_rest
           (cl : list (ilist2 (B:= @RawTuple) headings)),
      refine (l' <- (Join_Comp_Lists cl
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) (_ :: headings) => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (l' <- (Join_Comp_Lists cl
                                     (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite refineEquiv_unit_bind.
    rewrite filter_and_join_ilist2_hd_dep with
    (f := fun tup =>  (BagMatchSearchTerm (ith3 BagIndexKeys idx')
                                          (search_pattern tup))).
    simplify with monad laws; f_equiv.
  Qed.

  Lemma realizeable_Enumerate
  : forall
      (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
      (r_o : UnConstrQueryStructure qs_schema)
      idx,
      DelegateToBag_AbsR r_o r_n ->
      exists v : list RawTuple,
        refine
          (l <- CallBagMethod idx BagEnumerate r_n ();
           ret (snd l))
          (ret v).
  Proof.
    intros; destruct (H idx) as [l [l_eqv l_eqv']].
    Local Transparent CallBagMethod.
    eexists l; unfold CallBagMethod; simpl; simplify with monad laws.
    computes_to_econstructor;  computes_to_inv; subst; eauto.
  Qed.

  Lemma realizeable_Find
  : forall
      (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
      (r_o : UnConstrQueryStructure qs_schema)
      idx st,
      DelegateToBag_AbsR r_o r_n ->
      exists v : list RawTuple,
        refine (l <- CallBagMethod idx BagFind r_n st;
                ret (snd l))
               (ret v).
  Proof.
    intros; destruct (H idx) as [l [l_eqv l_eqv'] ].
    eexists (filter _ l); unfold CallBagMethod; simpl; eauto.
    computes_to_econstructor; eauto.
  Qed.

  Corollary refine_Join_Comp_Lists_filter_search_term_snd_dep'
            (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx idx'
           (search_pattern : _ -> _)
           (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
           filter_rest,
      refine (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                      ret (snd l)));
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
                            resultComp)
             (cl <- CallBagMethod idx BagEnumerate r_n ();
              l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                     (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                      ret (snd l)));
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; f_equiv; intro;
    apply refine_Join_Comp_Lists_filter_search_term_snd_dep.
  Qed.

  Lemma refine_Join_Comp_Lists_filter_search_term_fst
        (ResultT : Type) :
    forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
           idx
           heading
           cl
           (search_pattern : _)
           (resultComp : ilist2 (B:= @RawTuple) [heading ; _] -> Comp (list ResultT))
           (cl_realizable : forall a, exists v, computes_to (cl a) v)
           filter_rest,
      refine (l <- CallBagMethod idx BagEnumerate r_n ();
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => (BagMatchSearchTerm _ search_pattern (ilist2_hd (ilist2_tl a)) && filter_rest a)) l')
                            resultComp)
             (l <- CallBagMethod idx BagFind r_n search_pattern;
              l' <- Join_Comp_Lists (Build_single_Tuple_list (snd l)) cl;
              List_Query_In (filter filter_rest l') resultComp).
  Proof.
    intros; unfold CallBagMethod; simpl.
    repeat setoid_rewrite (refineEquiv_bind_bind);
      repeat setoid_rewrite refineEquiv_bind_unit; simpl.
    f_equiv; unfold pointwise_relation; intros.
    match goal with
      |- refine (l' <- Join_Comp_Lists ?l ?c; (@?f l')) _ =>
      setoid_rewrite (Join_Comp_Lists_apply_f l c) with (c' := fun l => List_Query_In l _)
    end.
    setoid_rewrite <- refineEquiv_unit_bind.
    setoid_rewrite (filter_and_join_ilist_tail
               (fun a0 : ilist2 (B:= @RawTuple) [_] =>_ (ilist2_hd a0))
               (Build_single_Tuple_list a)); eauto.
    simplify with monad laws; f_equiv.
    unfold Build_single_Tuple_list; simpl;
    repeat rewrite filter_map; f_equiv.
    setoid_rewrite refineEquiv_bind_bind; setoid_rewrite refineEquiv_unit_bind;
    reflexivity.
  Qed.

  Require Import Fiat.QueryStructure.Implementation.Operations.General.DeleteRefinements.

  Lemma refineEquiv_Join_Comp_Lists_Build_single_Tuple_list
  : forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys) idx,
      refineEquiv (Join_Comp_Lists [inil2 (B := @RawTuple)]
                                   (fun _ : ilist2 (B:= @RawTuple) [] =>
                                      l <- CallBagMethod idx BagEnumerate r_n ();
                                    ret (snd l)))
                  (l <- CallBagMethod idx BagEnumerate r_n ();
                   ret (Build_single_Tuple_list (snd l))) .
  Proof.
    unfold Join_Comp_Lists, Build_single_Tuple_list; simpl; intros;
    repeat setoid_rewrite refineEquiv_bind_bind;
    repeat setoid_rewrite refineEquiv_bind_unit; f_equiv.
    intros u.
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma refine_BagADT_QSDelete_fst :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx :Fin.t _)
                (DT : Ensemble RawTuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith3 BagIndexKeys idx) search_pattern)
           -> refine {x : list RawTuple |
                      QSDeletedTuples r_o idx DT x}
                     (l <- (CallBagMethod idx BagDelete r_n search_pattern);
                      ret (snd l)).
  Proof.
    intros; setoid_rewrite DeletedTuplesFor; auto.
    rewrite refine_Query_In_Enumerate by eauto.
    setoid_rewrite refine_List_Query_In_Where.
    instantiate (1 := _).
    simpl in *.
    rewrite (refineEquiv_Join_Comp_Lists_Build_single_Tuple_list r_n idx).
    setoid_rewrite refineEquiv_bind_bind at 1.
    setoid_rewrite refineEquiv_bind_bind at 1.
    setoid_rewrite refineEquiv_bind_unit at 1.
    setoid_rewrite <- refineEquiv_bind_bind at 1.
    rewrite (refine_Query_For_In_Find_snd' H _ H0).
    setoid_rewrite refine_List_Query_In_Return.
    unfold Build_single_Tuple_list; setoid_rewrite map_map; simpl.
    setoid_rewrite map_id.
    unfold CallBagMethod; simpl; simplify with monad laws;
    setoid_rewrite refineEquiv_bind_bind;
    setoid_rewrite refineEquiv_bind_unit; simpl;
    f_equiv; intro.
    refine pick val _; eauto.
    reflexivity.
  Qed.

  Lemma NoDup_filter {A} :
    forall (f : A -> bool)
           (l : list A),
      NoDup l
      -> NoDup (filter f l).
  Proof.
    induction l; simpl.
    - constructor.
    - case_eq (f a); simpl; intros.
      + inversion H0; constructor; eauto.
        subst; unfold not; intros H1;
        apply filter_In in H1; intuition.
      + inversion H0; eauto.
  Qed.

  Lemma NoDup_filter_map {A} :
    forall (f : A -> bool)
           (l : list _),
      NoDup (map elementIndex l)
      -> NoDup
           (map elementIndex
                (filter (fun a => f (indexedElement a)) l)) .
  Proof.
    induction l; simpl.
    - constructor.
    - case_eq (f (indexedElement a)); simpl; intros; inversion H0; subst; eauto.
      constructor; eauto.
      unfold not; intros; apply H3.
      revert H1; clear; induction l; simpl.
      + eauto.
      + case_eq (f (indexedElement a0)); simpl; intros; intuition.
  Qed.

  Lemma refine_BagADT_QSDelete_snd :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx :Fin.t _)
                (DT : Ensemble RawTuple)
                (DT_Dec : DecideableEnsemble DT)
                search_pattern,
           ExtensionalEq (@dec _ _ DT_Dec)
                         (BagMatchSearchTerm (ith3 BagIndexKeys idx) search_pattern)
           -> refine
                {r_n' |
                 DelegateToBag_AbsR
                   (UpdateUnConstrRelation r_o idx (EnsembleDelete
                                                      (GetUnConstrRelation r_o idx)
                                                      DT)) r_n'}
                (l <- (CallBagMethod idx BagDelete r_n search_pattern);
                 ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
    intros.
    computes_to_constructor;  computes_to_inv.
    unfold CallBagMethod in *; simpl in *;  computes_to_inv; subst.
    simpl.
    unfold DelegateToBag_AbsR; intros.
    - destruct (fin_eq_dec idx idx0); subst.
      + rewrite get_update_unconstr_eq, get_update_indexed_eq.
        unfold DelegateToBag_AbsR in H.
        destruct (H idx0) as
            [l [[[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]
                  [[bnd' fresh_bnd'] [l'' [l''_eq [l''_eqv NoDup_l'']]]]]].
        exists (filter (fun a => negb (dec a)) l); repeat split.
        * exists bnd; unfold EnsembleDelete, UnConstrFreshIdx; intros.
          inversion H2; subst; eauto.
        * unfold UnIndexedEnsembleListEquivalence;
          exists (filter (fun a => negb (dec (indexedElement a))) l'); split; eauto.
          rewrite <- l'_eq; rewrite filter_map; reflexivity.
          intuition.
          apply filter_In; split.
          eapply l_eqv; inversion H2; eauto.
          inversion H2; subst; rewrite (proj2 (Decides_false _ _)); eauto.
          rewrite filter_In in H2; intuition; constructor;
          [ apply l_eqv; eauto
          | case_eq (dec (indexedElement x)); intros H'; rewrite H' in H4;
            try discriminate;
            eapply Decides_false in H'; eauto ].
          eapply NoDup_filter_map with (f := fun a => negb (dec a)); eauto.
        * exists bnd'; unfold EnsembleDelete, UnConstrFreshIdx; intros.
          inversion H2; subst; eauto.
        * unfold UnIndexedEnsembleListEquivalence;
          exists (filter (fun a => negb (dec (indexedElement a))) l''); split; eauto.
          rewrite <- l''_eq; rewrite filter_map; reflexivity.
          intuition.
          apply filter_In; split.
          eapply l''_eqv; inversion H2; eauto.
          inversion H2; subst; rewrite (proj2 (Decides_false _ _)); eauto.
          unfold Complement, In in *.
          intro; apply H4.
          rewrite <- H0.
          apply dec_decides_P; eauto.
          rewrite filter_In in H2; intuition; constructor;
          [ apply l''_eqv; eauto
          | case_eq (dec (indexedElement x)); intros H'; rewrite H' in H4;
            try discriminate;
            eapply Decides_false in H'; eauto ].
          unfold Complement, In; rewrite <- H0;
          eapply Decides_false in H'; rewrite H'; congruence.
          eapply NoDup_filter_map with (f := fun a => negb (dec a)); eauto.
      + rewrite get_update_unconstr_neq, get_update_indexed_neq; eauto.
  Qed.

  Lemma refine_Pick_DelegateToBag_AbsR
    : forall r_o r_n,
      DelegateToBag_AbsR r_o r_n
      -> refine {r_n : IndexedQueryStructure qs_schema BagIndexKeys |
                 DelegateToBag_AbsR r_o r_n}
                (ret r_n).
  Proof.
    intros; refine pick val r_n; eauto; reflexivity.
  Qed.

  Lemma refine_BagADT_QSInsert :
    forall r_o (r_n : IndexedQueryStructure qs_schema BagIndexKeys),
      DelegateToBag_AbsR r_o r_n
      -> forall (idx :Fin.t _)
                t freshIdx,
        UnConstrFreshIdx (GetUnConstrRelation r_o idx) freshIdx
        -> refine
             {r_n' |
               DelegateToBag_AbsR
                 (UpdateUnConstrRelation r_o idx (
                                           EnsembleInsert
                                             {| indexedElement := t; elementIndex := freshIdx |}
                                             (GetUnConstrRelation r_o idx))) r_n'}
             (l <- (CallBagMethod idx BagInsert r_n t);
              ret (UpdateIndexedRelation r_n idx (fst l))).
  Proof.
    unfold refine; intros.
    unfold CallBagMethod in *; simpl in *; computes_to_inv; subst.
    computes_to_econstructor; simpl.
    unfold DelegateToBag_AbsR in *; intuition; intros.
    intros; destruct (fin_eq_dec idx idx0); subst.
    - rewrite get_update_unconstr_eq, get_update_indexed_eq.
      destruct (H idx0) as
          [l [[[bnd fresh_bnd] [l' [l'_eq [l_eqv NoDup_l']]]]
                [[bnd' fresh_bnd'] [l'' [l''_eq [l''_eqv NoDup_l'']]]]]].
      exists (cons t l); repeat split.
      + exists (S freshIdx); unfold EnsembleInsert, UnConstrFreshIdx; intros.
        unfold UnConstrFreshIdx in H0; intuition; subst; simpl; eauto.
      + unfold UnIndexedEnsembleListEquivalence;
                 exists ({| indexedElement := t; elementIndex := freshIdx |} :: l')%list; intuition.
        * simpl in *; rewrite l'_eq; trivial.
        * simpl; destruct H2;
          [left; symmetry; exact H2
           | right; apply l_eqv; eauto].
        * unfold EnsembleInsert; destruct H2;
          [rewrite <- H2; left; trivial
           | right; eapply l_eqv; eauto ].
        * simpl; apply NoDup_cons; eauto.
          unfold not; intros;
          apply in_map_iff in H2; destruct H2; destruct H2;
            apply l_eqv in H3. unfold UnConstrFreshIdx in H0;
            unfold In in H2; apply H0 in H3;
            unfold GetNRelSchema in *; omega.
      + exists (S v1); unfold Add, UnConstrFreshIdx; intros.
        inversion H2; subst.
        unfold UnConstrFreshIdx in H1; intuition; subst; simpl; eauto.
        inversion H3; subst.
        simpl; eauto.
      + unfold UnIndexedEnsembleListEquivalence;
                 exists ({| indexedElement := t; elementIndex := v1 |} :: l'')%list; intuition.
        * simpl in *; rewrite l''_eq; trivial.
        * simpl; destruct H2;
          [right; apply l''_eqv; eauto |
           left; inversion H2; reflexivity ].
        * unfold Add; destruct H2;
          [ right; subst; econstructor
          | left; eapply l''_eqv; eauto ].
        * simpl; apply NoDup_cons; eauto.
          unfold not; intros;
          apply in_map_iff in H2; destruct H2; destruct H2;
            apply l''_eqv in H3; unfold UnConstrFreshIdx in H1;
            unfold In in H2; apply H1 in H3;
            unfold GetNRelSchema in *; omega.
      - rewrite get_update_unconstr_neq, get_update_indexed_neq; eauto.
  Qed.


Corollary refine_Join_Comp_Lists_filter_filter_search_term_snd_dep'
          (ResultT : Type) :
  forall (r_n : IndexedQueryStructure qs_schema BagIndexKeys)
         idx idx'
         (search_pattern : _ -> _)
         (resultComp : ilist2 (B:= @RawTuple) [_; _] -> Comp (list ResultT))
         filter_rest st,
    refine (cl <- CallBagMethod idx BagFind r_n st;
            l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                   (fun _ => l <- CallBagMethod idx' BagEnumerate r_n ();
                                    ret (snd l)));
            List_Query_In (filter (fun a : ilist2 (B:= @RawTuple) [_ ; _] => BagMatchSearchTerm _ (search_pattern (ilist2_tl a)) (ilist2_hd a) && filter_rest a) l')
                          resultComp)
           (cl <- CallBagMethod idx BagFind r_n st;
            l' <- (Join_Comp_Lists (Build_single_Tuple_list (snd cl))
                                   (fun tup => l <- CallBagMethod idx' BagFind r_n (search_pattern tup);
                                    ret (snd l)));
            List_Query_In (filter filter_rest l') resultComp).
Proof.
  intros; f_equiv; intro;
  apply refine_Join_Comp_Lists_filter_search_term_snd_dep.
Qed.

End BagsQueryStructureRefinements.
