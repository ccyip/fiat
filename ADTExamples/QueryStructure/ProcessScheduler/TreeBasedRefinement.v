Require Import String Omega List FunctionalExtensionality Ensembles
        Computation ADT ADTRefinement ADTNotation BuildADTRefinements
        QueryStructureSchema QueryStructure
        QueryQSSpecs InsertQSSpecs EmptyQSSpecs
        GeneralInsertRefinements GeneralQueryRefinements
        GeneralQueryStructureRefinements
        ListQueryRefinements ListInsertRefinements
        ListQueryStructureRefinements
        ProcessScheduler.AdditionalLemmas
        DBSchema SetEq.

Require Import Bags.
Require Import FMapAVL OrderedTypeEx.
Require Import FMapExtensions.
Require Import DBSchema SetEq AdditionalLemmas.
Require Export ADTRefinement.BuildADTRefinements.

Unset Implicit Arguments.

Module GenericTreeDB := FMapAVL.Make(Nat_as_OT). (* TODO: Add the generic implementation *)
(*Module Import DBExtraFacts := FMapExtensions GenericTreeDB.*)

Definition PIDIndex : @BagPlusBagProof (@Tuple ProcessSchema).
Proof.
  mkIndex ProcessSchema [STATE; PID].
Defined.

(* TODO: Remove: Definition PIDIndexedTree := BagType PIDIndex. *)

(* TODO: Rename BagPlusBagProof to BagSpecification *)

Definition Storage := AddCachingLayer (BagProof PIDIndex) (fun p => p PID)
                                      0 max (ListMax_cacheable 0).

Definition StorageType           := BagType Storage.
Definition StorageIsBag          := BagProof Storage.
Definition StorageSearchTermType := SearchTermType Storage.

Section TreeBasedRefinement.
  Open Scope type_scope.
  Open Scope Tuple_scope.

  Definition NeatDB := StorageType.

  Definition NeatDB_equivalence old_rep (neat_db: NeatDB) :=
    let set_db := GetUnConstrRelation old_rep PROCESSES in
    EnsembleListEquivalence set_db (benumerate neat_db).

  Definition ObservationalEq {A B} f g :=
    forall (a: A), @eq B (f a) (g a).

  Lemma filter_by_equiv :
    forall {A} f g,
      ObservationalEq f g ->
      forall seq, @List.filter A f seq = @List.filter A g seq.
  Proof.
    intros A f g obs seq; unfold ObservationalEq in obs; induction seq; simpl; try rewrite obs; try rewrite IHseq; trivial.
  Qed.

  Lemma filter_on_key :
    forall (tree: StorageType) (key: nat),
      SetEq
        (List.filter
           (fun (p: Process) => beq_nat (p PID) key)
           (benumerate tree))
        (bfind tree (None, (Some key, bstar))).
  Proof.
    intros tree key.

    rewrite (filter_by_equiv _ (@bfind_matcher _ _ _ StorageIsBag (None, (Some key, bstar)))).
    apply (bfind_correct).
    
    unfold ObservationalEq.
    simpl.
    intros.
    rewrite (NatTreeExts.KeyFilter_beq beq_nat) by apply NPeano.Nat.eqb_spec.
    rewrite andb_true_r; unfold cast; trivial.
  Qed.

  Notation "x '∈' y" := (In _ y x) (at level 50, no associativity).

  Lemma no_collisions_when_using_a_fresh_pid :
    forall pid c (tup tup': Process),
      tupleAgree tup tup' [PID_COLUMN]%SchemaConstraints ->
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      tup PID = pid ->
      GetUnConstrRelation c PROCESSES tup' ->
      False.
  Proof.
    unfold tupleAgree, GetAttribute;
    simpl;
    intuition;
    specialize (H0 tup' H2);
    specialize (H PID);
      subst;
      intuition.
  Qed.

  Lemma insert_always_happens :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>) tup'
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

  Lemma tupleAgree_sym :
    forall (heading: Heading) tup1 tup2 attrs,
      @tupleAgree heading tup1 tup2 attrs <-> @tupleAgree heading tup2 tup1 attrs.
  Proof.
    intros; unfold tupleAgree.
    intuition; symmetry; intuition.
  Qed.

  Lemma insert_always_happens' :
    forall pid c,
      (forall a, (GetUnConstrRelation c PROCESSES) a -> pid > (a PID)) ->
      refine
        {b |
         decides b
                 (forall tup' : Tuple,
                    GetUnConstrRelation c PROCESSES tup' ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [PID_COLUMN]%SchemaConstraints ->
                    tupleAgree
                      tup' (<PID_COLUMN :: pid, STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>)
                      [CPU_COLUMN; STATE_COLUMN]%SchemaConstraints)
                    }
        (ret true).
  Proof.
    intros; constructor; inversion_by computes_to_inv; subst; simpl.
    intros; exfalso; rewrite tupleAgree_sym in H1; apply (no_collisions_when_using_a_fresh_pid pid c _ _ H1); trivial.
  Qed.

  Lemma get_update_unconstr_iff :
    forall db_schema qs table new_contents,
    forall x,
      x ∈ GetUnConstrRelation (UpdateUnConstrRelation db_schema qs table new_contents) table <->
      x ∈ new_contents.
  Proof.
    unfold GetUnConstrRelation, UpdateUnConstrRelation, RelationInsert;
    intros; rewrite ith_replace_BoundIndex_eq;
    reflexivity.
  Qed.

  Lemma NeatScheduler :
    Sharpened ProcessSchedulerSpec.
  Proof.
    unfold ProcessSchedulerSpec.

    unfold ForAll_In; start honing QueryStructure.

    hone representation using NeatDB_equivalence.
    
    (* (* TODO: Why does adding this followed simpl break the 
          Equivalent_UnConstr_In_EnsembleListEquivalence rewrite? *) 
      unfold UnConstrQuery_In.
     (*simpl.*) *)

    hone constructor INIT. {
      unfold NeatDB_equivalence, DropQSConstraints_SiR.
      repeat setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      repeat setoid_rewrite refineEquiv_pick_eq'.
      simplify with monad laws.

      rewrite refine_pick_val;
        [ | instantiate (1 := bempty); apply EnsembleListEquivalence_Empty ].

      subst_body; higher_order_1_reflexivity. 
    }

    hone method ENUMERATE. {
      unfold NeatDB_equivalence in H.

      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence);
        eauto. (* TODO: Could explicitly pass the right list *)

      setoid_rewrite Equivalent_List_In_Where.

      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ StorageIsBag (Some n, (None, []))))
        by (
            unfold ObservationalEq; simpl; 
            unfold NatTreeExts.KeyFilter;
            unfold NatTreeExts.MoreFacts.BasicProperties.F.eq_dec;
            
            intros;
            rewrite ?andb_true_r, ?andb_true_l;
            intuition
          ).

      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (Some n, (None, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }    

    (* TODO: s/Decideable/Decidable/ *)
    (* TODO: Use rewrite by instead of [ ... | eassumption ] *)
    (* TODO: Handle the 'projection' parameter differently; 
             right now it appears explicitly in plenty of 
             places, and since it is infered in KeyFilter 
             it makes it possble to swap same-type search terms,
             delaying the failure until the call to bfind_correct *)
    (* TODO: The backtick notation from bounded indexes cannot be input *)
    (* TODO: The insert_always_happens scripts could probably be made more generic *)
    
    hone method GET_CPU_TIME. {
      unfold NeatDB_equivalence in H.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.

      rewrite (Equivalent_UnConstr_In_EnsembleListEquivalence);
        eauto. (* TODO: Could explicitly pass the right list *)

      setoid_rewrite Equivalent_List_In_Where.
      rewrite (filter_by_equiv dec (@bfind_matcher _ _ _ StorageIsBag (None, (Some n, [])))) 
        by (
            unfold ObservationalEq; simpl; 
            unfold NatTreeExts.KeyFilter;
            unfold NatTreeExts.MoreFacts.BasicProperties.F.eq_dec;
            
            intros;
            rewrite ?andb_true_r, ?andb_true_l;
            intuition
          ).
      setoid_rewrite (@bfind_correct _ _ _ StorageIsBag r_n (None, (Some n, []))).
      setoid_rewrite refine_For_List_Return.
      simplify with monad laws.

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.
      finish honing.
    }

    hone method SPAWN. {
      unfold NeatDB_equivalence in H.
      
      setoid_rewrite refineEquiv_pick_ex_computes_to_and.
      setoid_rewrite refineEquiv_pick_pair.
      setoid_rewrite refineEquiv_pick_eq'. 
      simplify with monad laws.
      simpl.
 
      assert (forall tup : Tuple,
                GetUnConstrRelation c PROCESSES tup ->
                S (ccached_value r_n) > tup!PID_COLUMN) 
        by (
            intros;
            rewrite <- (cfresh_cache r_n);
            apply (cached_max_gt_projected (fun (p: Process) => p!PID_COLUMN));
            unfold EnsembleListEquivalence, In in H;               (* TODO: Get rid of this unfold *)
            rewrite <- H; assumption                               (* TODO: What is this spurious GetAttribute? *)
          ).

      rewrite refine_pick_val by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens by eassumption.
      simplify with monad laws.

      rewrite insert_always_happens' by eassumption.
      simplify with monad laws.

      unfold NeatDB_equivalence.

      rewrite refine_pick_val;
        [ | instantiate (1 := (binsert r_n <PID_COLUMN :: (S (ccached_value r_n)), STATE_COLUMN :: SLEEPING, CPU_COLUMN :: 0>))].

      simplify with monad laws.

      finish honing.

      (* Insert correct *)
      unfold EnsembleListEquivalence in *.

      setoid_rewrite (@binsert_enumerate _ _ _ StorageIsBag).
      setoid_rewrite get_update_unconstr_iff.
      setoid_rewrite <- H.
      unfold RelationInsert, In in *;
      intuition.
    }

    finish sharpening.
  Defined.
End TreeBasedRefinement.
