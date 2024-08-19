Require Import GrtA GrtI.
Require Import HoareDef SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem ModSemE Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 STB Invariant.

Require Import IProofMode IRed ITactics.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
        
  Variable GlobalStbM: Sk.t -> gname -> option fspec.

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun _ _ => (True)%I.

  Lemma simF_test:
    HModPair.sim_fun
      (GrtA.HChoose GlobalStbM) GrtI.Choose
      Ist "test".
  Proof.
    simF_init GrtA.HChoose_unfold GrtI.Choose_unfold testF GrtI.testF.

    st_l. hss. iDestruct "ASM" as "(W & (% & %Y))".
    subst. hss.
    apc_l.

    st_r. iDestruct "GRT" as "%". ss.
  Qed.
  
  Theorem sim: HModPair.sim (GrtA.HChoose GlobalStbM) GrtI.Choose Ist.
  Proof.
    sim_init.
    - rewrite// GrtA.HChoose_unfold GrtI.Choose_unfold. s.
      iIntros "E"; iFrame.
    - iApply simF_test. ss.
  Qed.
  
End SIMMODSEM.
