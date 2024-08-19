Require Import ChooseA ChooseI.
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
      (ChooseA.HChoose GlobalStbM) ChooseI.Choose
      Ist "test".
  Proof.
    simF_init ChooseA.HChoose_unfold ChooseI.Choose_unfold testF ChooseI.testF.

    st_l. hss. iDestruct "ASM" as "(W & (% & %Y))".
    subst. hss.
    rewrite interp_hAGEs_hapc. hss. unfold HoareAPC. force_l.
    rewrite unfold_APC. st_l. force_l. des_ifs. st_l. force_l. st_l.
    force_l. force_l. iSplitL "W"; et.
    st. iFrame. et.
    Unshelve. exact 0.
  Qed.
  
  Theorem sim: HModPair.sim (ChooseA.HChoose GlobalStbM) ChooseI.Choose Ist.
  Proof.
    sim_init.
    - rewrite// ChooseA.HChoose_unfold ChooseI.Choose_unfold. s.
      iIntros "E"; iFrame.
    - iApply simF_test. ss.
  Qed.
  
End SIMMODSEM.
