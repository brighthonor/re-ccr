Require Import ModFairTest2A ModFairTest2I ModFairA ModFairNot ModFairANotproof.
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

Require Import WFLibLarge FairCounter.
From Ordinal Require Import ClassicalOrdinal.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
        
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCL: forall sk, stb_incl (to_stb (FairStb nat)) (GlobalStb sk).
  Hypothesis STB_fair: forall sk, (GlobalStb sk) "fair" = Some (fair_spec nat).

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => (⌜True⌝)%I.

  Ltac coapply :=
    iApply isim_progress;
    iApply isim_base;
    match goal with [|- context[_ _ _ _ _ (?st_src, _) (?st_tgt, _)]] =>
      iApply ("CIH" $! (@existT _ (λ _, _) st_src st_tgt)); eauto
    end.

  Lemma simF_test:
    forall i_src: iimap nat owf,
    HModPair.sim_fun
      (HMod.add (ModFairTest2A.HFair GlobalStb) (ModFairA.HFair i_src))
      (HMod.add ModFairTest2I.Fair (ModFairA.HFair (@i_zero nat)))
      (IstProd Ist (IstFairSrc nat)) "test".
  Proof.
    simF_init ModFairTest2A.HFair_unfold ModFairTest2I.Fair_unfold ModFairTest2A.testF ModFairTest2I.testF.
  Admitted.
  
  Theorem sim: 
    forall i_tgt: iimap nat nat_wf,
      HModPair.sim 
        (HMod.add (ModFairTest2A.HFair GlobalStb) (ModFairNot.HUnFair i_tgt (GlobalStb)))
        (HMod.add ModFairTest2I.Fair (ModFairA.HFair i_tgt)) 
        (IstProd Ist (IstFairTgt nat)).
  Proof.
  Admitted.

End SIMMODSEM.
