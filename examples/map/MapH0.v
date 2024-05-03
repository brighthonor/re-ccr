Require Import MapHeader MapI MapM HoareDef HPSim HPSimFacts.
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
Require Import HPTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB Invariant.

Set Implicit Arguments.

Local Open Scope nat_scope.


Section H0.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG MapRA0 Σ}.
  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.
  Definition MapH0: HMod.t := HMod.lift MapI.Map.
  Definition MapH1 o: HMod.t := SMod.to_hmod (GlobalStbM (SMap.(SMod.sk))) o MapM.SMap.

  Lemma asdf o: HModPair.sim (MapH1 o) MapH0.
  Proof.
    econs; et. ii. econs; cycle 1.
    { (* invariant *) admit. }
    econs.
    {
      econs; et.  
    }



End H0.