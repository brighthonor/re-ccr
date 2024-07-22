
(*** PROOF ***)
Require Import Singleton0 Singleton1 SingletonRA HoareDef SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import IPM IProofMode ITactics.
Require Import sProp sWorld World SRF.


Set Implicit Arguments.

Local Open Scope nat_scope.

Section PRF.
  Context `{_S: SingletonRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  (* Beware that Union(∨) is not '\' + '/', but '\vee'... *)
  Let Ist: Any.t -> Any.t -> iProp :=
    (fun _ st_tgt => 
             ((⌜st_tgt = (1: Z)%Z↑⌝ ∗ Ready)
              ∨ (⌜exists m: Z, m <> 1 /\ st_tgt↓ = Some m⌝ ∗ Fired))%I).

  Theorem sim: HModPair.sim (Singleton1.Singleton GlobalStb) (Singleton0.Singleton) Ist.
  Proof.
    sim_init.
    - (* initial condition *)
      admit.
    - (* singleton (fun 1) *)
      unfold cfunU, singletonF, singletonA, interp_sb_hp, HoareFun, ccallU. s.
      admit.
  Admitted.

End PRF.









(*********************************************************************)


















































  (* Theorem sim: HModPair.sim (Singleton1.Singleton GlobalStb) (Singleton0.Singleton) Ist.
  Proof.
    sim_init.
    - (* initial condition *)
      iIntros "R". iSplitR; eauto. steps.
      iLeft. eauto.
    - (* singleton (fun 1) *)
      unfold cfunU, singletonF, singletonA, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (% & B) & %)". subst.
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      { iDestruct "IST" as "[% F]". iExFalso. iApply (FiredBall with "F B"). }
      iDestruct "IST" as "[% R]". subst. 
      force. force. iSplitL "W". { eauto. }
      steps. force. steps.
      iSplit; eauto. iRight.
      iSplitR.
      { iPureIntro. exists 0. rewrite Any.upcast_downcast. split; [lia|f_equal]. }
      { iApply ReadyBall. iFrame. }
    Unshelve. lia.
  Qed.  *)
