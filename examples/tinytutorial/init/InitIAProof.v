Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef IPM.
Require Import sProp sWorld World SRF.
Require Import InitI InitA InitRA.
Require Import Relation_Operators.
Require Import RelationPairs.

Require Import SimModSemFacts IProofMode IRed ITactics.


Set Implicit Arguments.

Section SIM.
  Context `{_I: InitRA.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Let Ist : Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt => 
          (pending ∗ (∃n:Z, ⌜st_src = n↑ /\ st_tgt = (Vint n)↑⌝ )) ∨ (callable ∗ emp)
    )%I.

  Theorem sim: HModPair.sim (InitA.Init GlobalStb) (InitI.Init) Ist.
  Proof.
    sim_init.
    - (* initial condition *)
      admit.
    - (* init *)
      unfold cfunU, initF, InitI.initF, interp_sb_hp, HoareFun, ccallU. s.
      admit.
    - (* incr *)
      unfold cfunU, incrF, InitI.incrF, interp_sb_hp, HoareFun, ccallU. s.
      admit.
    - (* final *)
      unfold cfunU, finalF, InitI.finalF, interp_sb_hp, HoareFun, ccallU. s.
      admit.
  Admitted.

End SIM.




(*******************************************************)


















































  (* Theorem sim: HModPair.sim (InitA.Init GlobalStb) (InitI.Init) Ist.
  Proof.
    sim_init.
    - (* initial condition *)
      iIntros "H". iSplitR; eauto. steps. iRight. eauto.
    - (* init *)
      unfold cfunU, initF, InitI.initF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (P & %))".
      iDestruct "IST" as "[IST|IST]".
      { iDestruct "IST" as "(P' & _)". iExFalso. iApply (pending_unique with "P P'"). }
      iDestruct "IST" as "[C _]". subst.
      rewrite G. steps.
      rewrite G0. steps.
      force. force.
      iSplitL "C W". { iFrame. eauto. }
      steps. iSplitL; eauto.
      iLeft. iFrame. iPureIntro. exists (1:Z). eauto.
    - (* incr *)
      unfold cfunU, incrF, InitI.incrF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (C & %))". subst.
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      { iDestruct "IST" as "[C' _]". iExFalso. iApply (callable_unique with "C C'"). }
      iDestruct "IST" as "[P N]". iDestruct "N" as ( ? ) "%". des. subst.  
      rewrite Any.upcast_downcast in G1. inv G1. rewrite G.
      steps. rewrite G0. steps.
      force. force. iSplitL "W C".
      { iFrame. eauto. }
      steps. iSplitL; eauto.
      { iLeft. iFrame. iPureIntro. exists (y5 + 1)%Z. eauto. }
    - (* final *)
      unfold cfunU, finalF, InitI.finalF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (C & %))". subst.
      rewrite G. steps. rewrite G0. steps.
      force. force. iSplitL "W". { iFrame. eauto. }
      steps. iFrame. eauto. 
  Qed. *)