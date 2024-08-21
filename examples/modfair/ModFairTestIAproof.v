Require Import ModFairTestA ModFairTestI ModFairA ModFairAproof.
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

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
        
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb (FairStb nat)) (GlobalStb sk).

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => (⌜True⌝)%I.

  Ltac coapply :=
    iApply isim_progress;
    iApply isim_base;
    match goal with [|- context[_ _ _ _ _ (?st_src, _) (?st_tgt, _)]] =>
      iApply ("CIH" $! (@existT _ (λ _, _) st_src st_tgt)); eauto
    end.

  Definition i_kappa: iimap nat owf := @i_kappa nat.

  Lemma simF_test:
    forall i_tgt: iimap nat nat_wf,
    HModPair.sim_fun
      (HMod.add (ModFairTestA.HFair GlobalStb) (ModFairA.HFair i_kappa))
      (HMod.add ModFairTestI.Fair (ModFairA.HFair i_tgt))
      (IstProd Ist (IstFairTgt nat)) "test".
  Proof.
    simF_init ModFairTestA.HFair_unfold ModFairTestI.Fair_unfold ModFairTestA.testF ModFairTestI.testF.

    st_l. hss. iDestruct "ASM" as "(W & (% & %Y))". subst. hss. st_r. grind.
    iApply isim_progress.
        
    (* To prove a situation of infinity, use coinduction *)
    iStopProof.
    revert st_src st_tgt. apply combine_quant. (* boilerplate for coinduction *)
    eapply isim_coind.
    i. destruct a as [st_src st_tgt]. s.
    iIntros "(#(_ & CIH) & [IST W])".
    (* Now we can use a coinduction hypothesis *)
    
    rewrite// [X in isim _ _ _ _ _ _ _ _ (_, (translate _ (interp_hEs_hAGEs _ _ X)) >>= _) (_, _)] unfold_iter_eq.
    rewrite// [X in isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ X) >>= _)] unfold_iter_eq.
    st_r. destruct y.
    
    (* CASE 1: fair case *)
    {
      (* Inlining fair function *)
      inline_r. s.
      st_r. force_r. instantiate (1:=mk_meta y0 y1 ()). st_r. force_r. st_r. force_r.
      iSplitR "IST".
      { iFrame. iPureIntro. esplits; et. }
      unfold ModFairA.fairF. st_r. unfold cfunU. hss.
      iDestruct "IST" as (? ? ? ?) "[% [_ %]]". des; subst. 
      st_r. hss. st_r. unfold Fair. st_r. hss. hss.
      rename itgt into prev. rename y into next.
      iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]"; des; subst. st_r.
      st. coapply. iClear "CIH".
      unfold IstProd, Ist, IstFairTgt. iFrame.
      iExists (st_srcL), (st_tgtL), (isrc↑), (next↑). iSplit.
      - iPureIntro. esplits; ss.
      - iSplit; ss. iPureIntro. esplits; et. ii. 
        specialize (H2 f i). specialize (H i).
        unfold fair_update, mirror_update in *. 
        des_ifs; ss.
        3:{}
        + admit.
        + rewrite H. ss.
        +
        + etrans. apply OrdArith.lt_from_nat. eapply H. ss.
        + rewrite H. ss.
        + 
    }
    (* CASE 2: unfair case *)
    {
      inline_r. s.
      st_r. force_r. instantiate (1:=mk_meta y0 y1 ()). st_r. force_r. st_r. force_r.
      iSplitR "IST".
      { iFrame. iPureIntro. esplits; et. }
      unfold ModFairA.fairF. st_r. unfold cfunU. hss.
      iDestruct "IST" as (? ? ? ?) "[% [_ %]]". des; subst.
      st_r. hss. st_r. unfold Fair. st_r. hss. hss.
      rename itgt into prev. rename y into next.
      iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]"; des; subst. st_r.
      unfold FairCounter.fair_update, ff in H. specialize (H 1). ss.

      remember (prev 1) as chance. clear Heqchance. gen next.
      induction chance.
      { ii. inv H. }
      {
        ii. rewrite// [X in isim _ _ _ _ _ _ _ _ (_, _) (_, (translate _ X) >>= _)] unfold_iter_eq.
        st_r. destruct y.
        (* If the next case is fair, the previous unfair one won't be an issue. *)
        {
          st_r. inline_r. s. st_r. force_r. instantiate (1:=mk_meta y0 y1 ()). st_r. force_r.
          st_r. force_r. iSplitL.
          { iFrame. iPureIntro. et. }
          unfold fairF. st_r. unfold cfunU. hss.
          st_r. hss. st_r. unfold Fair. st_r. hss. hss.
          iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]"; des; subst. st.
          coapply. iClear "CIH".
          unfold IstProd, Ist, IstFairTgt. iFrame.
          iExists (st_srcL), (st_tgtL), (st_srcR), (y↑). iSplit; [|iSplit; esplits; et].
          iPureIntro. esplits; ss.
        }

        (* Consecutive unfair case *)
        {
          st_r. inline_r. s. st_r. force_r. instantiate (1:=mk_meta y0 y1 ()). st_r. force_r. st_r.
          force_r. iSplitL.
          { iFrame; iPureIntro; et. }
          unfold fairF. st_r. unfold cfunU. hss. st_r. hss. hss. st_r.
          unfold Fair. st_r. hss. hss.
          iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]"; des; subst. st_r.
          apply IHchance. clear IHchance.
          specialize (H0 1). ss. nia.
        }
      }
    }
  Qed.
  
  Theorem sim: 
    forall ii, 
      HModPair.sim 
        (ModFairTestA.HFair GlobalStb)
        (HMod.add ModFairTestI.Fair (ModFairA.HFair ii)) 
        (IstProd Ist IstFairTgt).
  Proof.
    ii. 
    econs; eauto; ii.
    - Locate HModSemPair.sim.
    econs. cycle 1; [s|sim_split].
    sim_init.
    - rewrite// ModFairTestA.HFair_unfold ModFairTestI.Fair_unfold. s.
      iIntros "E"; iFrame. unfold IstProd. iExists _, _, _, _.
      iSplit; ss. iSplit; ss. unfold IstFairTgt. iPureIntro. et.
    - iApply simF_test. ss.
    - 
  Qed.
  
End SIMMODSEM.
