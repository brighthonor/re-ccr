Require Import HoareDef MapHeader MapM MapA SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
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

Require Import ProofMode STB Invariant.
Require Import Mem1.

Require Import SimModSemFacts IProofMode IRed ITactics.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
  Context `{@GRA.inG MapRA Γ}.
  Context `{@GRA.inG MapRA0 Γ}.
  Context `{@GRA.inG CallableRA Γ}.
  Context `{@GRA.inG memRA Γ}. 

  Section LEMMA. 
    Local Transparent unallocated map_points_to initial_map black_map pending pending0.

    Lemma unallocated_alloc' sz
      (POS: Z.to_nat sz > 0)
      :
      unallocated sz -∗ (map_points_to sz 0 ∗ unallocated (Z.succ sz)).
    Proof.
      unfold map_points_to, unallocated. iIntros "H".
      replace (unallocated_r sz) with ((map_points_to_r sz 0) ⋅ (unallocated_r (Z.succ sz))).
      { iDestruct "H" as "[H0 H1]". iFrame. }
      unfold unallocated_r, map_points_to_r. ur. f_equal.
      { ur. auto. }
      { ur. unfold Auth.white. f_equal. ur. extensionality k.
        ur. des_ifs; try by (exfalso; lia).
      }
    Qed.

    Lemma unallocated_alloc (sz: nat)
      :
      unallocated sz -∗ (map_points_to sz 0 ∗ unallocated (Z.pos (Pos.of_succ_nat sz))).
    Proof.
      unfold map_points_to, unallocated. iIntros "H".
      replace (unallocated_r sz) with ((map_points_to_r sz 0) ⋅ (unallocated_r (S sz))).
      { ss. iDestruct "H" as "[H0 H1]". iFrame. }
      unfold unallocated_r, map_points_to_r. ur. f_equal.
      { ur. auto. }
      { ur. unfold Auth.white. f_equal. ur. extensionality k.
        ur. des_ifs; try by (exfalso; lia).
      }
    Qed.

    Lemma initial_map_initialize sz
      :
      initial_map -∗ (black_map (fun _ => 0%Z) ∗ initial_points_tos sz ∗ unallocated sz).
    Proof.
      induction sz.
      { ss. iIntros "H". unfold initial_map.
        replace initial_map_r with ((black_map_r (fun _ => 0%Z)) ⋅ (unallocated_r 0)).
        { iDestruct "H" as "[H0 H1]". iFrame. }
        { unfold initial_map_r, black_map_r, unallocated_r. ur. f_equal.
          { ur. auto. }
          { ur. f_equal. ur. extensionality k. ur. des_ifs. }
        }
      }
      { iIntros "H". iPoseProof (IHsz with "H") as "H". ss.
        iDes. iPoseProof (unallocated_alloc with "A0") as "A0". iFrame. auto.
      }
    Qed.

    Lemma initial_map_no_points_to k v
      :
      initial_map -∗ map_points_to k v -∗ ⌜False⌝.
    Proof.
      unfold initial_map, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. rr in H3. ur in H3. unseal "ra". des.
      rr in H4. ur in H4. unseal "ra". des.
      rr in H4. des. ur in H4. eapply equal_f with (x:=k) in H4.
      ur in H4. des_ifs.
    Qed.

    Lemma unallocated_range sz k v
      :
      unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
    Proof.
      unfold unallocated, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". iPureIntro. rr in H3. ur in H3. unseal "ra". des.
      rr in H3. ur in H4. unseal "ra".
      rr in H4. ur in H4. unseal "ra". specialize (H4 k).
      rr in H4. ur in H4. unseal "ra". des_ifs. lia.
    Qed.

    Lemma black_map_get f k v
      :
      black_map f -∗ map_points_to k v -∗ (⌜f k = v⌝).
    Proof.
      unfold black_map, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". iPureIntro. rr in H3. ur in H3. unseal "ra". des.
      rr in H4. ur in H4. unseal "ra". des.
      rr in H4. des. ur in H4. eapply equal_f with (x:=k) in H4.
      ur in H4. des_ifs.
    Qed.

    Lemma black_map_set f k w v
      :
      black_map f -∗ map_points_to k w -∗ #=> (black_map (fun n => if Z.eq_dec n k then v else f n) ∗ map_points_to k v).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iPoseProof (OwnM_Upd with "H") as "H".
      { instantiate (1:=black_map_r (fun n => if Z.eq_dec n k then v else f n) ⋅ map_points_to_r k v).
        rr. i. ur in H3. ur. unseal "ra". des_ifs. des. split; auto.
        ur in H4. ur. des_ifs. des. rr in H4. des. split.
        { rr. exists ctx. ur in H4. ur. extensionality n.
          eapply equal_f with (x:=n) in H4. ur in H4. ur. des_ifs.
        }
        { ur. i. rr. ur. unseal "ra". ss. }
      }
      iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
    Qed.


    Lemma pending_unique:
      pending -∗ pending -∗ False%I.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. clear - H3.
      rr in H3. ur in H3. unseal "ra". des.
      rr in H3. ur in H3. unseal "ra". ss.
    Qed.
  End LEMMA.

  Local Notation universe := positive.
  (* Local Notation level := nat. *)

  (* 
    isim_apc_src : src hAPC, tgt HoareCall true(pure)
  *)

  Definition is_possibly_pure (fsp: fspec): Prop := exists x, is_pure (fsp.(measure) x).

  Definition stb_pure_incl (stb_tgt stb_src: string -> option fspec): Prop :=
    forall fn fsp (FIND: stb_tgt fn = Some fsp) (PURE: is_possibly_pure fsp), stb_src fn = Some fsp
  .

  Let Ist: Any.t -> Any.t -> iProp :=
        (fun st_src st_tgt =>
             ((∃ f sz, pending ∗ ⌜st_src = f↑ /\ st_tgt = (f, sz)↑⌝ ∗ black_map f ∗ unallocated sz) ∨ 
             (pending0 ∗ ⌜st_src = (fun (_: Z) => 0%Z)↑ /\ st_tgt = (fun (_: Z) => 0%Z, 0%Z)↑⌝ ∗ initial_map))%I).

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec.

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  (* Hypothesis PUREINCL: forall sk, stb_pure_incl (GlobalStbM sk) (GlobalStb sk). *)


  From Ordinal Require Import Ordinal.

  Lemma isim_apc 
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt stb_src stb_tgt
    (* (STBINCL: stb_pure_incl stb_tgt stb_src) *)
  :
    (I st_src st_tgt ∗ (∀st_src0 st_tgt0 vret, (I st_src0 st_tgt0) -∗ isim I fls flt r g RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗
    @isim _ I fls flt r g R RR ps pt (st_src, interp_hEs_hAGEs stb_src ord_top (trigger hAPC) >>= k_src) (st_tgt, interp_hEs_hAGEs stb_tgt ord_top (trigger hAPC) >>= k_tgt).
  Proof.
    iIntros "[IST K]".
    unfold interp_hEs_hAGEs. rewrite! interp_trigger. grind.
    unfold HoareAPC. grind.
    choose. instantiate (1:= x).
    induction ord_top.
    { rewrite ! unfold_APC. steps. 
      force. instantiate (1:= y).
      destruct y; steps.
      { iApply "K"; eauto. }
    }


    (****)
    rewrite! unfold_APC.
    choose. instantiate (1:= x0).
    destruct x0 eqn: Eqx.
    { steps. iApply "K". eauto. }
    choose. instantiate (1:= x1).
    unfold guarantee.
    choose. rewrite! bind_ret_l. choose. instantiate (1:= x3).
    destruct x3. steps. 
    unfold HoareCall.
    choose. instantiate (1:= x3).
    choose. instantiate (1:= x4).
    steps. force. iSplitL "GRT"; [eauto|].
    prep. call; eauto.
    take. instantiate (1:= x5).
    steps. force. iSplitL "ASM"; [eauto|].
    steps. 
  Admitted.

  (* Lemma isim_call_impure
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt 
    fn args stb_src stb_tgt
  :
    (I st_src st_tgt ∗ (∀st_src0 st_tgt0 vret, (I st_src0 st_tgt0) -∗ isim I fls flt r g RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗
    @isim _ I fls flt r g R RR ps pt (st_src, HoareCall false ord_top stb_src fn args >>= k_src) (st_tgt, HoareCall false ord_top stb_tgt fn args >>= k_tgt).
  Proof.
    iIntros "[IST K]".
    rewrite ! HoareCall_parse. unfold HoareCallPre.
    steps.
    
  
  Admitted. *)

(* TODO: Try spawn & consume a dummy world *)
  Ltac apc := prep; iApply isim_apc; iSplitL "IST"; [eauto|iIntros "% % %"; iIntros "IST"].

  Theorem sim: HModPair.sim (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist.
  Proof.
    sim_init.
    - iIntros "[IST P]"; s. iSplitR; eauto. 
      steps. iRight. iFrame. eauto.
    - unfold cfunU, initF, MapM.initF, interp_sb_hp, HoareFun. s.
      take. instantiate (1:= x). destruct x. 
      take. instantiate (1:= x0).
      asm. iDestruct "ASM" as "(W & (%Y & %M & P) & %X)". subst.
      iDestruct "IST" as "[IST|[P0 [% INIT]]]".
      (* Precondition *)
      { 
        iDestruct "IST" as (? ?) "(P' & _)".
        iExFalso. iApply (pending_unique with "P P'"). 
      } 
      iPoseProof (initial_map_initialize with "INIT") as "(BLACK & INIT & UNALLOC)". instantiate (1:= x).
      iCombine "P BLACK UNALLOC" as "IST".
      iSplitL "P0 W".
      { iFrame. esplits; eauto. }  
      steps. 
      des. subst. rewrite Any.upcast_downcast in G. inv G.
      apc.
      { (* Invariant *)
        iLeft. iExists (λ _ : Z, 0%Z), x. iDestruct "IST" as "(P & BLACK & UNALLOC)". 
        iFrame. eauto.
      }
      steps. force. instantiate (1:= y).
      force. iSplitR "IST". 
      { (* Postcondition *)
        iDestruct "GRT" as "(W & _ & %Y)". iFrame.
        iSplit; eauto. 
      }
      steps. eauto. 

    - unfold cfunU, getF, MapM.getF, interp_sb_hp, HoareFun. s.
      take. destruct x, x.
      take. instantiate (1:= x).
      asm. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst. iSplitR; [eauto|].
      steps. iDestruct "IST" as "[IST|IST]"; cycle 1.
      {
        iExFalso. iDestruct "IST" as "(_ & _ & INIT)".
        iApply (initial_map_no_points_to with "INIT MAP").
      }
      iDestruct "IST" as (? ?) "(P & % & BLACK & UNALLOC)". 
      des. subst. rewrite Any.upcast_downcast in G.
      iPoseProof (unallocated_range with "UNALLOC MAP") as "%".
      steps. force. steps. 
      iPoseProof (black_map_get with "BLACK MAP") as "%".      
      (* APC *)
      iCombine "P BLACK UNALLOC" as "IST".
      apc.
      {
        iLeft. iExists f, sz. iDestruct "IST" as "(P & B & U)". 
        iFrame. esplits; eauto.  
      }
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      {
        iExFalso. iDestruct "IST" as "(_ & _ & INIT)".
        iApply (initial_map_no_points_to with "INIT MAP").
      }
      iDestruct "IST" as (? ?) "(P & % & BLACK & UNALLOC)". 
      des. subst. 
      steps. iDestruct "GRT" as "%GRT". 
      force. instantiate (1:= y).
      force.
      iSplitL "WORLD MAP".
      { iFrame. iPureIntro. inv G. esplits; eauto. }
      steps. iSplit; [|eauto]. iLeft.
      iExists f0, sz0. iFrame. esplits; eauto. 

    - unfold cfunU, setF, MapM.setF, interp_sb_hp, HoareFun. s.
      take. destruct x, x, p. take. instantiate (1:= x).  
      asm. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst. iSplitR; [eauto|].
      steps.
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      {
        iExFalso. iDestruct "IST" as "(_ & _ & INIT)".
        iApply (initial_map_no_points_to with "INIT MAP").
      }
      iDestruct "IST" as (? ?) "(P & % & BLACK & UNALLOC)". 
      des. subst. rewrite Any.upcast_downcast in G. 
      steps.
      iPoseProof (unallocated_range with "UNALLOC MAP") as "%".
      force. steps.
      iPoseProof (black_map_set with "BLACK MAP") as ">(BLACK & MAP)". instantiate (1:= z).
            
      (* APC *)
      iCombine "P BLACK UNALLOC" as "IST".
      apc. 
      {
        iLeft. iExists (λ n0 : Z, if Z.eq_dec n0 z0 then z else f n0), sz. iDestruct "IST" as "(P & B & U)". 
        iFrame. iPureIntro. inv G. esplits; eauto.  
      }
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      {
        iExFalso. iDestruct "IST" as "(_ & _ & INIT)".
        iApply (initial_map_no_points_to with "INIT MAP").
      }
      steps. force. instantiate (1:= y). force. iDestruct "GRT" as "%GRT".
      iSplitL "WORLD MAP".
      { iFrame. subst. iSplit; eauto. }
      steps. iSplit; eauto. iLeft. eauto.

    - unfold cfunU, set_by_userF, MapM.set_by_userF, interp_sb_hp, HoareFun. s.
      take. destruct x, x. take. instantiate (1:= x).
      asm. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst. iSplitR; [eauto|].

      iDestruct "IST" as "[IST|IST]"; cycle 1.
      {
        iExFalso. iDestruct "IST" as "(_ & _ & INIT)".
        iApply (initial_map_no_points_to with "INIT MAP").
      }
      iDestruct "IST" as (? ?) "(P & % & BLACK & UNALLOC)".      
      des. subst.
      iCombine "P BLACK UNALLOC" as "IST".

      steps. unfold ccallU. steps.        
      rewrite STB_set. steps.

      (* iApply isim_call_impure. *)

      specialize (STB_setM sk). rewrite STB_setM in G0. inv G0.
      rewrite! HoareCall_parse. unfold HoareCallPre.
      steps. iDestruct "GRT" as "(% & _)". subst.
      force. instantiate (1:= mk_meta u n (z, z0, y)).
       (* Unshelve. 2: { destruct y0. econs; [eapply u| eapply n| eapply (z, z0, y)]. } *)
      force. instantiate (1:= Any.upcast [Vint z; Vint y]). 
      steps. force. iSplitL "WORLD MAP".
      { iFrame. iPureIntro. esplits; eauto.  }
      steps. call.
      {
        iLeft. iExists f, sz. iDestruct "IST" as "(P & B & U)".
        iFrame. iSplit; eauto.  
      }
      unfold HoareCallPost.
      steps. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst.
      force. instantiate (1:= Any.upcast Vundef). instantiate (1:= Any.upcast Vundef).
      force. iSplitL "WORLD MAP". 
      { iFrame. rewrite Any.upcast_downcast in G0. inv G0. 
        iSplit; eauto. }
      force. iSplitR; [eauto|].
      steps. iFrame.

      Unshelve.
      2, 4: inv G; eauto.
      all: destruct x; econs; eauto.
    Qed.




End SIMMODSEM.


(* 


  Theorem correct: refines2 [MapM.Map GlobalStbM] [MapA.Map GlobalStb].
  Proof.
    eapply adequacy_local2. econs; ss.
    i. econstructor 1 with (wf:=wf) (le:=top2); ss.
    2: { esplits. econs; et. eapply to_semantic. iIntros "H". iSplitL "H"; eauto. iApply Own_unit. ss. }
    Local Opaque initial_map black_map map_points_to unallocated.
    econs.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.initF, MapA.initF, ccallU, ccallN.
      harg. fold wf. ss.
      unfold pending in ACC. mDesAll; des; clarify.
      mDesOr "INVS".
      { mDesAll. mAssertPure False; ss. iApply (pending1_unique with "A A2"). }
      steps. mDesAll. des. subst.
      mAssert _ with "INVS".
      { iApply (initial_map_initialize with "INVS"). }
      mDesAll.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps_safe. rewrite Any.pair_split in *. s. rewrite Any.pair_split.
      inv _UNWRAPN. rewrite Any.upcast_downcast in H3. inv H3.
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A".
        { iLeft. iExists _, _. iFrame. iSplits; eauto.  }
        { iApply "A". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        { iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
          iFrame. iSplits; auto.
          iLeft. iExists _, _. iFrame. iPureIntro. eauto.
        }
        { iDes. des; subst. iSplitR "H1"; eauto. }
      }
      { iDestruct "Q" as "[_ %]". des; subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.getF, MapA.getF, ccallU, ccallN.
      harg. fold wf. destruct x. ss.
      mDesAll; des; clarify.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst.
      mAssertPure (0 ≤ z < a0)%Z.
      { iApply (unallocated_range with "A2 A1"); eauto. }
      mAssertPure _.
      { iApply (black_map_get with "A3 A1"). }
      subst. steps. rewrite ! Any.pair_split. s. steps.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps.
      inv _UNWRAPN. rewrite Any.pair_split in H3. ss. rewrite Any.upcast_downcast in H3. inv H3.
      rewrite ! Any.pair_split. s.
      force_r; auto. steps.
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A2".
        { iLeft. iExists _, _. iFrame. iSplits; auto. }
        { iApply "A2". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H0 H1") as "H"; ss. }
        iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iFrame. iSplits; auto.
        iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }

    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.setF, MapA.setF, ccallU, ccallN.
      harg. fold wf. destruct x as [[? ?] ?]. ss.
      mDesAll; des; clarify.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst.
      mAssertPure (0 ≤ z < a0)%Z.
      { iApply (unallocated_range with "A2 A1"); eauto. }
      steps.
      rewrite ! Any.pair_split. s.

      mAssert _ with "A3 A1".
      { iApply (black_map_set with "A3 A1"). }
      mUpd "A4". mDesAll.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps.
      inv _UNWRAPN. rewrite Any.pair_split in H3. ss. rewrite Any.upcast_downcast in H3. inv H3.
      rewrite ! Any.pair_split. s. 
      
      force_r; auto. steps.
      rewrite ! Any.pair_split. s. 
      (*** calling APC ***)
      hAPC _.
      { iIntros "A"; iDes. iSplitR "A".
        { iLeft. iExists _, _. iFrame. iSplits; eauto. }
        { iApply "A". }
      }
      { auto. }
      fold wf. steps.
      hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H0" as "[H0 | H0]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H0 H1") as "H"; ss. }
        iDestruct "H0" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iFrame. iSplits; auto.
        iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    econs; ss.
    {
      init.
      rename mp_tgt into mpr_tgt.
      assert(exists mp_src mp_tgt (mr_src mr_tgt: Σ),
                mrp_src = Any.pair mp_src mr_src↑ ∧ mpr_tgt = Any.pair mp_tgt mr_tgt↑).
      { inv WF. esplits; et. } des; clarify.
      (*** init ***)
      unfold MapM.set_by_userF, MapA.set_by_userF, ccallU, ccallN.
      harg. fold wf. destruct x. ss.
      mDesOr "INVS".
      2:{ mDesAll. mAssertPure False; ss. iApply (initial_map_no_points_to with "INVS A1"). }
      mDesAll. des; subst. steps.
      harg_tgt.
      { iModIntro. iFrame. iSplits; et. xtra. }
      steps. rewrite _UNWRAPU. rewrite STB_set. steps.
      rewrite STB_setM in *. clarify. hcall _ _.
      { instantiate (1:=(_, _, _)). ss. iModIntro.
        iSplits; ss. iDes. iFrame. iSplits; ss; eauto.
        { instantiate (1:=True%I). iSplit; ss. iLeft.
          iExists _, _. iFrame. iPureIntro. eauto.
        }
      }
      { i. ss. iIntros "H". iDes. subst. eauto. }
      ss. mDesAll. subst.
      hpost_tgt.
      { iModIntro. iFrame. iSplits; ss; et. xtra. }
      steps. hret _; ss.
      { iModIntro.
        iDestruct "Q" as "[CLOSED %]". subst. iFrame.
        iDestruct "FR" as "[H0 H1]". iDestruct "H1" as "[H1 | H1]".
        2:{ iDes. iPoseProof (initial_map_no_points_to with "H1 H0") as "H"; ss. }
        iDestruct "H1" as (f0 sz0) "[[[% H2] H3] H4]". des; subst.
        iSplitR "H0"; eauto. iLeft. iExists _, _. iFrame. iPureIntro. eauto.
      }
      { iDestruct "Q" as "[_ %]". subst. iPureIntro.
        rr. esplits; eauto.
      }
    }
    Unshelve. all: ss.
  Qed. *)

End SIMMODSEM.
