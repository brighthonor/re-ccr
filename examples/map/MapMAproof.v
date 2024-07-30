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

Require Import (* SimModSemFacts *) IProofMode IRed ITactics.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.
  Context `{_M: MapRA.t}.
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
        iDestruct "H" as "(B & I & U)".
        iPoseProof (unallocated_alloc with "U") as "U". iFrame. auto.
      }
    Qed.

    Lemma initial_map_no_points_to k v
      :
      initial_map -∗ map_points_to k v -∗ ⌜False⌝.
    Proof.
      unfold initial_map, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. exfalso. rr in WF. ur in WF. unseal "ra". des.
      rr in WF0. ur in WF0. unseal "ra". des.
      rr in WF0. des. ur in WF0. eapply equal_f with (x:=k) in WF0.
      ur in WF0. des_ifs.
    Qed.

    Lemma unallocated_range sz k v
      :
      unallocated sz -∗ map_points_to k v -∗ ⌜(0 <= k < sz)%Z⌝.
    Proof.
      unfold unallocated, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
      rr in WF. ur in WF0. unseal "ra".
      rr in WF0. ur in WF0. unseal "ra". specialize (WF0 k).
      rr in WF0. ur in WF0. unseal "ra". des_ifs. lia.
    Qed.

    Lemma black_map_get f k v
      :
      black_map f -∗ map_points_to k v -∗ (⌜f k = v⌝).
    Proof.
      unfold black_map, map_points_to.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. iPureIntro. rr in WF. ur in WF. unseal "ra". des.
      rr in WF0. ur in WF0. unseal "ra". des.
      rr in WF0. des. ur in WF0. eapply equal_f with (x:=k) in WF0.
      ur in WF0. des_ifs.
    Qed.

    Lemma black_map_set f k w v
      :
      black_map f -∗ map_points_to k w -∗ #=> (black_map (<[k:=v]>f) ∗ map_points_to k v).
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iPoseProof (OwnM_Upd with "H") as "H".
      { instantiate (1:=black_map_r (<[k:=v]>f) ⋅ map_points_to_r k v).
        rr. intros ctx WF. ur in WF. ur. unseal "ra". des_ifs. des. split; auto.
        ur in WF0. ur. des_ifs. des. rr in WF0. des. split.
        { rr. exists ctx. ur in WF0. ur. extensionality n.
          eapply equal_f with (x:=n) in WF0. ur in WF0. ur.
          des_ifs; rewrite ->?fn_lookup_insert, ?fn_lookup_insert_ne; eauto.
        }
        { ur. i. rr. ur. unseal "ra". ss. }
      }
      iMod "H". iDestruct "H" as "[H0 H1]". iFrame. auto.
    Qed.

    Lemma pending_unique:
      pending -∗ pending -∗ False%I.
    Proof.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H" as WF. exfalso.
      rr in WF. ur in WF. unseal "ra". des.
      rr in WF. ur in WF. unseal "ra". ss.
    Qed.
    
  End LEMMA.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STB_set: forall sk, (GlobalStb sk) "set" = Some set_spec.

  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  (* TODO: Try spawn & consume a dummy world *)
  Definition Ist: Any.t -> Any.t -> iProp :=
    (fun st_src st_tgt =>
       ((pending0 ∗ initial_map ∗ ⌜st_src = (fun (_: Z) => 0%Z)↑ /\ st_tgt = (fun (_: Z) => 0%Z, 0%Z)↑⌝)
        ∨ 
        (pending ∗ ∃ f sz, ⌜st_src = f↑ /\ st_tgt = (f, sz)↑⌝ ∗ black_map f ∗ unallocated sz))%I).

  Lemma simF_init:
    HModPair.sim_fun
      (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist "init".
  Proof.
    simF_init MapA.HMap_unfold MapM.HMap_unfold MapM.initF initF.
    
    st.
    iDestruct "ASM" as "(W & (%Y & %M & P) & %X)". subst.
    iDestruct "IST" as "[(P0 & INIT & %)|(P' & _)]"; cycle 1.
    { iExFalso. iApply (pending_unique with "P P'"). }
    iPoseProof (initial_map_initialize with "INIT") as "(BLACK & INIT & UNALLOC)".    des; subst.
    force_r. instantiate (1:= mk_meta _ _ _).
    force_r. force_r.
    iSplitL "P0 W". { iFrame. eauto. }
    st. force_l. force_l.
    iDestruct "GRT" as "(CW & %Y)". des. subst.
    iSplitL "CW INIT". { iFrame. eauto. }
    st. iSplit; eauto.
    iRight. iFrame. iExists (λ _ : Z, 0%Z), x. iFrame. eauto.
  Qed.

  Lemma simF_get:
    HModPair.sim_fun
      (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist "get".
  Proof.
    simF_init MapA.HMap_unfold MapM.HMap_unfold MapM.getF getF.
    
    st. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst.
    hss. inv G. inv G0.
    iDestruct "IST" as "[(_ & INIT & _)|(P & IST)]".
    { iExFalso. iApply (initial_map_no_points_to with "INIT MAP"). }
    iDestruct "IST" as (? ?) "(% & BLACK & UNALLOC)".
    force_r. instantiate (1:= mk_meta y0 y1 y3).
    force_r. instantiate (1:= [Vint y3]↑).
    force_r. iSplitL "WORLD". { iFrame. eauto. }
    des. subst. st. 
    iPoseProof (unallocated_range with "UNALLOC MAP") as "%".
    iPoseProof (black_map_get with "BLACK MAP") as "%".
    subst. force_r. { eauto. } st.
    iDestruct "GRT" as "(WORLD & %)". des. subst.
    force_l. force_l.
    iSplitL "WORLD MAP". { iFrame. eauto. }
    st. iSplitL; eauto. iRight.
    iFrame. iExists f, sz. iFrame. eauto.
  Qed.

  Lemma simF_set:
    HModPair.sim_fun
      (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist "set".
  Proof.
    simF_init MapA.HMap_unfold MapM.HMap_unfold MapM.setF setF.
    
    st. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst. 
    iDestruct "IST" as "[(_ & INIT & _)|(P & IST)]".
    { iExFalso. iApply (initial_map_no_points_to with "INIT MAP"). }
    iDestruct "IST" as (? ?) "(% & BLACK & UNALLOC)". 
    force_r. instantiate (1:= mk_meta _ _ (_,_)).
    force_r.
    force_r. iSplitL "WORLD". { iFrame. eauto. }
    des. subst. st. 
    iPoseProof (unallocated_range with "UNALLOC MAP") as "%".
    iPoseProof (black_map_set with "BLACK MAP") as ">(BLACK & MAP)". instantiate (1:= y5).
    subst. force_r. { eauto. } st.
    iDestruct "GRT" as "(WORLD & %)". des; subst.
    hss. inv G. inv G0. 
    force_l. force_l. iSplitL "WORLD MAP". { iFrame. eauto. } 
    st. iSplit; eauto.
    iRight. iFrame. iExists (<[y4:=y5]> f), sz.
    iFrame. eauto.
  Qed.

  Lemma simF_set_by_user:
    HModPair.sim_fun
      (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist "set_by_user".
  Proof.
    simF_init MapA.HMap_unfold MapM.HMap_unfold MapM.set_by_userF set_by_userF.

    st. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst.
    force_r. force_r. force_r. instantiate (1:= mk_meta _ _ _). s.
    iSplitL "WORLD". { iFrame. eauto. }

    st. rewrite STB_set. st.
    rewrite !HoareCall_parse. unfold HoareCallPre.
    rewrite STB_setM in G2. inv G2.
    hss. inv G. inv G0.
    st. iDestruct "GRT" as "[[WORLD [% %]] _]". subst.
    force_l. instantiate (1:= mk_meta _ _ (_,_,_)).
    force_l. force_l.
    iSplitL "WORLD MAP". { iFrame. eauto. }

    st. call. { eauto. }

    unfold HoareCallPost.
    st. iDestruct "ASM" as "(WORLD & (% & MAP) & %)". subst.
    hss. inv G.
    force_r. st. force_r.
    iSplitL "WORLD". { iFrame. eauto. }
    st. iDestruct "GRT" as "(WORLD & _ & %)". subst.
    force_l. force_l.
    iSplitL "MAP WORLD". { iFrame. eauto. }
    st. eauto.
  Qed.
  
  Theorem sim: HModPair.sim (MapA.HMap GlobalStb) (MapM.HMap GlobalStbM) Ist.
  Proof.
    sim_init.
    - iIntros "(IST & P & INIT0)"; s. iSplitL "INIT0"; eauto.
      iLeft. iFrame. eauto.
    - iApply simF_init. eauto.
    - iApply simF_get. eauto.
    - iApply simF_set. eauto.
    - iApply simF_set_by_user. eauto.
    Qed.

End SIMMODSEM.

