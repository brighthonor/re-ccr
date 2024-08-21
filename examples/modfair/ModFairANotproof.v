Require Import ModFairA ModFairNot.
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

  Variable id: ID.
        
  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb (UnFairStb id)) (GlobalStb sk).

  (* proof for fun *)

  Definition middle_update isrc itgt f: iimap id owf := 
    (fun x => match f x with
              | Flag.success => Ord.omega
              | Flag.fail => Ord.from_nat (itgt x)
              | _ => isrc x 
              end).

  Definition IstFair: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => 
      (⌜exists (itgt: iimap id nat_wf) (isrc: iimap id owf), 
        st_tgt = itgt↑ ∧ st_src = isrc↑
        ∧ forall f, fair_update id owf isrc (middle_update isrc itgt f) f⌝)%I.

  Definition i_omega: iimap id owf := fun x => Ord.omega.

  Lemma simF_fair:
    forall (i_tgt: iimap id nat_wf),
    HModPair.sim_fun
      (ModFairA.HFair i_omega)
      (ModFairA.HFair i_tgt)
      IstFair "fair".
  Proof.
    simF_init HFair_unfold HFair_unfold fairF fairF.
    st. iDestruct "ASM" as "[W [% %]]"; des; subst.
    
    rewrite Any.upcast_downcast in G. inv G. ss. inv G0.

    force_r. instantiate (1:=mk_meta y0 y1 ()). force_r. force_r. iSplitR "IST".
    { iFrame; et. }
    st. iDestruct "IST" as "%"; des; subst.
    
    rewrite Any.upcast_downcast in G1. symmetry in G1. inv G1.

    st. unfold Fair. st.
    iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]". subst.
    force_l. 
    instantiate (1:=middle_update isrc itgt y3).
    st. force_l. iSplitR.
    { iPureIntro. et. }

    st. force_l. force_l. iSplitL "W"; iFrame; et. st. iSplit; et.

    unfold IstFair. iPureIntro.
    exists y, (middle_update isrc itgt y3).
    esplits; et. ii. unfold middle_update in *.
    des_ifs.
    - specialize (H i). rewrite Heq0 in H. apply OrdArith.lt_from_nat. ss.
    - specialize (H i). rewrite Heq0 in H. rewrite H.
      specialize (H1 f i). repeat rewrite Heq in H1. ss.
    - apply Ord.omega_upperbound.
  Qed.

  Theorem sim: 
    forall (i_tgt: iimap id nat_wf),
    HModPair.sim
      (ModFairA.HFair i_omega)
      (ModFairA.HFair i_tgt)
      IstFair.
  Proof.
    ii. sim_init.
    - rewrite// HFair_unfold. rewrite// HFair_unfold. s.
      iIntros "E"; iFrame. unfold IstFair. iPureIntro. exists i_tgt. esplits; ss.
      ii. unfold middle_update in *. des_ifs; ss. unfold i_omega. apply Ord.omega_upperbound.
    - iApply simF_fair. ss.
  Qed.


  (* IST when target's imap only have a progress *)

  Definition IstFairTgt: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => 
      (⌜exists (itgt: iimap id nat_wf) (isrc: iimap id nat_wf), 
        st_tgt = itgt↑ ∧ st_src = isrc↑⌝)%I.
  
  Lemma simF_fair_tgt:
    forall (i_tgt: iimap id nat_wf),
    HModPair.sim_fun
      (ModFairNot.HUnFair i_tgt GlobalStb)
      (ModFairA.HFair i_tgt)
      IstFairTgt "fair".
  Proof.
    simF_init HUnFair_unfold HFair_unfold unfairF fairF.
    st. iDestruct "ASM" as "[W [% %]]"; des; subst.
    
    rewrite Any.upcast_downcast in G. inv G.

    force_r. instantiate (1:=mk_meta y0 y1 ()). force_r. force_r. iSplitR "IST".
    { iFrame; et. }
    st. iDestruct "IST" as "%"; des; subst. st.
    
    unfold Fair. st.
    iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]". subst.

    force_l. force_l. iSplitL.
    { iFrame; et. }

    st. iSplit; et.
  Qed.

  Theorem sim_tgt: 
    forall (i_tgt: iimap id nat_wf),
    HModPair.sim
      (ModFairNot.HUnFair i_tgt GlobalStb)
      (ModFairA.HFair i_tgt)
      IstFairTgt.
  Proof.
    i. sim_init.
    - rewrite// HFair_unfold. rewrite// HUnFair_unfold. s.
      iIntros "E"; iFrame. unfold IstFairTgt. iPureIntro. esplits; et.
    - iApply simF_fair_tgt. ss.
  Qed.

  (* for use *)

  Lemma isim_fair_tgt Ist fnsems_src fnsems_tgt st_src st_tgt y sk:
    IstProd Ist IstFairTgt st_src st_tgt -∗
      isim (IstProd Ist IstFairTgt) fnsems_src fnsems_tgt ibot ibot
      (λ '(st_src, v_src) '(st_tgt, v_tgt), IstProd Ist IstFairTgt st_src st_tgt ** ⌜v_src = v_tgt⌝) false false
      (st_src, translate (HModSem.emb_ ModSem.run_r) (interp_sb_hp (GlobalStb sk) {| fsb_fspec := unfair_spec id; fsb_body := cfunU (unfairF (id:=id)) |} y))
      (st_tgt, translate (HModSem.emb_ ModSem.run_r) (interp_sb_hp (to_stb []) {| fsb_fspec := fair_spec id; fsb_body := cfunU (fairF (id:=id) nat_wf) |} y)).
  Proof.
    iIntros "IST". unfold unfairF, fairF.
    unfold interp_sb_hp, HoareFun. s.
    st. iDestruct "ASM" as "[W [% %]]"; des; subst.

    force_r. instantiate (1:=mk_meta y1 y2 ()). force_r. st_r. force_r. iSplitR "IST".
    { iFrame; et. }
    st. unfold cfunU. st. iDestruct "IST" as (? ? ? ?) "[% [IST %]]". des; subst. hss. hss.
    st. unfold Fair. st.
    iDestruct "GRT" as "%". iDestruct "GRT'" as "[W [_ %]]". subst.

    force_l. hss. hss. st_l. force_l. iSplitL "W".
    { iFrame; et. }

    st. iSplit; et.
    unfold IstProd. iExists _, _, _, _. iSplit; et. iFrame. unfold IstFairTgt. et.

  Qed.


  
End SIMMODSEM.
