Require Import MapHeader MapI MapM HoareDef SimModSem.
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
Require Import Mem1 MemOpen STB Invariant.

Require Import IProofMode IRed ITactics.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_M: MapRA.t}.
  Context `{@GRA.inG memRA Γ}. 
        
  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Lemma pending0_unique:
    pending0 -∗ pending0 -∗ False%I.
  Proof.
    Local Transparent pending0.
    iIntros "H0 H1". iCombine "H0 H1" as "H".
    iOwnWf "H" as WF. exfalso.
    rr in WF. ur in WF. unseal "ra". des. ur in WF. ss.
  Qed.
  
  Definition fun_to_list (f: Z -> Z) (sz: nat) : list val :=
    map (fun i:nat => Vint (f i)) (seq 0 sz).

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt =>
       ((⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑ /\ st_tgt = Vnullptr↑⌝)
        ∨
        (pending0 ∗ ∃ blk ofs (f: Z -> Z) (sz: Z), 
            ⌜st_src = (f, sz)↑ /\  st_tgt = (Vptr blk ofs)↑⌝ 
            ∗ [∗ list] i↦v ∈ (fun_to_list f (Z.to_nat sz)), PointsTo (blk, (ofs + i))%Z v)
       )%I.

  Lemma repeat_update {A} i n (v v' w: A):
    <[i:=v]> (repeat v i ++ v' :: repeat w n) = repeat v (i+1) ++ repeat w n.
  Proof.
    replace i with (length (repeat v i) + 0) at 1; cycle 1.
    { rewrite repeat_length. nia. }
    rewrite ->insert_app_r, repeat_app, <-app_assoc. eauto.
  Qed.

  Lemma repeat_fun_to_list (n: nat):
    repeat (Vint 0) n = fun_to_list (λ _ : Z, 0%Z) n.
  Proof.
    unfold fun_to_list. induction n; eauto.
    replace (S n) with (n+1) by nia.
    rewrite ->repeat_app, seq_app, map_app, IHn. eauto.
  Qed.

  Lemma fun_to_list_lookup (f: Z -> Z) (sz: nat) (i: nat)
    (LT: i < sz)
    :
    fun_to_list f sz !! i = Some (Vint (f i)).
  Proof.
    unfold fun_to_list.
    rewrite ->list_lookup_fmap, lookup_seq_lt; try nia. eauto.
  Qed.

  Lemma fun_to_list_update (f: Z -> Z) (sz: nat) (i: nat) (v: Z)
    :
    <[i := Vint v]> (fun_to_list f sz) = fun_to_list (<[Z.of_nat i := v]> f) sz.
  Proof.
    unfold fun_to_list. revert i. induction sz; i; eauto.
    replace (S sz) with (sz + 1) by nia.
    rewrite ->!seq_app, !map_app.
    assert (CASE: i < sz \/ i >= sz) by nia.
    des.
    - rewrite insert_app_l; cycle 1.
      { rewrite ->map_length, seq_length. nia. }
      rewrite IHsz. s. do 3 f_equal.
      rewrite fn_lookup_insert_ne; eauto. nia.
    - assert (Iadd: length (map (λ i0 : nat, Vint (f i0)) (seq 0 sz)) + (i - sz) = i).
      { rewrite ->map_length, seq_length. nia. }
      s. rewrite -IHsz -{1 2}Iadd -{4}(app_nil_r (seq 0 sz)) map_app. 
      rewrite ->!insert_app_r, <-app_assoc. f_equal. s.
      assert (CASE': i = sz \/ i > sz) by nia.
      des; subst.
      + rewrite ->fn_lookup_insert, Nat.sub_diag. eauto.
      + rewrite ->fn_lookup_insert_ne; try nia.
        destruct (i-sz) eqn: EQ; try nia. eauto.
  Qed.
  
  Let Mem := HMem (fun _ => false).

  Lemma simF_init:
    HModPair.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "init".
  Proof.
    r. i. pattern (MapM.HMap GlobalStbM) at 1. rewrite MapM.HMap_unfold. s.
    pattern MapI.Map at 1. rewrite MapI.Map_unfold. s. i. iIntros "IST".

    unfold cfunU, initF, MapI.initF, interp_sb_hp, HoareFun, ccallU. s.
    st. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)". subst.
    st. iDestruct "IST" as (? ? ? ?) "(%& [%|(P & _)] &%)"; des; subst; cycle 1.
    { iExFalso. iApply (pending0_unique with "P P0"). }
    inline_r.
    st. force. instantiate (1:= x).
    st. force. instantiate (1:= [Vint x]↑).
    st. force. iSplitR; eauto.
    (* todo: make the following as a lemma *)
    st. rewrite interp_hAGEs_hapc. st. unfold HoareAPC. st. rewrite unfold_APC.
    st. destruct y4; cycle 1.
    { unfold guarantee, triggerNB. st. inv y6. }
    
    unfold ModSem.run_l. rewrite !Any.pair_split. fold ModSem.run_l.
    
    st. iDestruct "GRT" as "[GRT %]". iDestruct "GRT" as ( ? ) "(% & POINTS)". subst. st.
    unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
    st. force. st. force. iSplitL "W". { iFrame. eauto. }
    rewrite Any.upcast_downcast in G. inv G. inv G0. st.

    iPoseProof (points_to_conv with "POINTS") as "POINTS".
    replace (repeat Vundef x) with (repeat (Vint 0) (x-x) ++ repeat Vundef x); cycle 1.
    { rewrite Nat.sub_diag. eauto. }
    match goal with |- context[ITree.iter ?f 0%Z] =>
      replace (ITree.iter f 0%Z) with (ITree.iter f (x-x)%Z) by (f_equal; nia)
    end.

    iStopProof. cut (x <= x); [|lia].
    generalize x at 1 4 5 11. intros n. induction n; i; iIntros "(PD & PTS)".
    {
      rewrite unfold_iter_eq. st. des_ifs. { exfalso. nia. }
      st. iSplitL; [|eauto].
      iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.
      iRight. iFrame. iExists b, 0%Z, (fun _ => 0%Z), x.
      iSplit; eauto.
      rewrite ->app_nil_r, Nat.sub_0_r, repeat_fun_to_list, Nat2Z.id. eauto.
    }

    rewrite unfold_iter_eq. st. des_ifs; cycle 1. { exfalso. nia. }
    st. unfold scale_int at 1. des_ifs; cycle 1.
    { exfalso. eapply n0. eapply Z.divide_factor_r. }
    st. inline_r.
    st. force. instantiate (1:= (b, (x - S n)%Z, Vint 0)).
    st. force. instantiate (1:= [Vptr b (x - (S n))%Z; Vint 0]↑).
    st. force.
    iPoseProof (big_sepL_insert_acc with "PTS") as "(PT & CTN)".
    { instantiate (2:= (x - (S n))).
      rewrite lookup_app_r; rewrite repeat_length; try nia.
      rewrite Nat.sub_diag. eauto.
    }

    rewrite ->!Z.add_0_l, Zpos_P_of_succ_nat, <-Nat2Z.inj_succ, Nat2Z.inj_sub; try nia.
    iSplitL "PT".
    { iSplitL; cycle 1.
      { iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia. }
      iExists Vundef. iFrame.
      iPureIntro. do 3 f_equal. rewrite Z.div_mul; nia.
    }
    (* todo: make the following as a lemma *)
    st. rewrite interp_hAGEs_hapc. st. unfold HoareAPC. st. rewrite unfold_APC.
    st. destruct y3; cycle 1.
    { unfold guarantee, triggerNB. st. inv y5. }

    st. iDestruct "GRT" as "[[GRT %] %]". subst.
    st. iPoseProof ("CTN" with "GRT") as "PTS".
    rewrite ->!Zpos_P_of_succ_nat, <-!Nat2Z.inj_succ.
    replace (x - S n + 1)%Z with (x - n)%Z by nia.
    iApply IHn; try nia. iFrame.
    rewrite repeat_update.
    eapply eq_ind. { iApply "PTS". }
    do 3 f_equal. nia.
  Qed.

  Lemma simF_get:
    HModPair.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "get".
  Proof.
    r. i. pattern (MapM.HMap GlobalStbM) at 1. rewrite MapM.HMap_unfold. s.
    pattern MapI.Map at 1. rewrite MapI.Map_unfold. s. i. iIntros "IST".

    unfold cfunU, getF, MapI.getF, interp_sb_hp, HoareFun, ccallU. s.
    st. iDestruct "ASM" as "(W & % & %)". subst. st.
    rewrite Any.upcast_downcast in G. inv G. inv G0.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; unfold ModSem.run_l, assume; rewrite ! Any.pair_split.
    { st. nia. }
    st. force. instantiate (1:= (Vint (f y3))↑).
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    st. force. iSplitL "W". { eauto. }

    rewrite Z_div_mult; try nia.
    iPoseProof (big_sepL_lookup_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat y3). nia. }
    inline_r.
    st. force. instantiate (1:= (blk, (ofs + y3)%Z, Vint (f y3))).
    st. force.
    st. force. rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    (* todo: make the following as a lemma *)
    st. rewrite interp_hAGEs_hapc. st. unfold HoareAPC. st. rewrite unfold_APC.
    st. destruct y4; cycle 1.
    { unfold guarantee, triggerNB. st. inv y6. }
    
    st. iDestruct "GRT" as "[[GRT %] %]". subst.
    st. iSplitL; eauto.
    iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.
    iRight. iFrame. iExists blk, ofs, f, sz.
    iPoseProof ("M" with "GRT") as "M". iFrame. eauto.
  Qed.

  Lemma simF_set:
    HModPair.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "set".
  Proof.
    r. i. pattern (MapM.HMap GlobalStbM) at 1. rewrite MapM.HMap_unfold. s.
    pattern MapI.Map at 1. rewrite MapI.Map_unfold. s. i. iIntros "IST".
    
    unfold cfunU, setF, MapI.setF, interp_sb_hp, HoareFun, ccallU. s.
    st. iDestruct "ASM" as "(W & % & %)". subst. st.
    rewrite Any.upcast_downcast in G. inv G. inv G0.
    iDestruct "IST" as (? ? ? ?) "(%& [%|(P & IST)] &%)";      
      [|iDestruct "IST" as (? ? ? ?) "(% & M)"];
      des; subst; unfold ModSem.run_l, assume; rewrite ! Any.pair_split.
    { st. nia. }
    st. force. instantiate (1:= Vundef↑).
    rewrite ! Any.pair_split.
    unfold scale_int. des_ifs; cycle 1.
    { exfalso. eapply n. eapply Z.divide_factor_r. }
    st. force. iSplitL "W". { eauto. }

    rewrite Z_div_mult; try nia.
    iPoseProof (big_sepL_insert_acc with "M") as "(IP & M)".
    { apply fun_to_list_lookup with (i:=Z.to_nat y4). nia. }
    inline_r.
    st. force. instantiate (1:= (blk, (ofs + y4)%Z, Vint y5)).
    st. force.
    st. force. rewrite Z2Nat.id; try nia.
    iSplitL "IP"; eauto.
    (* todo: make the following as a lemma *)
    st. rewrite interp_hAGEs_hapc. st. unfold HoareAPC. st. rewrite unfold_APC.
    st. destruct y3; cycle 1.
    { unfold guarantee, triggerNB. st. inv y7. }
    st. iDestruct "GRT" as "[[GRT %] %]". subst.
    st. iSplitL; eauto.

    iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.      
    iRight. iFrame. iExists blk, ofs, (<[y4:=y5]> f), sz.
    iPoseProof ("M" with "GRT") as "M".
    rewrite ->fun_to_list_update, Z2Nat.id; try nia.
    eauto.
  Qed.

  Lemma simF_set_by_user:
    HModPair.sim_fun
      (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem)
      (IstProd Ist IstEq) "set_by_user".
  Proof.
    r. i. pattern (MapM.HMap GlobalStbM) at 1. rewrite MapM.HMap_unfold. s.
    pattern MapI.Map at 1. rewrite MapI.Map_unfold. s. i. iIntros "IST".

    unfold cfunU, set_by_userF, MapI.set_by_userF, interp_sb_hp, HoareFun, ccallU. s.
    st. iDestruct "ASM" as "(W & % & %)". subst.
    rewrite Any.upcast_downcast in G. inv G. inv G0.
    st. rewrite STB_setM. st. unfold HoareCall.
    force. instantiate (1:= mk_meta y0 y1 (y3, y)).
    force. instantiate (1:= [Vint y3; Vint y]↑).
    st. force. iSplitL "W". { iFrame. eauto. }
    call; [eauto|].
    st. iDestruct "ASM" as "(W & _ & %)". subst.
    force. st. force. iSplitL "W". { eauto. } 
    rewrite G0. st. eauto.
  Qed.
  
  Theorem sim: HModPair.sim (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem) (IstProd Ist IstEq).
  Proof.
    sim_init.
    - iIntros "[H0 H1]". iFrame.
      iExists _, _, _, _; iSplitR; eauto; iSplitL; eauto.
      iLeft; eauto.
    - iApply simF_init. eauto.
    - iApply simF_get. eauto.
    - iApply simF_set. eauto.
    - iApply simF_set_by_user. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
    - iApply isim_reflR. eauto.
  Qed.
  
End SIMMODSEM.




(***** Move and rename: APC & HoareCall LEMMAS *****)

  (* Try to match bind pattern *)
  Lemma APC_start_clo Σ
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb 
  :
    @isim Σ I fls flt r g R RR true pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, interp_hEs_hAGEs stb o (trigger hAPC) >>= k_src) sti_tgt.
  Proof.
    unfold interp_hEs_hAGEs. rewrite! interp_trigger. grind.
    destruct sti_tgt. unfold HoareAPC.
    iIntros "K". 
    force. instantiate (1:= at_most).
    iApply "K".
  Qed.

  Lemma APC_stop_clo Σ
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb
  :
    @isim Σ I fls flt r g R RR true pt (st_src, k_src tt) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K".
    rewrite unfold_APC. 
    force. instantiate (1:= true). steps. eauto.
  Qed.
  
  Lemma APC_step_clo Σ
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb next fn vargs fsp
    (SPEC: stb fn = Some fsp)
    (NEXT: (next < at_most)%ord)
  :
    @isim Σ I fls flt r g R RR true pt (st_src, HoareCall true o fsp fn vargs >>= (fun _ => _APC stb next o) >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K". prep.
    iEval (rewrite unfold_APC).
    force. instantiate (1:= false). steps.
    force. instantiate (1:= next). unfold guarantee.
    force. steps.
    force. instantiate (1:= (fn, vargs)). steps.
    rewrite SPEC. steps. grind.
    Unshelve. eauto.
  Qed.

  Lemma hcall_clo Σ
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt
    fn varg_src varg_tgt o X (x: shelve__ X) (D: X -> ord) P Q
    (* PURE, ... *)
    (ORD: ord_lt (D x) o)
    (PURE: is_pure (D x))
  :
    (P x varg_src varg_tgt 
      ∗ I st_src st_tgt 
      ∗ (∀st_src0 st_tgt0 vret_src vret_tgt, 
             (Q x vret_src vret_tgt ∗ I st_src0 st_tgt0) 
          -∗ @isim Σ I fls flt r g R RR true true (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)))
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, HoareCall true o (mk_fspec D P Q) fn varg_src >>= k_src) (st_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    iIntros "(P & IST & K)".
    unfold HoareCall. prep.
    force. instantiate (1:= x).
    force. instantiate (1:= varg_tgt).
    force. iSplitL "P"; [eauto|]. 
    call; [eauto|].
    steps. iApply "K". iFrame.
  Qed.
