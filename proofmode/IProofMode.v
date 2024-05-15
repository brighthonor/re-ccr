Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HPSim (* HPTactics *) (* HPSimFacts *).

From stdpp Require Import coPset gmap.
(* Require Import FancyUpdate. *)


Set Implicit Arguments.


Require Import Red.
Require Import IRed.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).


Section SPEC.
  Context `{Σ: GRA.t}.
  Variable stb: gname -> option fspec.
  Variable o: ord.


  Variant fn_has_spec (fn: gname) (arg_src: Any.t) (arg_tgt: Any.t)
          (pre: iProp)
          (post: Any.t -> Any.t -> iProp)
          (tbr: bool): Prop :=
  | fn_has_spec_intro
      fsp (x: fsp.(meta))
      (STB: stb fn = Some fsp)
      (MEASURE: ord_lt (fsp.(measure) x) o)
      (PRE: bi_entails pre (#=> fsp.(precond) x arg_src arg_tgt))
      (POST: forall ret_src ret_tgt, bi_entails (fsp.(postcond) x ret_src ret_tgt: iProp) (#=> post ret_src ret_tgt))
      (TBR: tbr = is_pure (fsp.(measure) x))
  .

  Lemma fn_has_spec_in_stb fsp (x: fsp.(meta))
        fn arg_src arg_tgt tbr
        (STB: stb fn = Some fsp)
        (MEASURE: ord_lt (fsp.(measure) x) o)
        (TBR: tbr = is_pure (fsp.(measure) x))
    :
      fn_has_spec
        fn arg_src arg_tgt
        (fsp.(precond) x arg_src arg_tgt)
        (fsp.(postcond) x)
        tbr.
  Proof.
    econs; eauto.
  Qed.

  Lemma fn_has_spec_impl fn arg_src arg_tgt pre0 post0 pre1 post1 tbr
        (PRE: bi_entails pre1 (#=> pre0))
        (POST: forall ret_src ret_tgt, bi_entails (post0 ret_src ret_tgt) (#=> (post1 ret_src ret_tgt)))
        (SPEC: fn_has_spec fn arg_src arg_tgt pre0 post0 tbr)
    :
      fn_has_spec fn arg_src arg_tgt pre1 post1 tbr.
  Proof.
    inv SPEC. econs; eauto.
    { iIntros "H". iPoseProof (PRE with "H") as "H".
      iMod "H". iApply PRE0. iApply "H".
    }
    { i. iIntros "H". iPoseProof (POST0 with "H") as "H".
      iMod "H". iApply POST. iApply "H".
    }
  Qed.

End SPEC.

Section SIM.

  Context `{Σ: GRA.t}.
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Let _hpsim := @_hpsim Σ fl_src fl_tgt Ist false.
  (* Variable stb_src: gname -> fspec.
  Variable stb_tgt: gname -> fspec. *)


  Program Definition isim
          r g {R} (RR: Any.t * R-> Any.t * R -> iProp) ps pt
          (sti_src sti_tgt : Any.t * itree hAGEs R): iProp := 
    iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) r g _ RR ps pt sti_src sti_tgt) _.
  Next Obligation.
    guclo hpsim_extendC_spec. econs; et.
  Qed.

  (* GIL: Deleted the following because it is subsumed by [isim_init]. *)
  
  (* Lemma isim_hpsim  *)
  (*   r g ps pt {R} RR sti_src sti_tgt fmr *)
  (*   (SIM: @isim r g R RR ps pt sti_src sti_tgt fmr) *)
  (*   (* (SIM: fmr ⊢ @isim r g R RR ps pt sti_src sti_tgt) *) *)
  (* : *)
  (*   gpaco7 _hpsim (cpn7 _hpsim) r g R RR ps pt sti_src sti_tgt fmr. *)
  (* Proof. uiprop in SIM. eauto. Qed. *)


(***** isim lemmas *****)

  Lemma isim_init
      r g ps pt {R} RR st_src st_tgt i_src i_tgt iP fmr
      (ENTAIL: bi_entails
                iP
                (@isim r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt)))
      (CUR: Own fmr ⊢ iP)
    :
      gpaco7 _hpsim (cpn7 _hpsim) r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in ENTAIL. eapply ENTAIL; eauto.
    eapply Own_iProp; eauto.
  Qed.

  Lemma isim_final
      r g ps pt {R} RR st_src st_tgt i_src i_tgt (iP: iProp)
      (SIM: forall fmr (IP: iP fmr), 
          gpaco7 _hpsim (cpn7 _hpsim) r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      bi_entails
        iP
        (isim r g RR ps pt (st_src, i_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsim_extendC_spec. econs; eauto. refl.
  Qed.

  Lemma isim_upd
      r g ps pt {R} RR sti_src sti_tgt
    :
      bi_entails
        (#=> (@isim r g R RR ps pt sti_src sti_tgt))
        (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. des. guclo hpsim_updateC_spec. econs. ii.
    esplits; eauto. eapply Own_Upd; eauto.
  Qed.

  (* GIL: Deleted the following because it is subsumed by [isim_wand]. *)
  
  (* Lemma isim_mono *)
  (*   r g ps pt {R} RR0 RR1 sti_src sti_tgt *)
  (*   (MONO: forall st_src st_tgt ret_src ret_tgt, *)
  (*           (bi_entails (RR0 (st_src, ret_src) (st_tgt, ret_tgt)) (RR1 (st_src, ret_src) (st_tgt, ret_tgt)))) *)
  (*   : *)
  (*     bi_entails *)
  (*       (@isim r g R RR0 ps pt sti_src sti_tgt) *)
  (*       (@isim r g R RR1 ps pt sti_src sti_tgt). *)
  (* Proof. *)
  (*   uiprop. i. destruct sti_src, sti_tgt. *)
  (*   rewrite <-(bind_ret_r i). rewrite <-(bind_ret_r i0). *)
  (*   guclo hpsim_bindC_spec. econs; eauto. *)
  (*   i. gstep. econs. ii. esplits; eauto. econs; eauto. *)
  (*   iIntros "H". iApply MONO. iStopProof. eauto. *)
  (* Qed. *)

  Lemma isim_wand
        r g ps pt {R} RR RR' sti_src sti_tgt        
    :
      bi_entails
        ((∀ st_src ret_src st_tgt ret_tgt,
            ((RR' (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR (st_src, ret_src) (st_tgt, ret_tgt)))) ** (@isim r g R RR' ps pt sti_src sti_tgt))
        (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    rr. rewrite Seal.sealing_eq. i.
    guclo hpsim_frameC_spec.
    apply iProp_Own in H. eapply iProp_sepconj in H; des; eauto. subst.
    apply iProp_Own in H0.
    econs; cycle 1.
    { iIntros "[P Q]". iSplitL "Q". eauto.
      iPoseProof (H0 with "P") as "P". eauto.
    }
    
    destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i). rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec. econs; eauto.
    { apply H1. }
    i. gstep. econs. ii. esplits; eauto. econs; eauto.
    iIntros "H". iPoseProof (RET with "H") as "H". iMod "H".
    iModIntro. iIntros "Y". iApply "Y". eauto.
  Qed.

  Lemma isim_bind 
    r g ps pt {R S} RR st_src st_tgt i_src i_tgt k_src k_tgt        
  :
    bi_entails
    (@isim r g S
          (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
              (@isim r g R RR false false (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt))%I)
          ps pt (st_src, i_src) (st_tgt, i_tgt))
        (isim r g RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    uiprop. i.
    guclo hpsim_bindC_spec. econs; eauto.
    i. guclo hpsim_updateC_spec. econs.
    uiprop in RET. ii. exploit RET; eauto; try refl.
    i; des. esplits; eauto. eapply Own_Upd; eauto.
  Qed.

  Lemma isim_ret
    r g ps pt {R} RR st_src st_tgt v_src v_tgt
  :
    bi_entails
      (RR (st_src, v_src) (st_tgt, v_tgt))
      (@isim r g R RR ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. uiprop. i. eauto using iProp_mono.
  Qed.
  
  Lemma isim_call 
    r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg
  :
    bi_entails
      ((Ist st_src st_tgt) ** (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -* @isim r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
      (isim r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    remember (∀ st_src0 st_tgt0 vret : Any.t, Ist st_src0 st_tgt0 -* isim r g RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret))%I as FR.
    uiprop. i. des. guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto; i; subst. 
    { instantiate (1:= FR). subst. eapply iProp_Own in H0, H1.
      iIntros "[A B]". iPoseProof (H0 with "A") as "A". iPoseProof (H1 with "B") as "B".
      iFrame. eauto.
    }
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    eapply isim_init; eauto.
    iIntros "H". iPoseProof (INV with "H") as "H". iApply isim_upd.
    iMod "H". iDestruct "H" as "[X B]".
    iSpecialize ("B" $! st_src0 st_tgt0 vret).
    iApply "B". eauto.
  Qed.
  
  Lemma isim_syscall
    r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg rvs
  : 
    bi_entails
      (∀ vret, @isim r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
      (isim r g RR ps pt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto.
    econs; eauto. i.
    eapply iProp_Own in H.
    eapply isim_init; eauto.
    iIntros "H". iApply (H with "H").   
  Qed.
  
  Lemma isim_inline_src
    r g ps pt {R} RR st_src st_tgt k_src i_tgt f fn varg 
    (FIND: alist_find fn fl_src = Some f)
  :
  bi_entails
    (@isim r g R RR true pt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    (@isim r g R RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_inline_tgt
    r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_tau_src
    r g ps pt {R} RR st_src st_tgt i_src i_tgt
  :
    bi_entails
      (@isim r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_tau_tgt
    r g ps pt {R} RR st_src st_tgt i_src i_tgt
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_take_src
    X r g ps pt {R} RR st_src st_tgt k_src i_tgt 
  :
    bi_entails
      (∀ x, @isim r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    eapply isim_init; eauto. eapply iProp_Own in H.
    iIntros "H". iApply (H with "H").
  Qed.

  Lemma isim_choose_tgt
    X r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (∀x, @isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    eapply isim_init; eauto. eapply iProp_Own in H.
    iIntros "H". iApply (H with "H").
  Qed.

  Lemma isim_choose_src
    X x r g ps pt {R} RR st_src st_tgt k_src i_tgt
  :
    bi_entails
      (@isim r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_take_tgt
    X x r g ps pt {R} RR st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
  Qed.
  
  Lemma isim_supdate_src
    X
    r g ps pt {R} RR st_src st_tgt k_src i_tgt 
    (run: Any.t -> Any.t * X)
  :
    bi_entails
      (@isim r g R RR true pt ((run st_src).1, k_src (run st_src).2) (st_tgt, i_tgt))
      (@isim r g R RR ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
    destruct (run st_src); eauto.
  Qed.
  
  Lemma isim_supdate_tgt
    X
    r g ps pt {R} RR st_src st_tgt i_src k_tgt 
    (run: Any.t -> Any.t * X)
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) ((run st_tgt).1, k_tgt (run st_tgt).2))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto.
    destruct (run st_tgt); eauto.
  Qed.
  
  Lemma isim_assume_src
    r g ps pt {R} RR iP st_src st_tgt k_src i_tgt 
  :
    bi_entails
      (iP -* (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
      (@isim r g R RR ps pt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. i.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in NEW. edestruct NEW; eauto; try refl. des.
    guclo hpsim_updateC_spec. econs. ii. subst.
    esplits.
    - eapply H; eauto.
      eapply URA.wf_extends.
      { eapply URA.extends_add. eauto. }
      specialize (H3 ε). rewrite URA.add_comm. revert H3. r_solve. eauto.
    - eapply Own_Upd. ii. apply H3 in H2. eapply URA.wf_extends; eauto.
      rewrite (URA.add_comm a b). repeat apply URA.extends_add. eauto.
  Qed.
  
  Lemma isim_guarantee_tgt
    r g ps pt {R} RR iP st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (iP -* (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; i; eauto.
    econs; eauto. i.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in NEW. edestruct NEW; eauto; try refl. des.
    guclo hpsim_updateC_spec. econs. ii. subst.
    esplits.
    - eapply H; eauto.
      eapply URA.wf_extends.
      { eapply URA.extends_add. eauto. }
      specialize (H3 ε). rewrite URA.add_comm. revert H3. r_solve. eauto.
    - eapply Own_Upd. ii. apply H3 in H2. eapply URA.wf_extends; eauto.
      rewrite (URA.add_comm a b). repeat apply URA.extends_add. eauto.
  Qed.

  Lemma isim_guarantee_src
    r g ps pt {R} RR iP st_src st_tgt k_src i_tgt 
  :
    bi_entails
      (iP ** (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
      (@isim r g R RR ps pt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. des. subst.
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    { instantiate (1:= (@isim r g R RR true pt (st_src, k_src ()) (st_tgt, i_tgt))).
      eapply iProp_Own in H0.
      iIntros "[A B]". iPoseProof (H0 with "A") as "A". iFrame. iStopProof.
      eapply iProp_Own. uiprop. eauto.
    }
    eapply isim_init; eauto.
    iIntros "H". iApply isim_upd. iStopProof; eauto.
  Qed.

  Lemma isim_assume_tgt
    r g ps pt {R} RR iP st_src st_tgt i_src k_tgt 
  :
    bi_entails
      (iP ** (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt)).
  Proof.
    uiprop. i. des. subst. 
    guclo hpsimC_spec. econs; esplits; eauto. econs; eauto; i.
    { instantiate (1:= (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt))).
      eapply iProp_Own in H0.
      iIntros "[A B]". iPoseProof (H0 with "A") as "A". iFrame. iStopProof.
      eapply iProp_Own. uiprop. eauto.
    }
    eapply isim_init; eauto.
    iIntros "H". iApply isim_upd. iStopProof; eauto.
  Qed.

  Lemma isim_progress
    r g {R} RR st_src st_tgt i_src i_tgt
  :
    bi_entails
      (@isim g g R RR false false (st_src, i_src) (st_tgt, i_tgt))
      (@isim r g R RR true true (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    uiprop. i. eapply hpsim_progress_flag. eauto.
  Qed.  

  Lemma isim_triggerUB_src
    r g {R} RR ps pt X st_src st_tgt (k_src: X -> _) i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    iIntros "H". unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger
    r g {R} RR ps pt st_src st_tgt i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply isim_triggerUB_src. auto.
  Qed.

  Lemma isim_triggerNB_tgt
    r g {R} RR ps pt X st_src st_tgt i_src (k_tgt: X -> _)
  :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger
    r g {R} RR ps pt st_src st_tgt i_src
  :
    bi_entails
      (⌜True⌝)
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply isim_triggerNB_tgt. auto.
  Qed.

  Lemma isim_unwrapU_src
      r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
        (@isim r g R RR ps pt (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. auto. }
  Qed.

  (* Lemma isim_unwrapU_src_trigger
        r g {R} RR ps pt st_src st_tgt X (x: option X) i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim r g RR ps pt (st_src, Ret x') (st_tgt, i_tgt))
        (@isim r g R RR ps pt (st_src, unwrapU x) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iApply isim_unwrapU_src.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed. *)

  Lemma isim_unwrapN_src
    r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @isim r g R RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (isim r g RR ps pt (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  (* Lemma isim_unwrapN_src_trigger
        R_src R_tgt Frz
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt x i_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) Frz RR (st_src, Ret x') (st_tgt, i_tgt))
        (isim (r, g, ps, pt) Frz RR (st_src, unwrapN x) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapN_src. iExists x'. iSplit; auto.
  Qed. *)

  Lemma isim_unwrapU_tgt
    r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @isim r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (isim r g RR ps pt (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  (* Lemma isim_unwrapU_tgt_trigger
        R_src R_tgt Frz
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt x i_src
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, Ret x'))
        (isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, unwrapU x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapU_tgt. iExists x'. iSplit; auto.
  Qed. *)

  Lemma isim_unwrapN_tgt
    r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -* @isim r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (isim r g RR ps pt (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. auto. }
  Qed.

  (* Lemma isim_unwrapN_tgt_trigger
        R_src R_tgt Frz
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt x i_src
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, Ret x'))
        (isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, unwrapN x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iApply isim_unwrapN_tgt.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed. *)

  Definition isim_fsem isim_RR: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: Ist st_src st_tgt ε),
                ⊢ @isim bot7 bot7 Any.t isim_RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  Definition isim_fnsem isim_RR: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq (isim_fsem isim_RR).

End SIM.

Global Opaque isim.


Module IModSemPair.
Section ISIMMODSEM.
  Context `{Σ: GRA.t}.
  Variable (ms_src ms_tgt: HModSem.t).
  Let fl_src := ms_src.(HModSem.fnsems).
  Let fl_tgt := ms_tgt.(HModSem.fnsems).
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable isim_RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp.


  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    (* Ist: Any.t -> Any.t -> iProp; *)
    (* isim_RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp; *)
    isim_fnsems: Forall2 (isim_fnsem Ist fl_src fl_tgt isim_RR) ms_src.(HModSem.fnsems) ms_tgt.(HModSem.fnsems);
    isim_initial: Ist (ms_src.(HModSem.initial_st)) (ms_tgt.(HModSem.initial_st)) ε;
  }.


End ISIMMODSEM.
End IModSemPair.

Module IModPair.
Section ISIMMOD.
  Context `{Σ: GRA.t}.
   Variable (md_src md_tgt: HMod.t).
   Variable Ist: Any.t -> Any.t -> iProp.
   Variable isim_RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp.

   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(HMod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: IModSemPair.sim (md_src.(HMod.get_modsem) sk) (md_tgt.(HMod.get_modsem) sk) Ist isim_RR>>;
     sim_sk: <<SIM: md_src.(HMod.sk) = md_tgt.(HMod.sk)>>;
   }.

End ISIMMOD.
End IModPair.

(* Section TACTICS. *)

  Ltac ired_l := try Red.prw ltac:(IRed._red_gen) 1 2 1 0.
  Ltac ired_r := try Red.prw ltac:(IRed._red_gen) 1 1 1 0.
  Ltac ired_both := ired_l; ired_r.
  Ltac prep := cbn; ired_both.

  Ltac force_l :=
    prep;
    match goal with
    | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
        (* let tvar := fresh "tmp" in *)
        (* let thyp := fresh "TMP" in *)
        (* remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar; *)
        (* let name := fresh "G" in *)
        (* destruct (ox) eqn:name; [|exfalso]; cycle 1 *)
        idtac
        (* let name := fresh "y" in *)
        (* iApply isim_unwrapN_src; iIntros (name) "%"; *)
        (* match goal with *)
        (* | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in * *)
        (* end *)
    end
  .

Ltac force_r :=
  prep;
  match goal with
  | [ |- environments.envs_entails _ (@isim _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
      idtac
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      let name := fresh "G" in
      cut (P); [intros name; iApply isim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1
  end
.


Ltac step0 :=
  match goal with
  (** src **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapU_src; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
      iApply isim_assume_src; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
      iApply isim_tau_src
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (SUpdate _) >>= _) (_, _)) ] =>
      iApply isim_supdate_src

  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply isim_take_src; iIntros (name)

  (** tgt **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_unwrapN_tgt; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
      iApply isim_guarantee_tgt; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply isim_tau_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (SUpdate _) >>= _)) ] =>
      iApply isim_supdate_tgt
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply isim_choose_tgt; iIntros (name)

  (** call **)
  (* | [ |- environments.envs_entails _ (isim  _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _)
                                           (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
      iApply isim_call *)

  (** ret **)
  | [ |- environments.envs_entails _ (isim _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply isim_ret
  end.

  Ltac icall := iApply isim_call.
  Ltac inline_l := iApply isim_inline_src.
  Ltac inline_r := iApply isim_inline_tgt.

  Ltac des_pairs :=
    repeat match goal with
           | [H: context[let (_, _) := ?x in _] |- _] =>
               let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
           | |- context[let (_, _) := ?x in _] =>
               let n0 := fresh x in let n1 := fresh x in destruct x as [n0 n1]
           end.
  
  Ltac steps :=
    repeat (prep; try step0; simpl; des_pairs).

  (* Temporary Tactics *)
  Tactic Notation "steps!" := repeat (prep; try step0; try icall; des_pairs).
  Tactic Notation "ired_" := repeat (
    unfold fun_spec_hp, body_spec_hp;
    try rewrite interp_hAGEs_bind;
    try rewrite interp_hAGEs_tau;
    try rewrite interp_hAGEs_ret;
    try rewrite interp_hAGEs_call;
    try rewrite interp_hAGEs_triggere;
    try rewrite interp_hAGEs_triggerp;
    try rewrite interp_hAGEs_triggerUB;
    try rewrite interp_hAGEs_triggerNB;
    try rewrite interp_hAGEs_unwrapU;
    try rewrite interp_hAGEs_unwrapN;
    try rewrite interp_hAGEs_Assume;
    try rewrite interp_hAGEs_Guarantee;
    try rewrite interp_hAGEs_ext
  ).
  Section TEST.
    Definition mss0: HModSem.t := {|
      HModSem.fnsems := [("f0", (fun _ => Ret tt↑))];
      HModSem.initial_st := tt↑
    |}.

    Definition mss1: HModSem.t := {|
      HModSem.fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      HModSem.initial_st := tt↑
    |}.

    Definition mtt0: HModSem.t := {|
      HModSem.fnsems := [("f0", (fun _ => Ret tt↑))];
      HModSem.initial_st := tt↑
    |}.

    Definition mtt1: HModSem.t := {|
      HModSem.fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      HModSem.initial_st := tt↑
    |}.

    Definition ms0 := {|
      HMod.get_modsem := fun _ => mss0;
      HMod.sk := Sk.unit;
    |}.

    Definition ms1 := {|
      HMod.get_modsem := fun _ => mss1;
      HMod.sk := Sk.unit;
    |}.

    Definition mt0 := {|
      HMod.get_modsem := fun _ => mtt0;
      HMod.sk := Sk.unit;
    |}.

    Definition mt1 := {|
      HMod.get_modsem := fun _ => mtt1;
      HMod.sk := Sk.unit;
    |}.

    Definition Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
    Definition isim_RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.

    Goal IModPair.sim (HMod.add ms0 ms1) (HMod.add mt0 mt1) Ist isim_RR.
    Proof.
      econs; ss.
      ii. econs. 
      { econs.
        { econs; ss.  
          grind. iIntros. steps!.
          unfold isim_RR. et. 
        }
        econs.
        { econs; ss. grind.
          iIntros. steps!. unfold isim_RR. et.
        }
        econs; ss. econs; ss. grind.
        iIntros. steps!. iSplitL; et. iIntros.
        steps. inline_l; et. inline_r; et. steps.
        unfold isim_RR. et.
      }
      unfold Ist. rr. uipropall. 
    Qed.


  End TEST.

(* End TACTICS. *)



(* 
Section STSIM.

  Context `{Invs : @InvSet Σ}.
  Context `{COPSETRA : @GRA.inG CoPset.t Σ}.
  Context `{GSETRA : @GRA.inG Gset.t Σ}.
  Context `{INVSETRA : @GRA.inG (InvSetRA Var) Σ}.

  (* Let lift_rel (rr: rel):
    forall R_src R_tgt (QQ: R_src -> R_tgt -> shared_rel), bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> shared_rel :=
        fun R_src R_tgt QQ ps pt i_src i_tgt ths im_src im_tgt st_src st_tgt =>
          (∃ (RR: R_src -> R_tgt -> iProp)
             (EQ: QQ = (fun r_src r_tgt ths im_src im_tgt st_src st_tgt =>
                          (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** RR r_src r_tgt)),
              rr R_src R_tgt RR ps pt i_src i_tgt ** (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)))%I. *)

  Definition stsim (E : coPset) 
    r g {R} (RR: Any.t * R -> Any.t * R -> iProp) ps pt 
    '(st_src, i_src)
    '(st_tgt, i_tgt) 
  :=
    ((wsat ** OwnE E)
            -*
            (@isim r g R
              (fun '(st_src, ret_src) '(st_tgt, ret_tgt) 
                => (wsat ** OwnE ⊤) ** RR (st_src, ret_src) (st_tgt, ret_tgt))
              ps pt (st_src, i_src) (st_tgt, i_tgt)))%I.


  Definition stsim (E : coPset) : rel -> rel -> rel :=
    fun r g
        R_src R_tgt RR ps pt i_src i_tgt =>
      (∀ ths im_src im_tgt st_src st_tgt,
          (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE E))
            -*
            (isim
               tid
               I
               (lift_rel r)
               (lift_rel g)
               (fun r_src r_tgt ths im_src im_tgt st_src st_tgt => (default_I_past tid ths im_src im_tgt st_src st_tgt ** (wsat ** OwnE ⊤)) ** RR r_src r_tgt)
               ps pt i_src i_tgt
               ths im_src im_tgt st_src st_tgt))%I


  (***** stsim lemmas ****)

  Lemma stsim_ret 

  Lemma stsim_syscall
    E r g {R} RR ps pt st_src st_tgt k_src k_tgt fn varg rvs
  :
    (∀ vret, @stsim E r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
  -∗
    (stsim E r g RR ps pt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iApply isim_syscall. iIntros. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma stsim_tau_src
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@stsim E r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (stsim E r g RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_src. iFrame.
  Qed.


  Lemma stsim_tau_tgt
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@stsim E r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (stsim E r g RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_tgt. iFrame.
  Qed.

  Lemma stsim_choose_src 
    E X x r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (@stsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (stsim E r g RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_choose_src. iFrame.
  Qed.

  Lemma stsim_choose_tgt 
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (∀ x, @stsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (stsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iApply isim_choose_tgt. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma stsim_take_src 
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (∀ x, @stsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (stsim E r g RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iApply isim_take_src. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma stsim_take_tgt 
    E X x r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (@stsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (stsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_take_tgt. iFrame.
  Qed.
  
  Lemma stsim_supdate_src
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@stsim E r g R RR true pt ((run st_src).1, k_src (run st_src).2) (st_tgt, i_tgt))
  -∗
    (stsim E r g RR ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold stsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_src. iFrame.
  Qed.

  Lemma stsim_supdate_tgt
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@stsim E r g R RR ps true (st_src, i_src) ((run st_tgt).1, k_tgt (run st_tgt).2))
  -∗
    (stsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_tgt. iFrame.
  Qed.

  Lemma stsim_assume_src
    E r g {R} RR ps pt iP k_src i_tgt
  :
    (iP -* (@stsim E r g R RR true pt (k_src tt) i_tgt))
  -∗
    (@stsim E r g R RR ps pt (trigger (Assume iP) >>= k_src) i_tgt).
  Proof.
    unfold stsim. iIntros "H" (? ?) "D".
    iApply isim_assume_src. iIntros "IP".
    iPoseProof ("H" with "IP") as "H".
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma stsim_assume_tgt
    E r g {R} RR ps pt iP i_src k_tgt
  :
    (iP ** (@stsim E r g R RR ps true i_src (k_tgt tt)))
  -∗
    (@stsim E r g R RR ps pt i_src (trigger (Assume iP) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "[IP H]" (? ?) "D".
    iApply isim_assume_tgt. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma stsim_guarantee_src
    E r g {R} RR ps pt iP k_src i_tgt
  :
    (iP ** @stsim E r g R RR true pt (k_src tt) i_tgt)
  -∗
    (@stsim E r g R RR ps pt (trigger (Guarantee iP) >>= k_src) i_tgt).
  Proof.
    unfold stsim. iIntros "[IP H]" (? ?) "D". 
    iApply isim_guarantee_src. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.  
    
  Lemma stsim_guarantee_tgt
    E r g {R} RR ps pt iP i_src k_tgt
  :
    (iP -* @stsim E r g R RR ps true i_src (k_tgt tt))
  -∗
    (@stsim E r g R RR ps pt i_src (trigger (Guarantee iP) >>= k_tgt)).
  Proof.
    unfold stsim. iIntros "H" (? ?) "D".
    iApply isim_guarantee_tgt. iIntros "IP".
    iPoseProof ("H" with "IP") as "H".
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.  

End STSIM.

 *)





(*  




  Program Definition isim'
          r g p_src p_tgt
          {R}
          (RR: Any.t * R-> Any.t * R -> iProp)
          (sti_src sti_tgt : Any.t * itree hAGEs R): iProp := 
    iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) r g _ RR p_src p_tgt sti_src sti_tgt) _.
  Next Obligation.
    guclo hpsim_extendC_spec. econs; et.
  Qed.
    (* i. ss. eapply H. eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed. *)

  (* Program Definition isim'
          r g ps pt
          {R_src R_tgt}
          (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
          (fuel: option Ord.t)
          (st_src: Any.t * itree hEs R_src)
          (st_tgt: Any.t * itree Es R_tgt): iProp :=
    iProp_intro (fun res =>
                   forall ctx (WF: URA.wf (res ⋅ ctx)),
                     gpaco9 (_hsim) (cpn9 _hsim) r g _ _ RR ctx fuel ps pt st_src st_tgt) _.
  Next Obligation.
    i.  ss. i. eapply H. eapply URA.wf_extends; eauto. eapply URA.extends_add; eauto.
  Qed. *)

  Definition isim
             '(r, g, p_src, p_tgt)
             {R}
             (RR: Any.t * R -> Any.t * R -> iProp)
             (sti_src sti_tgt : Any.t * itree hAGEs R): iProp := 
    isim' r g p_src p_tgt RR sti_src sti_tgt.
    


  Lemma isim_init
        R (RR: Any.t * R -> Any.t * R -> iProp)
        P r g p_src p_tgt st_src st_tgt i_src i_tgt
        fmr
        (ENTAIL: bi_entails
                   P
                   (isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt)))
        (CUR: Own fmr ⊢ P)
        (WF: URA.wf fmr)
    :
      gpaco7 _hpsim (cpn7 _hpsim) r g _ RR p_src p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    assert (Own fmr ⊢ isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt)).
    { etrans; et. }
    unfold isim in H. unfold isim' in H. uipropall. eapply H; et. refl.
  Qed.

  (* Lemma isim_init
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g ctx fuel ps pt st_src st_tgt i_src i_tgt
        (ENTAIL: bi_entails
                   P
                   (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt)))
        (CUR: current_iProp ctx P)
    :
      gpaco9 _hsim (cpn9 _hsim) r g _ _ RR ctx fuel ps pt (st_src, i_src) (st_tgt, i_tgt).
  Proof.
    eapply current_iProp_entail in ENTAIL; eauto.
    inv ENTAIL. unfold isim in IPROP. eapply IPROP; eauto.
  Qed. *)

  Lemma isim_final
        R (RR: Any.t * R -> Any.t * R -> iProp)
        P r g p_src p_tgt st_src st_tgt i_src i_tgt
        (SIM: forall fmr (CUR: Own fmr ⊢ P) (WF: URA.wf fmr),
            gpaco7 _hpsim (cpn7 _hpsim) r g _ RR p_src p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      bi_entails
        P
        (isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    uipropall. ii.
    specialize (SIM r0). uipropall.
    eapply SIM; et. i. eapply iProp_mono; et. 
  Qed.

  (* Lemma isim_final
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        P r g fuel ps pt st_src st_tgt i_src i_tgt
        (SIM: forall ctx
                     (CUR: current_iProp ctx P),
            gpaco9 _hsim (cpn9 _hsim) r g _ _ RR ctx fuel ps pt (st_src, i_src) (st_tgt, i_tgt))
    :
      bi_entails
        P
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    uipropall. ii. eapply SIM. econs; eauto.
  Qed. *)

  Lemma isim_current
        R (RR: Any.t * R -> Any.t * R -> iProp)
        r g p_src p_tgt st_src st_tgt i_src i_tgt
        fmr
        (CUR: Own fmr ⊢ isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt))
        (WF: URA.wf fmr)
    :
        gpaco7 _hpsim (cpn7 _hpsim) r g _ RR p_src p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr.
  Proof.
    uipropall. eapply CUR; et. refl.
  Qed.

  (* Lemma isim_current
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ctx ps pt st_src st_tgt i_src i_tgt
        (CUR: current_iProp ctx (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt)))
    :
      gpaco9 _hsim (cpn9 _hsim) r g _ _ RR ctx fuel ps pt (st_src, i_src) (st_tgt, i_tgt).
  Proof.
    inv CUR. eapply IPROP; eauto.
  Qed. *)

  Lemma isim_upd 
        R (RR: Any.t * R -> Any.t * R -> iProp)
        r g p_src p_tgt st_src st_tgt (ret_src ret_tgt: R)
    :
      bi_entails
        (#=> (isim (r, g, p_src, p_tgt) (fun '(st_src, ret_src) '(st_tgt, ret_tgt) => #=> RR (st_src, ret_src) (st_tgt, ret_tgt)) st_src st_tgt))
        (isim (r, g, p_src, p_tgt) RR st_src st_tgt).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    rr in H. unfold bi_bupd_bupd in H. ss. unfold Upd in H. autorewrite with iprop in H.
    i. hexploit H; eauto. i. des.
    hexploit (H1 ε); r_solve; et. i.
    (* uclo hmonoC_spec. econs; auto. *)
  (* Qed. *)
  Admitted.
  
  (* Lemma isim_upd R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt
    :
      bi_entails
        (#=> (isim (r, g, ps, pt) (fun st_src st_tgt ret_src ret_tgt => #=> RR st_src st_tgt ret_src ret_tgt) fuel st_src st_tgt))
        (isim (r, g, ps, pt) RR fuel st_src st_tgt).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    rr in H. unfold bi_bupd_bupd in H. ss. unfold Upd in H. autorewrite with iprop in H.
    i. hexploit H; eauto. i. des.
    hexploit H1; eauto. i. guclo hmonoC_spec. econs; auto.
  Qed. *)

  Lemma isim_mono
        R (RR RR': Any.t * R -> Any.t * R -> iProp)
        r g p_src p_tgt st_src i_src st_tgt i_tgt
        (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (RR (st_src, ret_src) (st_tgt, ret_tgt)) (RR' (st_src, ret_src) (st_tgt, ret_tgt))))
    :
      bi_entails
        (isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, p_src, p_tgt) RR' (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i. hexploit H; eauto. i.
    (* guclo hmonoC_spec. econs; eauto. i. iIntros "H". *)
    (* iModIntro. iApply MONO. auto. *)
  (* Qed. *)
  Admitted.

  (* Lemma isim_mono R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src i_src st_tgt i_tgt
        (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (Q0 st_src st_tgt ret_src ret_tgt) (Q1 st_src st_tgt ret_src ret_tgt)))
    :
      bi_entails
        (isim (r, g, ps, pt) Q0 fuel (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) Q1 fuel (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i. hexploit H; eauto. i.
    guclo hmonoC_spec. econs; eauto. i. iIntros "H".
    iModIntro. iApply MONO. auto.
  Qed. *)

  Lemma isim_wand 
        R (RR RR': Any.t * R -> Any.t * R -> iProp)
        r g p_src p_tgt st_src i_src st_tgt i_tgt
    :
      bi_entails
        ((∀ st_src st_tgt ret_src ret_tgt,
             ((RR (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR' (st_src, ret_src) (st_tgt, ret_tgt)))) ** (isim (r, g, p_src, p_tgt) RR (st_src, i_src) (st_tgt, i_tgt)))
        (isim (r, g, p_src, p_tgt) RR' (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    (* red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' in *. rr. i.
    rr in H. unfold Sepconj in H. autorewrite with iprop in H.
    des. clarify. eapply from_semantic in H0. hexploit (H1 (ctx ⋅ a)).
    { r_wf WF0. }
    i. guclo hframeC_aux_spec. econs.
    { instantiate (1:=a). eapply URA.wf_mon. instantiate (1:=b). r_wf WF0. }
    guclo hmonoC_spec. econs.
    { eapply H. }
    i. iIntros "H0". iModIntro. iIntros "H1".
    iPoseProof (H0 with "H1") as "H1".
    iMod "H1". iApply "H1". iApply "H0".
  Qed. *)
  Admitted.

  (* Lemma isim_wand R_src R_tgt
        (Q0 Q1: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src i_src st_tgt i_tgt
    :
      bi_entails
        ((∀ st_src st_tgt ret_src ret_tgt,
             ((Q0 st_src st_tgt ret_src ret_tgt) -∗ (Q1 st_src st_tgt ret_src ret_tgt))) ** (isim (r, g, ps, pt) Q0 fuel (st_src, i_src) (st_tgt, i_tgt)))
        (isim (r, g, ps, pt) Q1 fuel (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' in *. rr. i.
    rr in H. unfold Sepconj in H. autorewrite with iprop in H.
    des. clarify. eapply from_semantic in H0. hexploit (H1 (ctx ⋅ a)).
    { r_wf WF0. }
    i. guclo hframeC_aux_spec. econs.
    { instantiate (1:=a). eapply URA.wf_mon. instantiate (1:=b). r_wf WF0. }
    guclo hmonoC_spec. econs.
    { eapply H. }
    i. iIntros "H0". iModIntro. iIntros "H1".
    iPoseProof (H0 with "H1") as "H1".
    iMod "H1". iApply "H1". iApply "H0".
  Qed. *)

  Lemma isim_bind 
        R S (RR: Any.t * R -> Any.t * R -> iProp)
        r g p_src p_tgt st_src st_tgt (i_src i_tgt: itree hAGEs S)
        k_src k_tgt
    :
      bi_entails
        (isim (r, g, p_src, p_tgt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) RR (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt)) (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, p_src, p_tgt) RR (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbindC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_bind R_src R_tgt S_src S_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src (i_src: itree hEs S_src)
        k_src st_tgt (i_tgt: itree Es S_tgt) k_tgt
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) RR None (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt)) fuel (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbindC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_bind_left R_src R_tgt S_src
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src (i_src: itree hEs S_src)
        k_src st_tgt i_tgt
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) RR None (st_src, k_src ret_src) (st_tgt, i_tgt)) fuel (st_src, i_src) (st_tgt, Ret tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: i_tgt = Ret tt >>= fun _ => i_tgt).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_bind_right R_src R_tgt S_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src i_src
        st_tgt (i_tgt: itree Es S_tgt) k_tgt
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) RR None (st_src, i_src) (st_tgt, k_tgt ret_tgt)) fuel (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    iIntros "H".
    assert (EQ: i_src = Ret tt >>= fun _ => i_src).
    { grind. }
    rewrite EQ. iApply isim_bind. rewrite <- EQ. iApply "H".
  Qed.

  Lemma isim_bind_right_pure R_src R_tgt S_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src i_src
        st_tgt (i_tgt: itree Es S_tgt) k_tgt
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt ret_src ret_tgt => isim (r, g, false, false) RR fuel (st_src, i_src) (st_tgt, k_tgt ret_tgt)) None (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hbind_rightC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_split_aux R_src R_tgt S_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src i_src st_tgt (i_tgt: itree Es S_tgt) k_tgt
        fuel0 fuel1 ps pt
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt _ ret_tgt => isim (r, g, false, false) RR (Some fuel1) (st_src, i_src) (st_tgt, k_tgt ret_tgt)) (Some fuel0) (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR (Some (fuel1 + fuel0)%ord) (st_src, i_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim in *. i.
    guclo hsplitC_spec. econs.
    { eapply H; eauto. }
    i. inv POST. eapply IPROP. eauto.
  Qed.

  Lemma isim_call_impure
        pre post w0
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt fn arg_src arg_tgt k_src k_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post false)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           ** (∀ st_src st_tgt ret_src ret_tgt,
                  inv_with le I w0 st_src st_tgt -* (post ret_src ret_tgt: iProp) -* isim (g, g, true, true) RR None (st_src, k_src ret_src) (st_tgt, k_tgt ret_tgt)))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Call fn arg_src) >>= k_src) (st_tgt, trigger (Call fn arg_tgt) >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp ctx P)
    end.
    { econs; eauto. }
    apply current_iPropL_convert in CUR. mDesAll.
    ired_both. gstep. inv SPEC. econs; eauto.
    { mAssert _ with "A1".
      { iApply (PRE with "A1"). }
      mUpd "A2".
      eapply current_iProp_entail; [eapply CUR|]. start_ipm_proof.
      iSplitR "A2"; [|iExact "A2"].
      iSplitR "H"; [|iExact "H"].
      iExact "A".
    }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    i. apply current_iPropL_convert in ACC.
    mDesAll. mSpcUniv "H" with st_src1.
    mSpcUniv "H" with st_tgt1.
    mSpcUniv "H" with ret_src.
    mSpcUniv "H" with ret_tgt.
    mAssert _ with "A".
    { iApply (POST with "A"). }
    mUpd "A2".
    mAssert (isim (g, g, true, true) RR None (st_src1, k_src ret_src)
                  (st_tgt1, k_tgt ret_tgt)) with "*".
    { iApply ("H" with "A1 A2"). }
    inv ACC. rr in IPROP. uipropall. des. subst.
    eapply IPROP0. eapply URA.wf_mon. instantiate (1:=b). r_wf GWF.
  Qed.

  Lemma isim_call_pure
        pre post w0 fuel1
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt fn arg_src arg_tgt i_src k_tgt
        fuel0
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post true)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (pre: iProp)
                  **
                  (∀ st_src st_tgt ret_src ret_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (post ret_src ret_tgt: iProp)) -* isim (g, g, true, true) RR (Some fuel1) (st_src, i_src) (st_tgt, k_tgt ret_tgt)))
        (isim (r, g, ps, pt) RR (Some fuel0) (st_src, i_src) (st_tgt, trigger (Call fn arg_tgt) >>= k_tgt)).
  Proof.
    red. unfold Entails. autorewrite with iprop.
    unfold isim, isim' at 2. rr. i.
    match (type of H) with
    | (iProp_pred ?P) _ =>
      assert (CUR: current_iProp ctx P)
    end.
    { econs; eauto. }
    apply current_iPropL_convert in CUR.
    mDesAll. ired_both. gstep. inv SPEC. econs; eauto.
    { mAssert _ with "A1".
      { iApply (PRE with "A1"). }
      mUpd "A2".
      eapply current_iProp_entail; [eapply CUR|]. start_ipm_proof.
      iSplitR "A2"; [|iExact "A2"].
      iSplitR "H"; [|iExact "H"].
      iExact "A".
    }
    { revert MEASURE TBR. generalize o. i. destruct (measure fsp x), o0; ss. }
    esplits; eauto.
    i. apply current_iPropL_convert in ACC.
    mDesAll. mSpcUniv "H" with st_src1.
    mSpcUniv "H" with st_tgt1.
    mSpcUniv "H" with ret_src.
    mSpcUniv "H" with ret_tgt.
    mAssert _ with "A".
    { iApply (POST with "A"). }
    mUpd "A2".
    mAssert (isim (g, g, true, true) RR (Some fuel1) (st_src1, i_src) (st_tgt1, k_tgt ret_tgt)) with "*".
    { iApply "H". iSplitR "A2"; auto. }
    inv ACC. rr in IPROP. uipropall. des. subst. eapply IPROP0.
    eapply URA.wf_mon. instantiate (1:=b). r_wf GWF.
  Qed.

  Lemma isim_apc
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt k_src i_tgt
        fuel0
    :
      bi_entails
        (∃ fuel1, isim (r, g, true, pt) RR fuel1 (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel0 (st_src, trigger hAPC >>= k_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i.
    inv CUR. rr in IPROP. uipropall. des.
    eapply hsimC_uclo. econs; eauto.
  Qed.

  Lemma isim_progress R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel st_src i_src st_tgt i_tgt
    :
      bi_entails
        (isim (g, g, false, false) RR fuel (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, true, true) RR fuel (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    eapply hsim_progress_flag. auto.
  Qed.

  Lemma isim_knowledge_mon
        r0 g0
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r1 g1 st_src i_src st_tgt i_tgt
        fuel ps pt
        (LE0: r0 <9= r1)
        (LE1: g0 <9= g1)
    :
      bi_entails
        (isim (r0, g0, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt))
        (isim (r1, g1, ps, pt) RR fuel (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    eapply gpaco9_mon; eauto.
  Qed.

  Lemma isim_flag_mon
        fuel0 f_src0 f_tgt0
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src i_src st_tgt i_tgt
        fuel1 f_src1 f_tgt1
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
        (FUEL: option_Ord_le fuel0 fuel1)
    :
      bi_entails
        (isim (r, g, f_src0, f_tgt0) RR fuel0 (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, f_src1, f_tgt1) RR fuel1 (st_src, i_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply isim_current in CUR.
    guclo hflagC_spec. econs; eauto.
  Qed.

  Lemma isim_split
        fuel0 fuel1
        R_src R_tgt S_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g st_src i_src st_tgt (i_tgt: itree Es S_tgt) k_tgt
        fuel ps pt
        (FUEL: (fuel1 + fuel0 <= fuel)%ord)
    :
      bi_entails
        (isim (r, g, ps, pt) (fun st_src st_tgt _ ret_tgt => isim (r, g, false, false) RR (Some fuel1) (st_src, i_src) (st_tgt, k_tgt ret_tgt)) (Some fuel0) (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR (Some fuel) (st_src, i_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    iIntros "H".
    iApply isim_flag_mon.
    { eauto. }
    { eauto. }
    { instantiate (1:=Some (fuel1 + fuel0)%ord). ss. }
    iApply isim_split_aux. auto.
  Qed.

  Lemma isim_ret
        R_src R_tgt (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g
        v_src v_tgt
        st_src st_tgt
        fuel ps pt
    :
      bi_entails
        (RR st_src st_tgt v_src v_tgt)
        (isim (r, g, ps, pt) RR fuel (st_src, Ret v_src) (st_tgt, (Ret v_tgt))).
  Proof.
    eapply isim_final. i.
    eapply hsimC_uclo. econs; eauto.
  Qed.

  Lemma isim_apc_trigger
        R_tgt
        (RR: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g ps pt st_src st_tgt i_tgt
        fuel0
    :
      bi_entails
        (∃ fuel1, isim (r, g, true, pt) RR fuel1 (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel0 (st_src, trigger hAPC) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (hAPC))).
    iIntros "H". iApply isim_apc. iExact "H".
  Qed.

  Lemma isim_call_impure_trigger
        pre post w0
        (RR: Any.t -> Any.t -> Any.t -> Any.t -> iProp)
        r g fuel ps pt st_src st_tgt fn arg_src arg_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post false)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           **
           (∀ st_src st_tgt ret_src ret_tgt,
               (inv_with le I w0 st_src st_tgt) -* (post ret_src ret_tgt: iProp) -* RR st_src st_tgt ret_src ret_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Call fn arg_src)) (st_tgt, trigger (Call fn arg_tgt))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Call fn arg_src))).
    erewrite (@idK_spec _ _ (trigger (Call fn arg_tgt))).
    iIntros "H". iApply isim_call_impure; eauto.
    iDestruct "H" as "[H0 H1]". iSplitL "H0"; auto.
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0 H2".
    iApply isim_ret. iApply ("H1" with "H0 H2").
  Qed.

  Lemma isim_call_pure_trigger
        pre post w0
        (RR: Any.t -> Any.t -> unit -> Any.t -> iProp)
        r g ps pt st_src st_tgt fn arg_src arg_tgt
        (SPEC: fn_has_spec fn arg_src arg_tgt pre post true)
    :
      bi_entails
        ((inv_with le I w0 st_src st_tgt)
           ** (pre: iProp)
           **
           (∀ st_src st_tgt ret_src ret_tgt,
               (inv_with le I w0 st_src st_tgt) -* (post ret_src ret_tgt: iProp) -* RR st_src st_tgt tt ret_tgt))
        (isim (r, g, ps, pt) RR (Some (1: Ord.t)) (st_src, Ret tt) (st_tgt, trigger (Call fn arg_tgt))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Call fn arg_tgt))).
    iIntros "H". iApply isim_call_pure; eauto.
    { oauto. }
    iDestruct "H" as "[H0 H1]". iSplitL "H0"; auto.
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "[H0 H2]".
    iApply isim_ret. iApply ("H1" with "H0 H2").
  Qed.

  Global Instance iProp_isim_absorbing
         R_src R_tgt r g (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         fuel ps pt st_src st_tgt:
    Absorbing (isim (r, g, ps, pt) RR fuel st_src st_tgt).
  Proof.
    unfold Absorbing. unfold bi_absorbingly.
    iIntros "[H0 H1]". iApply isim_upd.
    iDestruct "H0" as "%". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Global Instance iProp_isim_elim_upd
         R_src R_tgt r g (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
         fuel ps pt st_src st_tgt
         P:
    ElimModal True false false (#=> P) P (isim (r, g, ps, pt) RR fuel st_src st_tgt) (isim (r, g, ps, pt) RR fuel st_src st_tgt).
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    destruct st_src, st_tgt. iApply isim_mono; [|iApply "H1"; auto].
    i. ss. iIntros "H". iModIntro. auto.
  Qed.

  Lemma isim_syscall
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        fn arg rvs
        r g fuel ps pt st_src st_tgt k_src k_tgt
    :
      bi_entails
        (∀ ret, isim (g, g, true, true) RR None (st_src, k_src ret) (st_tgt, k_tgt ret))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Syscall fn arg rvs) >>= k_src) (st_tgt, trigger (Syscall fn arg rvs) >>= k_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    i. inv CUR. rr in IPROP. uipropall. eapply IPROP; eauto.
  Qed.

  Lemma isim_syscall_trigger
        (RR: Any.t -> Any.t -> Any.t -> Any.t -> iProp)
        fn arg_src arg_tgt rvs
        r g fuel ps pt st_src st_tgt
    :
      bi_entails
        (⌜arg_src = arg_tgt⌝ ** ∀ ret, RR st_src st_tgt ret ret)
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Syscall fn arg_src rvs)) (st_tgt, trigger (Syscall fn arg_tgt rvs))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Syscall fn arg_src rvs))).
    erewrite (@idK_spec _ _ (trigger (Syscall fn arg_tgt rvs))).
    iIntros "[% H1]". subst.
    iApply isim_syscall. iIntros (ret).
    iApply isim_ret. iApply "H1".
  Qed.

  Lemma isim_tau_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_src i_tgt
    :
      bi_entails
        (isim (r, g, true, pt) RR None (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_tau_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_src i_tgt
    :
      bi_entails
        (isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_choose_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X k_src i_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, pt) RR None (st_src, k_src x) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
  Qed.

  Lemma isim_choose_src_trigger
        X R_tgt
        (RR: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_tgt
    :
      bi_entails
        (∃ x, isim (r, g, true, pt) RR None (st_src, Ret x) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Choose X)) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_src.
    iDestruct "H" as (x) "H". iExists x. auto.
  Qed.

  Lemma isim_choose_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X i_src k_tgt
    :
      bi_entails
        (∀ x, isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, k_tgt x))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. i. eapply IPROP; eauto.
  Qed.

  Lemma isim_choose_tgt_trigger
        R_src X
        (RR: Any.t -> Any.t -> R_src -> X -> iProp)
        r g fuel ps pt st_src st_tgt i_src
    :
      bi_entails
        (∀ x, isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, Ret x))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (Choose X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Choose X))).
    iIntros "H". iApply isim_choose_tgt.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X k_src i_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, pt) RR None (st_src, k_src x) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. i. eapply IPROP; eauto.
  Qed.

  Lemma isim_take_src_trigger
        X R_tgt
        (RR: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_tgt
    :
      bi_entails
        (∀ x, isim (r, g, true, pt) RR None (st_src, Ret x) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (Take X)) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_src.
    iIntros (x). iApply "H".
  Qed.

  Lemma isim_take_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X i_src k_tgt
    :
      bi_entails
        (∃ x, isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, k_tgt x))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    inv CUR. rr in IPROP. uipropall. des. esplits. eapply IPROP; eauto.
  Qed.

  Lemma isim_take_tgt_trigger
        R_src X
        (RR: Any.t -> Any.t -> R_src -> X -> iProp)
        r g fuel ps pt st_src st_tgt i_src
    :
      bi_entails
        (∃ x, isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, Ret x))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (Take X))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (Take X))).
    iIntros "H". iApply isim_take_tgt.
    iDestruct "H" as (x) "H". iExists x. iApply "H".
  Qed.

  Lemma isim_pput_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src0 st_src1 st_tgt k_src i_tgt
    :
      bi_entails
        (isim (r, g, true, pt) RR None (st_src1, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src0, trigger (PPut st_src1) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_src_trigger
        R_tgt
        (RR: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel ps pt st_src0 st_src1 st_tgt i_tgt
    :
      bi_entails
        (isim (r, g, true, pt) RR None (st_src1, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src0, trigger (PPut st_src1)) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_src1))).
    iIntros "H". iApply isim_pput_src. iApply "H".
  Qed.

  Lemma isim_pget_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt k_src i_tgt
    :
      bi_entails
        (isim (r, g, true, pt) RR None (st_src, k_src st_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (PGet) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_get_src_trigger
        R_tgt
        (RR: Any.t -> Any.t -> Any.t -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_tgt
    :
      bi_entails
        (isim (r, g, true, pt) RR None (st_src, Ret st_src) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, trigger (PGet)) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_src. iApply "H".
  Qed.

  Lemma isim_pput_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt0 st_tgt1 i_src k_tgt
    :
      bi_entails
        (isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt1, k_tgt tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt0, trigger (PPut st_tgt1) >>= k_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pput_tgt_trigger
        R_src
        (RR: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel ps pt st_src st_tgt0 st_tgt1 i_src
    :
      bi_entails
        (isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt1, Ret tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt0, trigger (PPut st_tgt1))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PPut st_tgt1))).
    iIntros "H". iApply isim_pput_tgt. iApply "H".
  Qed.

  Lemma isim_pget_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_src k_tgt
    :
      bi_entails
        (isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, k_tgt st_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (PGet) >>= k_tgt)).
  Proof.
    eapply isim_final. i. eapply hsimC_uclo. econs; eauto.
    eapply isim_current; eauto.
  Qed.

  Lemma isim_pget_tgt_trigger
        R_src
        (RR: Any.t -> Any.t -> R_src -> Any.t -> iProp)
        r g fuel ps pt st_src st_tgt i_src
    :
      bi_entails
        (isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, Ret st_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, trigger (PGet))).
  Proof.
    erewrite (@idK_spec _ _ (trigger (PGet))).
    iIntros "H". iApply isim_pget_tgt. iApply "H".
  Qed.

  Lemma isim_assume_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, pt) RR None (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, assume P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold assume. hred_l.
    iApply isim_take_src. iIntros (H). hred_l. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_assume_src_trigger
        R_tgt
        (RR: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P i_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, true, pt) RR None (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, assume P) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_src.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_assume_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P i_src k_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, k_tgt tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, assume P >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold assume. hred_r. iApply isim_take_tgt.
    iExists H. hred_r. iApply "H".
  Qed.

  Global Instance iProp_pure_elim_affine
         P (RR: iProp):
    ElimModal True false false (<affine> ⌜P⌝) (⌜P⌝) RR RR.
  Proof.
    unfold ElimModal. i. iIntros "[H0 H1]".
    iApply "H1". iApply "H0".
  Qed.

  Lemma isim_assume_tgt_trigger
        R_src
        (RR: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel ps pt st_src st_tgt P i_src
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, Ret tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, assume P)).
  Proof.
    erewrite (@idK_spec _ _ (assume P)).
    iIntros "H". iApply isim_assume_tgt. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P k_src i_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, pt) RR None (st_src, k_src tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, guarantee P >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as "[% H]".
    unfold guarantee. hred_l. iApply isim_choose_src.
    iExists H. hred_l. iApply "H".
  Qed.

  Lemma isim_guarantee_src_trigger
        R_tgt
        (RR: Any.t -> Any.t -> unit -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P i_tgt
    :
      bi_entails
        (⌜P⌝ ∧ isim (r, g, true, pt) RR None (st_src, Ret tt) (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, guarantee P) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_src. iSplit; auto.
    { iDestruct "H" as "[H _]". iApply "H". }
    { iDestruct "H" as "[_ H]". iApply "H". }
  Qed.

  Lemma isim_guarantee_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt P i_src k_tgt
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, k_tgt tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, guarantee P >>= k_tgt)).
  Proof.
    iIntros "H". unfold guarantee. hred_r.
    iApply isim_choose_tgt.
    iIntros (H). hred_r. iApply "H". iPureIntro. auto.
  Qed.

  Lemma isim_guarantee_tgt_trigger
        R_src
        (RR: Any.t -> Any.t -> R_src -> unit -> iProp)
        r g fuel ps pt st_src st_tgt P i_src
    :
      bi_entails
        (⌜P⌝ -* isim (r, g, ps, true) RR fuel (st_src, i_src) (st_tgt, Ret tt))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, guarantee P)).
  Proof.
    erewrite (@idK_spec _ _ (guarantee P)).
    iIntros "H". iApply isim_guarantee_tgt.
    iIntros "H0". iApply "H". auto.
  Qed.

  Lemma isim_triggerUB_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X (k_src: X -> _) i_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, ps, pt) RR fuel (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold triggerUB. hred_l. iApply isim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerUB_src_trigger
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_tgt
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, ps, pt) RR fuel (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply isim_triggerUB_src. auto.
  Qed.

  Lemma isim_triggerNB_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X i_src (k_tgt: X -> _)
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply isim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma isim_triggerNB_trigger
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt i_src
    :
      bi_entails
        (⌜True⌝)
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply isim_triggerNB_tgt. auto.
  Qed.

  Lemma isim_unwrapU_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, ps, pt) RR fuel (st_src, k_src x') (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply isim_triggerUB_src. auto. }
  Qed.

  Lemma isim_unwrapU_src_trigger
        X R_tgt
        (RR: Any.t -> Any.t -> X -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt x i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, ps, pt) RR fuel (st_src, Ret x') (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, unwrapU x) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iApply isim_unwrapU_src.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

  Lemma isim_unwrapN_src
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) RR fuel (st_src, k_src x') (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma isim_unwrapN_src_trigger
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt x i_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) RR fuel (st_src, Ret x') (st_tgt, i_tgt))
        (isim (r, g, ps, pt) RR fuel (st_src, unwrapN x) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapN_src. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapU_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X (x: option X) i_src k_tgt
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, k_tgt x'))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma isim_unwrapU_tgt_trigger
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt x i_src
    :
      bi_entails
        (∃ x', ⌜x = Some x'⌝ ∧ isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, Ret x'))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, unwrapU x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapU x)).
    iIntros "H". iDestruct "H" as (x') "[% H]".
    iApply isim_unwrapU_tgt. iExists x'. iSplit; auto.
  Qed.

  Lemma isim_unwrapN_tgt
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt X (x: option X) i_src k_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, k_tgt x'))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply isim_triggerNB_tgt. auto. }
  Qed.

  Lemma isim_unwrapN_tgt_trigger
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g fuel ps pt st_src st_tgt x i_src
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -* isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, Ret x'))
        (isim (r, g, ps, pt) RR fuel (st_src, i_src) (st_tgt, unwrapN x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iApply isim_unwrapN_tgt.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed.

  Lemma isim_ccallU_pure
        pre post w0 fuel1
        R_src R_tgt
        (RR: Any.t -> Any.t -> R_src -> R_tgt -> iProp)
        r g ps pt st_src st_tgt
        fn X Y arg_src (arg_tgt: X) i_src (k_tgt: Y -> _)
        fuel0
        (SPEC: fn_has_spec fn arg_src (Any.upcast arg_tgt) pre post true)
        (FUEL: Ord.lt fuel1 fuel0)
    :
      bi_entails
        (inv_with le I w0 st_src st_tgt
                  ** (pre: iProp)
                  **
                  (∀ st_src st_tgt ret_src ret_tgt,
                      ((inv_with le I w0 st_src st_tgt) ** (post ret_src ret_tgt: iProp)) -* ∃ ret_tgt', ⌜ret_tgt = Any.upcast ret_tgt'⌝ ∧ isim (g, g, true, true) RR (Some fuel1) (st_src, i_src) (st_tgt, k_tgt ret_tgt')))
        (isim (r, g, ps, pt) RR (Some fuel0) (st_src, i_src) (st_tgt, ccallU fn arg_tgt >>= k_tgt)).
  Proof.
    iIntros "[H0 H1]". unfold ccallU. hred_r. iApply isim_call_pure; eauto.
    iSplitL "H0"; [iExact "H0"|].
    iIntros (st_src0 st_tgt0 ret_src ret_tgt) "H0".
    iPoseProof ("H1" with "H0") as (ret_tgt') "[% H1]". subst.
    hred_r. iApply "H1".
  Qed.
End SIM. *)




