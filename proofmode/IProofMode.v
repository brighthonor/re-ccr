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
Require Import RobustIndexedInvariants.

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
(* Don't want variable stb, o in isim *)
Section SIM.

  Context `{Σ: GRA.t}.
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Let _hpsim := @_hpsim Σ fl_src fl_tgt Ist false.
  Let rel := ∀ R : Type, (Any.t * R → Any.t * R → iProp) → bool → bool → Any.t * itree hAGEs R → Any.t * itree hAGEs R → iProp.

  (**** COMMENT: If using (_ -> iProp) for r, g: need a replacement of 'bot7' in wsim_fsem. ****)

  (* Definition unlift (r: rel) := fun R RR ps pt sti_src sti_tgt res => r R RR ps pt sti_src sti_tgt res. *)

  Variant unlift (r: rel) R RR ps pt sti_src sti_tgt res: Prop :=
    | unlift_intro
        (WF: URA.wf res)
        (REL: Own res ⊢ |==> r R RR ps pt sti_src sti_tgt)
  .

  Definition ibot : rel := fun _ _ _ _ _ _ => False%I.

  Program Definition isim
          r g {R} (RR: Any.t * R-> Any.t * R -> iProp) ps pt
          (sti_src sti_tgt : Any.t * itree hAGEs R): iProp := 
    iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) (unlift r) (unlift g) _ RR ps pt sti_src sti_tgt) _.
    (* iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) (unlift r) (unlift g) _ RR ps pt sti_src sti_tgt) _. *)
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

  Lemma unlift_ibot:
    unlift ibot <7= bot7.
  Proof.
    unfold ibot. i. destruct PR.
    eapply Own_iProp in REL; eauto.
    rr in REL. uiprop in REL. des.
    rr in REL. uiprop in REL. eauto.
  Qed.

  Lemma isim_init
      r g ps pt {R} RR st_src st_tgt i_src i_tgt iP fmr
      (ENTAIL: bi_entails
                iP
                (@isim r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt)))
      (CUR: Own fmr ⊢ iP)
    :
      gpaco7 _hpsim (cpn7 _hpsim) (unlift r) (unlift g) R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr.
      (* gpaco7 _hpsim (cpn7 _hpsim) (unlift r) (unlift g) R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr. *)
  Proof.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    uiprop in ENTAIL. exploit ENTAIL; eauto using Own_iProp.
  Qed.
  
  (* GIL: Deleted the following because it is subsumed by [isim_wand]. *)
  
  (* Lemma isim_final *)
  (*     r g ps pt {R} RR st_src st_tgt i_src i_tgt (iP: iProp) *)
  (*     (SIM: forall fmr (IP: iP fmr),  *)
  (*         gpaco7 _hpsim (cpn7 _hpsim) r g R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr) *)
  (*         (* gpaco7 _hpsim (cpn7 _hpsim) (unlift r) (unlift g) R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr) *) *)
  (*   : *)
  (*     bi_entails *)
  (*       iP *)
  (*       (isim r g RR ps pt (st_src, i_src) (st_tgt, i_tgt)). *)
  (* Proof.  *)
  (*   uiprop. i. guclo hpsim_extendC_spec. econs; eauto. refl. *)
  (* Qed. *)

  Lemma unlift_mon r0 r1
    (MON: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@r0 R RR ps pt sti_src sti_tgt)
              (#=> @r1 R RR ps pt sti_src sti_tgt))
  :
    unlift r0 <7= unlift r1.
  Proof.
    i. destruct PR. econs; eauto.
    iIntros "H". iPoseProof (REL with "H") as "H".
    iMod "H". iPoseProof (MON with "H") as "H". eauto.
  Qed.

  Lemma isim_mono_knowledge 
    r0 g0 r1 g1 {R} RR ps pt sti_src sti_tgt
    (MON0: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@r0 R RR ps pt sti_src sti_tgt)
              (#=> @r1 R RR ps pt sti_src sti_tgt))
    (MON1: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@g0 R RR ps pt sti_src sti_tgt)
              (#=> @g1 R RR ps pt sti_src sti_tgt))
    :
    bi_entails
      (@isim r0 g0 R RR ps pt sti_src sti_tgt)
      (@isim r1 g1 R RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. 
    eapply gpaco7_mon; eauto using unlift_mon.
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

  Global Instance isim_elim_upd
    r g {R} RR ps pt sti_src sti_tgt
    P p
  :
    ElimModal True p false (#=> P) P 
    (@isim r g R RR ps pt sti_src sti_tgt) 
    (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply isim_upd. iMod "H0". iModIntro.
    iApply "H1". iFrame.
  Qed.

  (* GIL: Deleted the following because it is subsumed by [isim_wand]. *)
  (* Restored to use in wsim_bind_top *)
  Lemma isim_mono
    r g ps pt {R} RR0 RR1 sti_src sti_tgt
    (MONO: forall st_src st_tgt ret_src ret_tgt,
            (bi_entails (RR0 (st_src, ret_src) (st_tgt, ret_tgt)) (RR1 (st_src, ret_src) (st_tgt, ret_tgt))))
    :
      bi_entails
        (@isim r g R RR0 ps pt sti_src sti_tgt)
        (@isim r g R RR1 ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. destruct sti_src, sti_tgt.
    rewrite <-(bind_ret_r i). rewrite <-(bind_ret_r i0).
    guclo hpsim_bindC_spec. econs; eauto.
    i. gstep. econs. ii. esplits; eauto. econs; eauto.
    iIntros "H". iApply MONO. iStopProof. eauto.
  Qed.

  (* Try RR` -∗#=> RR *)
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

  Lemma isim_frame 
    r g {R} RR ps pt sti_src sti_tgt
    P
  :
    bi_entails
      (P ** @isim r g R RR ps pt sti_src sti_tgt)
      (isim r g (fun str_src str_tgt => P ** RR str_src str_tgt) ps pt sti_src sti_tgt).
  Proof.
    iIntros "[H0 H1]". iApply isim_wand. iFrame. eauto.
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


  (* Simulation rules *)
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
      ((Ist st_src st_tgt) ** (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -∗ @isim r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
      (isim r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    remember (∀ st_src0 st_tgt0 vret : Any.t, Ist st_src0 st_tgt0 -∗ isim r g RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret))%I as FR.
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
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. grind.
    pattern (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_src x).
    replace (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_src x) with (f varg >>= k_src); grind.
    rewrite <- bind_bind. f_equal. etrans.
    { instantiate (1:=  (`x : Any.t <- f varg;; Ret x)). grind. } 
    f_equal. extensionality x. grind.
  Qed.
  
  Lemma isim_inline_tgt
    r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@isim r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@isim r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    uiprop. i. guclo hpsimC_spec. econs; esplits; eauto. econs; eauto. grind.
    pattern (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_tgt x).
    replace (` r1 : Any.t <- f varg;; ` x : Any.t <- (Ret ();;; Ret r1);; k_tgt x) with (f varg >>= k_tgt); grind.
    rewrite <- bind_bind. f_equal. etrans.
    { instantiate (1:= (`x : Any.t <- f varg;; Ret x)). grind. }
    f_equal. extensionality x. grind. 
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
      (iP -∗ (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
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
      (iP -∗ (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
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
        (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
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
        (∀ x', ⌜x = Some x'⌝ -∗ isim r g RR ps pt (st_src, Ret x') (st_tgt, i_tgt))
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
      (∀ x', ⌜x = Some x'⌝ -∗ @isim r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
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
        (∀ x', ⌜x = Some x'⌝ -∗ isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, Ret x'))
        (isim (r, g, ps, pt) Frz RR (st_src, i_src) (st_tgt, unwrapN x)).
  Proof.
    erewrite (@idK_spec _ _ (unwrapN x)).
    iIntros "H". iApply isim_unwrapN_tgt.
    iIntros (x') "EQ". iApply "H"; auto.
  Qed. *)

  (* Definition isim_fsem isim_RR: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: Ist st_src st_tgt ε),
                ⊢ @isim bot7 bot7 Any.t isim_RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  Definition isim_fnsem isim_RR: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq (isim_fsem isim_RR). *)

  Lemma isim_base r g R (RR: Any.t * R -> Any.t * R -> iProp)
    ps pt sti_src sti_tgt
    :
    bi_entails
      (r R RR ps pt sti_src sti_tgt)
      (isim r g RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. gfinal. left. econs; eauto.  eapply iProp_Own in H.
    iIntros "H". iModIntro. iStopProof. eauto.
  Qed.

  Lemma isim_reset 
    r g {R} RR ps pt sti_src sti_tgt
  :
    bi_entails
      (@isim r g R RR false false sti_src sti_tgt)
      (@isim r g R RR ps pt sti_src sti_tgt).
  Proof.
    uiprop. i. eapply hpsim_flag_down. eauto. 
  Qed.

  Lemma isim_coind (r g: rel) A P RA RRA psA ptA srcA tgtA
    (COIND: forall (g0: rel) (a:A),
      bi_entails
        (P a
         ∗ □ (∀ R RR ps pt src tgt, g R RR ps pt src tgt -∗ g0 R RR ps pt src tgt)
         ∗ □ (∀ a, P a -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))
        (@isim r g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))
    :
    forall (a:A),
      bi_entails
        (P a)
        (@isim r g (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)).
  Proof.
    i. iIntros "H". iPoseProof (bupd_intro with "H") as "H". iStopProof.
    rr. autorewrite with iprop.
    revert_until COIND. gcofix CIH. i.
    uiprop in H0. des.
    guclo hpsim_updateC_spec. econs. ii. exists r2.
    esplits; cycle 1.
    { uiprop. i. exists r2. split; try refl.
      i. eapply H1. eapply URA.wf_extends; eauto. apply URA.extends_add; eauto. }
    clear r1 H1 H WF.
    guclo hpsim_updateC_spec. econs; ii; esplits; eauto.
    specialize (COIND
      (fun R RR ps pt src tgt =>
         g R RR ps pt src tgt ∨
         ∃ a, P a ∗ ⌜@existT Type (fun _ => _) R (RR,ps,pt,src,tgt) =
                      existT (RA a) (RRA a,psA a,ptA a,srcA a,tgtA a)⌝)%I a).
    rr in COIND. autorewrite with iprop in COIND.
    eapply gpaco7_mon. eapply COIND; eauto.
    - rr. autorewrite with iprop. exists r2, ε. r_solve.
      esplits; eauto. eapply Own_iProp, URA.wf_unit.
      iIntros "_"; iSplit.
      + iModIntro. iIntros (R RR ps pt src tgt) "H". iFrame.
      + iModIntro. iIntros (a0) "HP". iRight. iExists a0. iFrame. eauto.
    - eauto.
    - i. destruct PR. rr in REL. autorewrite with iprop in REL.
      exploit REL; eauto using Own_iProp. clear REL.
      intros REL. rr in REL. autorewrite with iprop in REL.
      des. rr in REL. autorewrite with iprop in REL. des.
      + eapply CIH0. econs; eauto.
        rr; i. uiprop. i. esplits; eauto.
        i. apply REL0. eapply URA.wf_extends, H2. eapply URA.extends_add; eauto.
      + repeat (rr in REL; autorewrite with iprop in REL; des). subst.
        rr in REL2. uiprop in REL2. depdes REL2.
        eapply CIH; eauto. uiprop. esplits; eauto.
        i. apply REL0 in H1. eapply URA.wf_mon with (b:=b).
        eapply eq_ind; eauto. r_solve.
  Qed.

End SIM.

Global Opaque isim.


Section wsim.
  Local Notation universe := positive.
  Local Notation level := nat.
  Context `{Σ: GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{Invs : @InvSet Σ}.
  (* Context `{COPSETRA : @GRA.inG CoPset.t Σ}. *)
  (* Context `{GSETRA : @GRA.inG Gset.t Σ}. *)
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{INVSETRA : @GRA.inG (OwnIsRA sProp) Σ}.

  Variable u: universe.
  Variable n: level.
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Let isim := @isim Σ Ist fl_src fl_tgt.
  (* Let rel := ∀ x : Type, (Any.t * x → Any.t * x → iProp) → bool → bool → Any.t * itree hAGEs x → Any.t * itree hAGEs x → Σ → Prop. *)

  (* Program Definition lift_rel (r: rel)  := 
    fun R (RR: Any.t * R-> Any.t * R -> iProp) ps pt sti_src sti_tgt => iProp_intro (r _ RR ps pt sti_src sti_tgt) _.
  Next Obligation.
  Admitted. *)

  (* Let RR {R}: Any.t * R -> Any.t * R -> iProp :=
     fun '(st_src, v_src) '(st_tgt, v_tgt) => (Ist st_src st_tgt ** ⌜v_src = v_tgt⌝)%I.  *)

  Definition wsim (ES : coPsets) 
    r g {R} (RR: Any.t * R -> Any.t * R -> iProp) 
    ps pt 
    '(st_src, i_src)
    '(st_tgt, i_tgt) 
  :=
    ((wsats u n ∗ OwnE_all u ES ∗ univ_rest)
            -∗
            (isim r g 
              (fun '(st_src, ret_src) '(st_tgt, ret_tgt) 
                => (wsats u n ∗ OwnE_all u ∅ ∗ univ_rest) ∗ RR (st_src, ret_src) (st_tgt, ret_tgt))
              ps pt (st_src, i_src) (st_tgt, i_tgt)))%I.

  (***** wsim lemmas ****)

  Lemma wsim_discard 
        Es E0 E1 r g {R} RR
        ps pt sti_src sti_tgt
        (TOP: E0 ⊆ E1)
    :
      (@wsim (<[n:=E0]>Es) r g R RR ps pt sti_src sti_tgt)
    -∗
      (wsim (<[n:=E1]>Es) r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H [W [E U]]". 
    iApply "H". iFrame. iPoseProof (OwnE_all_subset with "E") as "[E0 E1]"; [eapply TOP|]. iFrame.
  Qed.

  Lemma wsim_free_all
    Es r g {R} RR 
    ps pt sti_src sti_tgt
    (TOP: OwnE_top Es)
  :
    (@wsim ∅ r g R RR ps pt sti_src sti_tgt)
  -∗
    (wsim Es r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H [W [E R]]".
    iApply isim_upd. iMod (OwnE_free_all with "E") as "E"; eauto.
    iApply "H". iFrame; eauto.
  Qed.
(* 
  Lemma wsim_base 
    Es r g {R} RR RR'
    (REL: RR' = (λ '(st_src, ret_src) '(st_tgt, ret_tgt), (wsats u n ** (OwnE_all u ∅ ** univ_rest)) ** RR (st_src, ret_src) (st_tgt, ret_tgt)))
    ps pt sti_src sti_tgt
    (TOP: OwnE_top Es)
  :
    (@r R RR' ps pt sti_src sti_tgt)
  -∗
    (wsim Es r g RR ps pt sti_src sti_tgt).
  Proof.
    rewrite <- wsim_free_all; [|eassumption].
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H [W D]".
    iApply isim_base. rewrite REL. iFrame.
  Qed. *)
  
  Lemma wsim_upd
    E r g {R} ps pt sti_src sti_tgt
    (RR: Any.t * R -> Any.t * R -> iProp)
  :
    (#=> (wsim E r g RR ps pt sti_src sti_tgt))
  -∗
    wsim E r g RR ps pt sti_src sti_tgt.
  Proof.
    unfold wsim. destruct sti_src, sti_tgt.
    iIntros "H WD". iApply isim_upd. iMod "H". iModIntro.
    iApply "H"; eauto.
  Qed.

  
  (* Comment: Update modality diff??: RR -∗#=> RR' in fairness *)
  Lemma wsim_wand 
    Es r g {R} RR0 RR1 ps pt sti_src sti_tgt
  :
    (@wsim Es r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (∀ st_src ret_src st_tgt ret_tgt,
          ((RR0 (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR1 (st_src, ret_src) (st_tgt, ret_tgt))))
      -∗
        (wsim Es r g RR1 ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H R D".
    iApply isim_wand.
    iPoseProof ("H" with "D") as "H".
    iSplitR "H"; [|auto]. iIntros (? ? ? ?) "[D H]".
    iPoseProof ("R" $! _ _ with "H") as "H". iFrame.
  Qed.

  Lemma wsim_mono 
    Es r g {R} RR0 RR1 ps pt sti_src sti_tgt
    (MONO: forall st_src r_src st_tgt r_tgt,
              (RR0 (st_src, r_src) (st_tgt, r_tgt))
            -∗
              ((RR1 (st_src, r_src) (st_tgt, r_tgt))))
  :
    (@wsim Es r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (wsim Es r g RR1 ps pt sti_src sti_tgt).
  Proof.
    iIntros "H". iApply (wsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma wsim_frame 
    Es r g {R} RR ps pt sti_src sti_tgt
    P
  :
    (@wsim Es r g R RR ps pt sti_src sti_tgt)
  -∗
    (P -∗ (wsim Es r g (fun str_src str_tgt => P ∗ RR str_src str_tgt) ps pt sti_src sti_tgt))
  .
  Proof.
    iIntros "H0 H1". iApply (wsim_wand with "H0").
    iIntros. iFrame.
  Qed.

  Lemma wsim_bind_top 
    Es r g {R S} RR ps pt st_src st_tgt i_src i_tgt k_src k_tgt
  :
    (@wsim Es r g S (fun '(s_src, r_src) '(s_tgt, r_tgt) => wsim ∅ r g RR false false (s_src, k_src r_src) (s_tgt, k_tgt r_tgt)) ps pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (@wsim Es r g R RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H W".
    iPoseProof ("H" with "W") as "H".
    iApply isim_bind. iApply (isim_mono with "H").
    iIntros (? ? ? ?) "[W H]".
    iApply ("H" with "W"). 
  Qed.

  (****** FUpd Rules ******)


  Lemma wsim_FUpd
    Es0 Es1 r g {R} RR ps pt sti_src sti_tgt 
  :
    (FUpd u n emp Es0 Es1 (wsim Es1 r g RR ps pt sti_src sti_tgt))
  -∗
    (@wsim Es0 r g R RR ps pt sti_src sti_tgt).
  Proof.
    Local Transparent FUpd.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "F WD".
    iAssert (emp ** (wsats u n ∗ OwnE_all u Es0 ∗ univ_rest)) with "[WD]" as "C".
    { iFrame. }
    iApply isim_upd.
    unfold FUpd. 
    iMod ("F" with "C") as "[A [W [E [U SIM]]]]".
    iApply "SIM"; iFrame. eauto.
  Qed.

  Lemma wsim_FUpd_weaken 
    Es1 Es2 r g {R} RR ps pt sti_src sti_tgt
    (E0 E1: coPset)
    (SUB: E0 ⊆ E1)
  :
    (FUpd u n emp (<[n:=E0]> Es1) (<[n:=E0]> Es2) (@wsim (<[n:=E1]> Es2) r g R RR ps pt sti_src sti_tgt))
  -∗
    (wsim (<[n:=E1]> Es1) r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    iIntros "H". iApply wsim_FUpd. iApply FUpd_mask_mono; eauto. 
  Qed.

  Global Instance wsim_elim_FUpd_gen
         Es0 Es1 r g {R} RR
         (E0 E1 E2: coPset)
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E0 ⊆ E2) p false 
    (FUpd u n emp (<[n:=E0]>Es0) (<[n:=E1]>Es1) P) 
    P 
    (@wsim (<[n:=E2]>Es0) r g R RR ps pt sti_src sti_tgt) 
    (wsim (<[n:=(E1 ∪ (E2 ∖ E0))]>Es1) r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd. iMod "H0". iModIntro. iApply "H1". iFrame.
  Qed.

  Global Instance wsim_elim_FUpd_eq
         Es0 Es1 (E1 E2: coPset) r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E1 ⊆ E2) p false 
    (FUpd u n emp (<[n:=E1]>Es0) (<[n:=E1]>Es1) P) 
    P
    (@wsim (<[n:=E2]>Es0) r g R RR ps pt sti_src sti_tgt) 
    (wsim (<[n:=E2]>Es1) r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.
  
  Global Instance wsim_elim_FUpd
         Es0 Es1 r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal True p false 
    (FUpd u n emp Es0 Es1 P)
    P
    (@wsim Es0 r g R RR ps pt sti_src sti_tgt)
    (wsim Es1 r g RR ps pt sti_src sti_tgt).
  Proof.
  Admitted.
  (*Comment: Proved, but iModIntro takes too long. *)
    (* unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd.
    iMod "H0". instantiate (1:= Es1). iModIntro.
    iApply ("H1" with "H0").
  Qed. *)

  Global Instance wsim_add_modal_FUpd
         Es r g {R} RR
         ps pt sti_src sti_tgt
         P
    :
    AddModal (FUpd u n emp Es Es P) P (@wsim Es r g R RR ps pt sti_src sti_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]".
    iApply ("H1" with "H0").
  Qed.

  (**** Simulation Rules ****)

  Lemma wsim_ret
    Es r g {R} ps pt st_src st_tgt v_src v_tgt
    (RR: Any.t * R -> Any.t * R -> iProp)
    (TOP: OwnE_top Es) (* make lemma: OwnE_top ∅ *)
  :
    (RR (st_src, v_src) (st_tgt, v_tgt))
  -∗
    (@wsim Es r g R RR ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt)).
  Proof.
    iIntros "H". unfold wsim. iIntros "[W [E U]]".
    iApply isim_upd. iPoseProof (OwnE_free_all with "E") as "E"; eauto.
    iApply isim_ret. iFrame. eauto.
  Qed.

  Lemma wsim_call 
    Es r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg
  :
    ((Ist st_src st_tgt) ** (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -∗ @wsim Es r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗  
    (wsim Es r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "[IST H] WD". iApply isim_call. iFrame.
    iIntros (? ? ?) "IST". iPoseProof ("H" with "IST") as "H". iApply "H". eauto.
  Qed.  

  Lemma wsim_syscall
    Es r g {R} RR ps pt st_src st_tgt k_src k_tgt fn varg rvs
  :
    (∀ vret, @wsim Es r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
  -∗
    (wsim Es r g RR ps pt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_syscall. iIntros. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_inline_src
    Es r g ps pt {R} RR st_src st_tgt k_src i_tgt f fn varg 
    (FIND: alist_find fn fl_src = Some f)
  :
  bi_entails
    (@wsim Es r g R RR true pt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    (@wsim Es r g R RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_inline_src; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.
  
  Lemma wsim_inline_tgt
    Es r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@wsim Es r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    unfold wsim. iIntros "H D".
    iApply isim_inline_tgt; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_tau_src
    Es r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim Es r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim Es r g RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_src. iFrame.
  Qed.


  Lemma wsim_tau_tgt
    Es r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim Es r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_tgt. iFrame.
  Qed.

  Lemma wsim_choose_src 
    Es X x r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (@wsim Es r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim Es r g RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_choose_src. iFrame.
  Qed.

  Lemma wsim_choose_tgt 
    Es X r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (∀ x, @wsim Es r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_choose_tgt. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_src 
    Es X r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (∀ x, @wsim Es r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim Es r g RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_take_src. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_tgt 
    Es X x r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (@wsim Es r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_take_tgt. iFrame.
  Qed.
  
  Lemma wsim_supdate_src
    Es X r g {R} RR ps pt st_src st_tgt k_src i_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim Es r g R RR true pt ((run st_src).1, k_src (run st_src).2) (st_tgt, i_tgt))
  -∗
    (wsim Es r g RR ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_src. iFrame.
  Qed.

  Lemma wsim_supdate_tgt
    Es X r g {R} RR ps pt st_src st_tgt i_src k_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim Es r g R RR ps true (st_src, i_src) ((run st_tgt).1, k_tgt (run st_tgt).2))
  -∗
    (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_tgt. iFrame.
  Qed.

  Lemma wsim_assume_src
    Es r g {R} RR ps pt iP st_src st_tgt k_src i_tgt
  :
    (iP -∗ (@wsim Es r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
  -∗
    (@wsim Es r g R RR ps pt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H WD".
    iApply isim_assume_src. iIntros "IP".
    iPoseProof ("H" with "IP") as "H".
    iPoseProof ("H" with "WD") as "H". iFrame.
  Qed.

  Lemma wsim_assume_tgt
    Es r g {R} RR ps pt iP st_src st_tgt i_src k_tgt
  :
    (iP ∗ (@wsim Es r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
  -∗
    (@wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "[IP H] WD".
    iApply isim_assume_tgt. 
    iPoseProof ("H" with "WD") as "H". iFrame.
  Qed.

  Lemma wsim_guarantee_src
    Es r g {R} RR ps pt iP st_src st_tgt k_src i_tgt
  :
    (iP ∗ @wsim Es r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt))
  -∗
    (@wsim Es r g R RR ps pt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "[IP H] WD". 
    iApply isim_guarantee_src. 
    iPoseProof ("H" with "WD") as "H". iFrame.
  Qed.  
    
  Lemma wsim_guarantee_tgt
    Es r g {R} RR ps pt iP st_src st_tgt i_src k_tgt
  :
    (iP -∗ @wsim Es r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt))
  -∗
    (@wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H WD".
    iApply isim_guarantee_tgt. iIntros "IP".
    iPoseProof ("H" with "IP") as "H".
    iPoseProof ("H" with "WD") as "H". iFrame.
  Qed.  

  Lemma wsim_progress
    Es r g {R} RR sti_src sti_tgt
  :
    @wsim Es g g R RR false false sti_src sti_tgt
  -∗
    @wsim Es r g R RR true true sti_src sti_tgt.
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H WD".
    iApply isim_progress. iApply "H". eauto.
  Qed.

  (********)

  Lemma wsim_triggerUB_src
    Es r g {R} RR ps pt X st_src st_tgt (k_src: X -> _) i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim Es r g R RR ps pt (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    iIntros "H". unfold triggerUB. hred_l. iApply wsim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerUB_src_trigger
    Es r g {R} RR ps pt st_src st_tgt i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim Es r g R RR ps pt (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply wsim_triggerUB_src. auto.
  Qed.

  Lemma wsim_triggerNB_tgt
    Es r g {R} RR ps pt X st_src st_tgt i_src (k_tgt: X -> _)
  :
    bi_entails
      (⌜True⌝)
      (@wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply wsim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerNB_trigger
    Es r g {R} RR ps pt st_src st_tgt i_src
  :
    bi_entails
      (⌜True⌝)
      (@wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply wsim_triggerNB_tgt. auto.
  Qed.

  Lemma wsim_unwrapU_src
      Es r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -∗ wsim Es r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
        (@wsim Es r g R RR ps pt (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply wsim_triggerUB_src. auto. }
  Qed.

  Lemma wsim_unwrapN_src
    Es r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @wsim Es r g R RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (wsim Es r g RR ps pt (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma wsim_unwrapU_tgt
    Es r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma wsim_unwrapN_tgt
    Es r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -∗ @wsim Es r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim Es r g RR ps pt (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply wsim_triggerNB_tgt. auto. }
  Qed.

  (********)

  Definition wsim_fsem RR: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: Ist st_src st_tgt ε),
                ⊢ @isim ibot ibot Any.t RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  Definition wsim_fnsem RR: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq (wsim_fsem RR).


  (* Definition wsim_fsem Es RR: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: Ist st_src st_tgt ε),
                ⊢ @wsim Es bot7 bot7 Any.t RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  Definition wsim_fnsem Es RR: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq (wsim_fsem Es RR). *)


End wsim.

Global Opaque wsim.


Module HModSemPair.
Section WSIMMODSEM.
  Import HModSem.
  Local Notation universe := positive.
  Local Notation level := nat.

  Context `{Σ: GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{Invs : @InvSet Σ}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{INVSETRA : @GRA.inG (OwnIsRA sProp) Σ}.

  Variable (ms_src ms_tgt: HModSem.t).
  (* Variable u: universe. *)
  (* Variable n: level. *)
  Variable Ist: Any.t -> Any.t -> iProp.
  (* Variable RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp.  *)
  (* Variable Es: coPsets. *)


  Let fl_src := ms_src.(fnsems).
  Let fl_tgt := ms_tgt.(fnsems).
  Let init_src := ms_src.(initial_st).
  Let init_tgt := ms_tgt.(initial_st).
  Let cond_src := ms_src.(initial_cond).
  Let cond_tgt := ms_tgt.(initial_cond).

  Let RR {R}: Any.t * R -> Any.t * R -> iProp :=
     fun '(st_src, v_src) '(st_tgt, v_tgt) => (Ist st_src st_tgt ** ⌜v_src = v_tgt⌝)%I.   
 
  Inductive sim: Prop := mk {
    wsim_fnsems: Forall2 (wsim_fnsem Ist fl_src fl_tgt RR) fl_src fl_tgt;
    wsim_initial: cond_src ⊢ cond_tgt ∗ (isim (fun _ _ => ⌜True⌝%I) [] [] ibot ibot (fun '(_, v_src) '(_, v_tgt) => Ist v_src v_tgt) false false (tt↑, resum_itr init_src) (tt↑, resum_itr init_tgt))
    (* In initial itree, states are dummy and return values are initial states of main-itree. *)
  }.     
     
  (* Inductive sim: Prop := mk {
    wsim_fnsems: Forall2 (wsim_fnsem u n Ist fl_src fl_tgt Es RR) fl_src fl_tgt;
    wsim_initial: cond_src ⊢ cond_tgt ∗ (wsim 1 0 (fun _ _ => ⌜True⌝%I) [] [] ∅ bot7 bot7 (fun '(_, v_src) '(_, v_tgt) => Ist v_src v_tgt) false false (tt↑, resum_itr init_src) (tt↑, resum_itr init_tgt))
    (* In initial itree, states are dummy and return values are initial states of main-itree. *)
  }. *)

End WSIMMODSEM.
End HModSemPair.

Module HModPair.
Section WSIMMOD.
  Local Notation universe := positive.
  Local Notation level := nat.

  Context `{Σ: GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{Invs : @InvSet Σ}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{INVSETRA : @GRA.inG (OwnIsRA sProp) Σ}.

  Variable (md_src md_tgt: HMod.t).
  Variable Ist: Any.t -> Any.t -> iProp.
  (* Variable RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp. *)
  (* Variable Es: coPsets. *)
  (* Variable u: universe. *)
  (* Variable n: level. *)

  Inductive sim: Prop := mk {
    sim_modsem:
        forall sk (SKINCL: Sk.incl md_tgt.(HMod.sk) sk) (SKWF: Sk.wf sk),
        <<SIM: HModSemPair.sim (md_src.(HMod.get_modsem) sk) (md_tgt.(HMod.get_modsem) sk) Ist>>;
    sim_sk: <<SIM: md_src.(HMod.sk) = md_tgt.(HMod.sk)>>;
   }.

End WSIMMOD.
End HModPair.


(* Module IModSemPair.
Section ISIMMODSEM.
  Import HModSem.
  Context `{Σ: GRA.t}.
  Variable (ms_src ms_tgt: HModSem.t).
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable isim_RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp. (* Fix *)

  Let fl_src := ms_src.(fnsems).
  Let fl_tgt := ms_tgt.(fnsems).
  Let init_src := ms_src.(initial_st).
  Let init_tgt := ms_tgt.(initial_st).
  Let cond_src := ms_src.(initial_cond).
  Let cond_tgt := ms_tgt.(initial_cond).
  
  Inductive sim: Prop := mk {
    isim_fnsems: Forall2 (isim_fnsem Ist fl_src fl_tgt isim_RR) fl_src fl_tgt;
    isim_initial: cond_src ⊢ cond_tgt ∗ (isim Ist [] [] bot7 bot7 isim_RR false false (tt↑, resum_itr init_src) (tt↑, resum_itr init_tgt))
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
End IModPair. *)

(* Section TACTICS. *)


  (*** Simply switching isim -> wsim? ***)
  Ltac ired_l := try Red.prw ltac:(IRed._red_gen) 1 2 1 0.
  Ltac ired_r := try Red.prw ltac:(IRed._red_gen) 1 1 1 0.
  Ltac ired_both := ired_l; ired_r.
  Ltac prep := cbn; ired_both.

  Ltac force_l :=
    prep;
    match goal with
    | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
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
  | [ |- environments.envs_entails _ (@wsim _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
      idtac
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
      let name := fresh "G" in
      cut (P); [intros name; iApply wsim_assume_tgt; iSplitR; [iPureIntro; exact name|]|]; cycle 1
  end
.

Ltac iIntrosFresh H := iIntros H || iIntrosFresh (H ++ "'")%string.

Ltac step0 :=
  match goal with
  (** src **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply wsim_unwrapU_src; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
      iApply wsim_assume_src; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, tau;; _) (_, _)) ] =>
      iApply wsim_tau_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (SUpdate _) >>= _) (_, _)) ] =>
      iApply wsim_supdate_src
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Take _) >>= _) (_, _)) ] =>
      let name := fresh "y" in
      iApply wsim_take_src; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _  (_, trigger (Assume _) >>= _) (_, _)) ] =>
      iApply wsim_assume_src; iIntrosFresh "ASM"
  (* | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, trigger (Assume _);;; _) (_, _)) ] =>
      let name := fresh "y" in
      iApply wsim_assume_src; iIntros (name) *)

  (** tgt **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
      let name := fresh "y" in
      iApply wsim_unwrapN_tgt; iIntros (name) "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name; try rewrite name in *
      end
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
      iApply wsim_guarantee_tgt; iIntros "%";
      match goal with
      | [ H: _ |- _ ] => let name := fresh "G" in rename H into name
      end
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, tau;; _)) ] =>
      iApply wsim_tau_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (SUpdate _) >>= _)) ] =>
      iApply wsim_supdate_tgt
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Choose _) >>= _)) ] =>
      let name := fresh "y" in
      iApply wsim_choose_tgt; iIntros (name)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Guarantee _) >>= _)) ] =>
      iApply wsim_guarantee_tgt; iIntrosFresh "GRT"  
  (* | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Guarantee _);;; _)) ] =>
      let name := fresh "y" in
      iApply wsim_guarantee_tgt; iIntros (name)   *)
  (** call **)
  (* | [ |- environments.envs_entails _ (wsim  _ _ _ _ _ _ _ _ (_, trigger (Call ?x0 ?y0) >>= _)
                                           (_, trigger (Call ?x1 ?y1) >>= _)) ] =>
      iApply wsim_call *)

  (** ret **)
  | [ |- environments.envs_entails _ (wsim _ _ _ _ _ _ _ _ _ _ _ (_, Ret _) (_, Ret _)) ] =>
      iApply wsim_ret
  end.

  Ltac hcall := iApply wsim_call.
  Ltac inline_l := iApply wsim_inline_src.
  Ltac inline_r := iApply wsim_inline_tgt.

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
  Tactic Notation "steps!" := repeat (prep; try step0; try hcall; des_pairs).
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


  (* Section TEST. *)
    From iris.proofmode Require Import coq_tactics environments.

    Global Arguments Envs _ _%proof_scope _%proof_scope _.
    Global Arguments Enil {_}.
    Global Arguments Esnoc {_} _%proof_scope _%string _%I.
    
    Local Notation universe := positive.
    Local Notation level := nat.
  
    Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' Ist '------------------------------------------------------------------' st_src st_tgt '------------------------------------------------------------------'  itr_src itr_tgt"
    :=
      (environments.envs_entails (Envs E1 E2 _) (wsim _ _ Ist _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
      (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
        (at level 50,
         format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' Ist '//' '------------------------------------------------------------------' '//' st_src '//' st_tgt '//' '------------------------------------------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

    Notation "E1 '------------------------------------------------------------------□' Ist '------------------------------------------------------------------' st_src st_tgt '------------------------------------------------------------------'  itr_src itr_tgt"
    :=
      (environments.envs_entails (Envs E1 Enil _) (wsim _ _ Ist _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
      (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
        (at level 50,
         format "E1 '------------------------------------------------------------------□' '//' Ist '//' '------------------------------------------------------------------' '//' st_src '//' st_tgt '//' '------------------------------------------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

    Notation "E2 '------------------------------------------------------------------∗' Ist '------------------------------------------------------------------' st_src st_tgt '------------------------------------------------------------------'  itr_src itr_tgt"
    :=
      (environments.envs_entails (Envs Enil E2 _) (wsim _ _ Ist _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
      (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
        (at level 50,
         format "E2 '------------------------------------------------------------------∗' '//' Ist '//' '------------------------------------------------------------------' '//' st_src '//' st_tgt '//' '------------------------------------------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

    Notation "Ist '------------------------------------------------------------------' st_src st_tgt '------------------------------------------------------------------'  itr_src itr_tgt"
    :=
      (environments.envs_entails (Envs Enil Enil _) (wsim _ _ Ist _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
      (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
        (at level 50,
         format "Ist '//' '------------------------------------------------------------------' '//' st_src '//' st_tgt '//' '------------------------------------------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").
   


  Section TEST.      
    Context `{Σ: GRA.t}.
    Context `{sProp : level -> Type}.
    Context `{Invs : @InvSet Σ}.
    Context `{@IInvSet Σ sProp}.
    Context `{@GRA.inG OwnEsRA Σ}.
    Context `{@GRA.inG OwnDsRA Σ}.
    Context `{INVSETRA : @GRA.inG (OwnIsRA sProp) Σ}.

    Let Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
    Let RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.
    Variable iP: iProp.


    Goal ⊢ ((⌜False⌝**iP) -∗ wsim 1 0 Ist [] [] ∅ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
    Proof. iIntros "[#A B]". clarify. Qed.
    Goal ⌜False⌝%I ⊢ (wsim 1 0 Ist [] [] ∅ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
    Proof. iIntros "#H". Admitted.
    Goal ⊢ (iP -∗ wsim 1 0 Ist [] [] ∅ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
    Proof. iIntros "H". Admitted.
    Goal ⊢ (wsim 1 0 Ist [] [] ∅ ibot ibot RR false false (tt↑, trigger (Assume (⌜False⌝%I));;; Ret tt↑ >>= (fun r => Ret r)) (tt↑, Ret tt↑)).
    Proof. iIntros. steps. Admitted.



  End TEST.


  Section TEST.
    Import HModSem HMod.
    Local Notation universe := positive.
    Local Notation level := nat.
  
    Context `{Σ: GRA.t}.
    Context `{sProp : level -> Type}.
    Context `{Invs : @InvSet Σ}.
    Context `{@IInvSet Σ sProp}.
    Context `{@GRA.inG OwnEsRA Σ}.
    Context `{@GRA.inG OwnDsRA Σ}.
    Context `{INVSETRA : @GRA.inG (OwnIsRA sProp) Σ}.

    Definition mss0: HModSem.t := {|
      fnsems := [("f0", (fun _ => Ret tt↑))];
      initial_st := Ret tt↑;
      initial_cond := ⌜True⌝%I;
    |}.

    Definition mss1: HModSem.t := {|
      fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      initial_st := Ret tt↑;
      initial_cond := ⌜True⌝%I;
    |}.

    Definition mtt0: HModSem.t := {|
      fnsems := [("f0", (fun _ => Ret tt↑))];
      initial_st := Ret tt↑;
      initial_cond := ⌜True⌝%I;
    |}.

    Definition mtt1: HModSem.t := {|
      fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
      initial_st := Ret tt↑;
      initial_cond := ⌜True⌝%I;
    |}.

    Definition ms0 := {|
      get_modsem := fun _ => mss0;
      sk := Sk.unit;
    |}.

    Definition ms1 := {|
      get_modsem := fun _ => mss1;
      sk := Sk.unit;
    |}.

    Definition mt0 := {|
      get_modsem := fun _ => mtt0;
      sk := Sk.unit;
    |}.

    Definition mt1 := {|
      get_modsem := fun _ => mtt1;
      sk := Sk.unit;
    |}.

    Definition Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
    Definition RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.

    Goal HModPair.sim (HMod.add ms0 ms1) (HMod.add mt0 mt1) Ist.
    Proof.
      (* econs; ss.
      ii. econs. 
      { econs.
        { econs; ss.  
          grind. iIntros. 
          (* Set Printing All.  *)
          steps!; eauto.
          admit.
        }
        econs.
        { econs; ss. grind.
          iIntros. steps!; et. 
          admit.
        }
        econs; ss. econs; ss. grind.
        iIntros. steps!. iSplitL; et. iIntros.
        steps. inline_l; et. inline_r; et. steps; eauto.
        admit.
      }
      ss. iIntros.
      iSplitL; eauto.
      rewrite ! resum_itr_bind.
      rewrite ! resum_itr_ret. steps; eauto.
      admit. *)
    Admitted.
    (* Qed. *)


  End TEST.

