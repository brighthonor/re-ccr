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
Require Import World sWorld.

From stdpp Require Import coPset gmap.
(* Require Import FancyUpdate. *)


Set Implicit Arguments.


Require Import Red.
Require Import IRed.

Ltac hred_l := try (prw _red_gen 1 2 1 0).
Ltac hred_r := try (prw _red_gen 1 1 1 0).
Ltac hred := try (prw _red_gen 1 1 0).



Section SPEC.
  Context `{_W: CtxWD.t}.

  (* Definition mk_fspec_inv {X: Type} (DPQ: X -> ord * (Any.t -> iProp) * (Any.t -> iProp)): fspec :=
    mk_fspec (fst ∘ fst ∘ DPQ)
             (fun x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∧ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∧ ⌜z = a⌝)%I)
  . *)

  Inductive meta_inv {X: positive -> nat -> Type} : Type :=
  | mk_meta (u: positive) (n: nat) (x: X u n).  

  Definition mk_fspec_inv (k: nat) (fsp: positive -> nat -> fspec): fspec :=
    @mk_fspec
      Σ
      (@meta_inv (fun u n => (fsp u n).(meta)))
      (fun '(mk_meta u n x) => (fsp u n).(measure) x)
      (fun '(mk_meta u n x) varg_src varg_tgt =>
         closed_world u (k+n) ⊤ ∗ (fsp u n).(precond) x varg_src varg_tgt)%I
      (fun '(mk_meta u n x) vret_src vret_tgt =>
         closed_world u (k+n) ⊤ ∗ (fsp u n).(postcond) x vret_src vret_tgt)%I.

  Definition fspec_trivial: fspec :=
    @mk_fspec 
      _
      (@meta_inv (fun _ _ => unit)) 
      (fun _ => ord_top) 
      (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
      (fun _ reth retl => (⌜reth = retl⌝: iProp)%I).


End SPEC.

(*** Move ***)
(* Section SPEC.
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

End SPEC. *)

(* Don't want variable stb, o in isim *)
Section SIM.

  Context `{Σ: GRA.t}.
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Let _hpsim := @_hpsim Σ fl_src fl_tgt Ist false.
  Let rel := ∀ R : Type, (Any.t * R → Any.t * R → iProp) → bool → bool → Any.t * itree hAGEs R → Any.t * itree hAGEs R → iProp.

  (**** COMMENT: If using (_ -> iProp) for r, g: need a replacement of 'bot7' in wsim_fsem. ****)

  (* Definition unlift (r: rel) := fun R RR ps pt sti_src sti_tgt res => r R RR ps pt sti_src sti_tgt res. *)

  Variant iunlift (r: rel) R RR ps pt sti_src sti_tgt res: Prop :=
    | unlift_intro
        (WF: URA.wf res)
        (REL: Own res ⊢ |==> r R RR ps pt sti_src sti_tgt)
  .

  Definition ibot : rel := fun _ _ _ _ _ _ => False%I.

  Program Definition isim
          r g {R} (RR: Any.t * R-> Any.t * R -> iProp) ps pt
          (sti_src sti_tgt : Any.t * itree hAGEs R): iProp := 
    iProp_intro (gpaco7 (_hpsim) (cpn7 _hpsim) (iunlift r) (iunlift g) _ RR ps pt sti_src sti_tgt) _.
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

  Lemma iunlift_ibot:
    iunlift ibot <7= bot7.
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
      gpaco7 _hpsim (cpn7 _hpsim) (iunlift r) (iunlift g) R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr.
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

  Lemma iunlift_mon r0 r1
    (MON: forall R RR ps pt sti_src sti_tgt,
            bi_entails
              (@r0 R RR ps pt sti_src sti_tgt)
              (#=> @r1 R RR ps pt sti_src sti_tgt))
  :
    iunlift r0 <7= iunlift r1.
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
    eapply gpaco7_mon; eauto using iunlift_mon.
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
            ((RR' (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR (st_src, ret_src) (st_tgt, ret_tgt)))) ∗ (@isim r g R RR' ps pt sti_src sti_tgt))
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
      (P ∗ @isim r g R RR ps pt sti_src sti_tgt)
      (isim r g (fun str_src str_tgt => P ∗ RR str_src str_tgt) ps pt sti_src sti_tgt)%I.
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
      ((Ist st_src st_tgt) ∗ (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -∗ @isim r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
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
      (iP ∗ (@isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
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
      (iP ∗ (@isim r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
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
        ((□ ((∀ R RR ps pt src tgt, g R RR ps pt src tgt -∗ g0 R RR ps pt src tgt) ∗
             (∀ a, P a -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))) ∗
         P a)
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
    - rr. autorewrite with iprop. exists ε, r2. r_solve.
      esplits; eauto. eapply Own_iProp, URA.wf_unit.
      iIntros "_". iModIntro. iSplitL "".
      + iIntros (R RR ps pt src tgt) "H". iFrame.
      + iIntros (a0) "HP". iRight. iExists a0. iFrame. eauto.
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

Section WSIM.
  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{CtxWD.t}.

  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Let isim := isim Ist fl_src fl_tgt.

  Variable u: world_id.
  Variable b: level.

  Definition wsim (E : coPset) 
    r g {R} (RR: Any.t * R -> Any.t * R -> iProp) ps pt src tgt
  :=
    (world u b E -∗ isim r g RR ps pt src tgt)%I.

  Definition wclosed u b (P: iProp) : iProp := P ∗ closed_world u b ⊤.

  (***** wsim lemmas ****)

  Lemma wsim_discard 
        E0 E1 r g {R} RR
        ps pt sti_src sti_tgt
        (TOP: E0 ⊆ E1)
    :
      (@wsim E0 r g R RR ps pt sti_src sti_tgt)
    -∗
      (wsim E1 r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. 
    Local Transparent world. 
    iIntros "H [W [E U]]". 
    iApply "H". iFrame. iPoseProof (OwnE_subset with "E") as "[E0 E1]"; [eapply TOP|]. iFrame.
  Qed.

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
    E r g {R} RR0 RR1 ps pt sti_src sti_tgt
  :
    (@wsim E r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (∀ st_src ret_src st_tgt ret_tgt,
          ((RR0 (st_src, ret_src) (st_tgt, ret_tgt)) -∗ (RR1 (st_src, ret_src) (st_tgt, ret_tgt))))
      -∗
        (wsim E r g RR1 ps pt sti_src sti_tgt)
  .
  Proof.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "H R D".
    iApply isim_wand.
    iPoseProof ("H" with "D") as "H".
    iSplitR "H"; [|auto]. iIntros (? ? ? ?) "H".
    iPoseProof ("R" $! _ _ with "H") as "H". iFrame.
  Qed.

  Lemma wsim_mono 
    E r g {R} RR0 RR1 ps pt sti_src sti_tgt
    (MONO: forall st_src r_src st_tgt r_tgt,
              (RR0 (st_src, r_src) (st_tgt, r_tgt))
            -∗
              ((RR1 (st_src, r_src) (st_tgt, r_tgt))))
  :
    (@wsim E r g R RR0 ps pt sti_src sti_tgt)
  -∗
    (wsim E r g RR1 ps pt sti_src sti_tgt).
  Proof.
    iIntros "H". iApply (wsim_wand with "H").
    iIntros. iApply MONO. auto.
  Qed.

  Lemma wsim_frame 
    E r g {R} RR ps pt sti_src sti_tgt
    P
  :
    (@wsim E r g R RR ps pt sti_src sti_tgt)
  -∗
    (P -∗ (wsim E r g (fun str_src str_tgt => P ∗ RR str_src str_tgt) ps pt sti_src sti_tgt))
  .
  Proof.
    iIntros "H0 H1". iApply (wsim_wand with "H0").
    iIntros. iFrame.
  Qed.

  Lemma wsim_bind_top
    E r g {R S} RR ps pt st_src st_tgt i_src i_tgt k_src k_tgt
  :
    (@wsim E r g S (fun '(s_src, r_src) '(s_tgt, r_tgt) => isim r g RR false false (s_src, k_src r_src) (s_tgt, k_tgt r_tgt)) ps pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (@wsim E r g R RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt)).
  Proof.
    iIntros "H W". iPoseProof ("H" with "W") as "H".
    iApply isim_bind. iApply (isim_mono with "H"). eauto.
  Qed.

  (****** FUpd Rules ******)

  Lemma wsim_FUpd
    E0 E1 r g {R} RR ps pt sti_src sti_tgt 
  :
    (FUpd u b emp E0 E1 (wsim E1 r g RR ps pt sti_src sti_tgt))
  -∗
    (@wsim E0 r g R RR ps pt sti_src sti_tgt).
  Proof.
    Local Transparent FUpd.
    unfold wsim. destruct sti_src, sti_tgt. iIntros "F WD".
    iAssert (emp ∗ world u b E0)%I with "[WD]" as "WD". { iFrame. }
    iApply isim_upd.
    iMod ("F" with "WD") as "(_ & W & SIM)".
    iApply "SIM"; iFrame. eauto.
  Qed.

  Lemma wsim_FUpd_weaken 
    r g {R} RR ps pt sti_src sti_tgt
    (E0 E1: coPset)
    (SUB: E0 ⊆ E1)
  :
    (FUpd u b emp E0 E0 (@wsim E1 r g R RR ps pt sti_src sti_tgt))
  -∗
    (wsim E1 r g RR ps pt sti_src sti_tgt)
  .
  Proof.
    iIntros "H". iApply wsim_FUpd. iApply FUpd_mask_mono; eauto. 
  Qed.

  Global Instance wsim_elim_FUpd_gen
         r g {R} RR
         (E0 E1 E2: coPset)
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E0 ⊆ E2) p false 
    (FUpd u b emp E0 E1 P) 
    P 
    (@wsim E2 r g R RR ps pt sti_src sti_tgt) 
    (wsim (E1 ∪ (E2 ∖ E0)) r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd. iMod "H0". iModIntro. iApply "H1". iFrame.
  Qed.

  Global Instance wsim_elim_FUpd_eq
         (E1 E2: coPset) r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal (E1 ⊆ E2) p false 
    (FUpd u b emp E1 E1 P) 
    P
    (@wsim E2 r g R RR ps pt sti_src sti_tgt) 
    (wsim E2 r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "[H0 H1]".
    iApply wsim_FUpd_weaken.
    { eauto. }
    iMod "H0". iModIntro. iApply ("H1" with "H0").
  Qed.

  Global Instance wsim_elim_FUpd
         E0 E1 r g {R} RR
         ps pt sti_src sti_tgt p
         P
    :
    ElimModal True p false 
    (FUpd u b emp E0 E1 P)
    P
    (@wsim E0 r g R RR ps pt sti_src sti_tgt)
    (wsim E1 r g RR ps pt sti_src sti_tgt).
  Proof.
    unfold ElimModal. rewrite bi.intuitionistically_if_elim.
    i. iIntros "(H0 & H1)".
    iApply wsim_FUpd. instantiate (1:= E1).
    iMod "H0". iApply FUpd_intro. iModIntro. (* iModIntro doesn't work. why? *)
    iApply "H1". eauto.
  Qed.
  
  Global Instance wsim_add_modal_FUpd
         E r g {R} RR
         ps pt sti_src sti_tgt
         P
    :
    AddModal (FUpd u b emp E E P) P (@wsim E r g R RR ps pt sti_src sti_tgt).
  Proof.
    unfold AddModal. iIntros "[> H0 H1]".
    iApply ("H1" with "H0").
  Qed.

  (**** Simulation Rules ****)

  Lemma wsim_ret
    r g {R} ps pt st_src st_tgt v_src v_tgt
    (RR: Any.t * R -> Any.t * R -> iProp)
  :
    (RR (st_src, v_src) (st_tgt, v_tgt))
  -∗
    (@wsim ⊤ r g R RR ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt)).
  Proof.
    iIntros "H". unfold wsim. iIntros "[W [E U]]".
    iApply isim_upd. iApply isim_ret. iFrame. eauto.
  Qed.

  Lemma wsim_call 
    E r g ps pt {R} RR st_src st_tgt k_src k_tgt fn varg
  :
    ((Ist st_src st_tgt) ∗ (∀ st_src0 st_tgt0 vret, (Ist st_src0 st_tgt0) -∗ @wsim E r g R RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret)))
  -∗  
    (wsim E r g RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "[IST H] WD". iApply isim_call. iFrame.
    iIntros (? ? ?) "IST". iPoseProof ("H" with "IST") as "H". iApply "H". eauto.
  Qed.  

  Lemma wsim_syscall
    E r g {R} RR ps pt st_src st_tgt k_src k_tgt fn varg rvs
  :
    (∀ vret, @wsim E r g R RR true true (st_src, k_src vret) (st_tgt, k_tgt vret))
  -∗
    (wsim E r g RR ps pt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_syscall. iIntros. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_inline_src
    E r g ps pt {R} RR st_src st_tgt k_src i_tgt f fn varg 
    (FIND: alist_find fn fl_src = Some f)
  :
  bi_entails
    (@wsim E r g R RR true pt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    (@wsim E r g R RR ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_inline_src; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.
  
  Lemma wsim_inline_tgt
    E r g ps pt {R} RR st_src st_tgt i_src k_tgt f fn varg
    (FIND: alist_find fn fl_tgt = Some f)
  :
    bi_entails
      (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)).
  Proof. 
    unfold wsim. iIntros "H D".
    iApply isim_inline_tgt; eauto. 
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_tau_src
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim E r g R RR true pt (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, tau;; i_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_src. iFrame.
  Qed.


  Lemma wsim_tau_tgt
    E r g {R} RR ps pt st_src st_tgt i_src i_tgt
  :
    (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, tau;; i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_tau_tgt. iFrame.
  Qed.

  Lemma wsim_choose_src 
    E X x r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (@wsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim E r g RR ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_choose_src. iFrame.
  Qed.

  Lemma wsim_choose_tgt 
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (∀ x, @wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_choose_tgt. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_src 
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (∀ x, @wsim E r g R RR true pt (st_src, k_src x) (st_tgt, i_tgt))
  -∗ (* same as bi_entails *)
    (wsim E r g RR ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iApply isim_take_src. iIntros.
    iPoseProof ("H" with "D") as "H". iFrame.
  Qed.

  Lemma wsim_take_tgt 
    E X x r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt x))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D".
    iPoseProof ("H" with "D") as "H".
    iApply isim_take_tgt. iFrame.
  Qed.
  
  Lemma wsim_supdate_src
    E X r g {R} RR ps pt st_src st_tgt k_src i_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim E r g R RR true pt ((run st_src).1, k_src (run st_src).2) (st_tgt, i_tgt))
  -∗
    (wsim E r g RR ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_src. iFrame.
  Qed.

  Lemma wsim_supdate_tgt
    E X r g {R} RR ps pt st_src st_tgt i_src k_tgt
    (run: Any.t -> Any.t * X)
    (* (RUN: run st_src = (st_src0, x)) *)
  :
    (@wsim E r g R RR ps true (st_src, i_src) ((run st_tgt).1, k_tgt (run st_tgt).2))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)).
  Proof.
    unfold wsim. iIntros "H D". 
    iPoseProof ("H" with "D") as "H".
    iApply isim_supdate_tgt. iFrame.
  Qed.

  Lemma wsim_assume_src
    P r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (P ∗ free_worlds u b -∗ (@wsim ⊤ r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt)))
  -∗
    (isim r g RR ps pt (st_src, trigger (Assume (wclosed u b P)) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iApply isim_assume_src. iIntros "(P & (F & W))".
    iPoseProof ("H" with "[P F]") as "H". iFrame.
    iApply "H". eauto.
  Qed.

  Lemma wsim_guarantee_src
    P r g {R} RR ps pt st_src st_tgt k_src i_tgt
  :
    (P ∗ free_worlds u b ∗ @isim r g R RR true pt (st_src, k_src tt) (st_tgt, i_tgt))
  -∗
    (wsim ⊤ r g RR ps pt (st_src, trigger (Guarantee (wclosed u b P)) >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "(P & F & H) WD". iApply isim_guarantee_src. iFrame.
  Qed.  
  
  Lemma wsim_assume_tgt
    P u0 b0 E r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (wclosed u0 b0 P ∗ (@wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt)))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Assume (wclosed u0 b0 P)) >>= k_tgt)).
  Proof.
    iIntros "(P & H) WD". iApply isim_assume_tgt. iFrame.
    iApply "H". eauto.
  Qed.

  Lemma wsim_guarantee_tgt
    P u0 b0 E r g {R} RR ps pt st_src st_tgt i_src k_tgt
  :
    (wclosed u0 b0 P -∗ @wsim E r g R RR ps true (st_src, i_src) (st_tgt, k_tgt tt))
  -∗
    (wsim E r g RR ps pt (st_src, i_src) (st_tgt, trigger (Guarantee (wclosed u0 b0 P)) >>= k_tgt)).
  Proof.
    iIntros "H WD". iApply isim_guarantee_tgt. iIntros "IP".
    iPoseProof ("H" with "IP") as "H". iApply "H". eauto.
  Qed.  

  Lemma wsim_progress
    E r g {R} RR sti_src sti_tgt
  :
    @wsim E g g R RR false false sti_src sti_tgt
  -∗
    @wsim E r g R RR true true sti_src sti_tgt.
  Proof.
    destruct sti_src, sti_tgt. iIntros "H WD".
    iApply isim_progress. iApply "H". eauto.
  Qed.

  Lemma wsim_base E r g R (RR: Any.t * R -> Any.t * R -> iProp)
    ps pt sti_src sti_tgt
    :
    bi_entails
      (world u b E -∗ r R RR ps pt sti_src sti_tgt)
      (wsim E r g RR ps pt sti_src sti_tgt).
  Proof.
    iIntros "H W". iApply isim_base. iApply "H". eauto.
  Qed.

  Lemma wsim_reset 
    E r g {R} RR ps pt sti_src sti_tgt
  :
    bi_entails
      (@wsim E r g R RR false false sti_src sti_tgt)
      (@wsim E r g R RR ps pt sti_src sti_tgt).
  Proof.
    iIntros "H W". iApply isim_reset. iApply "H". eauto.
  Qed.

  Lemma wsim_coind E r g A P RA RRA psA ptA srcA tgtA
    (COIND: forall g0 (a:A),
      bi_entails
        ((□ ((∀ R RR ps pt src tgt, g R RR ps pt src tgt -∗ g0 R RR ps pt src tgt) ∗
             (∀ a, P a ∗ world u b E -∗ g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))) ∗
         P a)
        (@wsim E r g0 (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)))
    :
    forall (a:A),
      bi_entails
        (P a)
        (@wsim E r g (RA a) (RRA a) (psA a) (ptA a) (srcA a) (tgtA a)).
  Proof.
    i. iIntros "P W". iApply (isim_coind _ (fun a => P a ∗ world u b E)%I); i.
    - iIntros "(H & P & W)". iRevert "W". iApply COIND. eauto.
    - iFrame.
  Qed.

  (********)

  Lemma wsim_triggerUB_src
    E r g {R} RR ps pt X st_src st_tgt (k_src: X -> _) i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, triggerUB >>= k_src) (st_tgt, i_tgt)).
  Proof. 
    iIntros "H". unfold triggerUB. hred_l. iApply wsim_take_src.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerUB_src_trigger
    E r g {R} RR ps pt st_src st_tgt i_tgt
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, triggerUB) (st_tgt, i_tgt)).
  Proof.
    erewrite (@idK_spec _ _ (triggerUB)).
    iIntros "H". iApply wsim_triggerUB_src. auto.
  Qed.

  Lemma wsim_triggerNB_tgt
    E r g {R} RR ps pt X st_src st_tgt i_src (k_tgt: X -> _)
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB >>= k_tgt)).
  Proof.
    iIntros "H". unfold triggerNB. hred_r. iApply wsim_choose_tgt.
    iIntros (x). destruct x.
  Qed.

  Lemma wsim_triggerNB_trigger
    E r g {R} RR ps pt st_src st_tgt i_src
  :
    bi_entails
      (⌜True⌝)
      (@wsim E r g R RR ps pt (st_src, i_src) (st_tgt, triggerNB)).
  Proof.
    erewrite (@idK_spec _ _ (triggerNB)).
    iIntros "H". iApply wsim_triggerNB_tgt. auto.
  Qed.

  Lemma wsim_unwrapU_src
      E r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
    :
      bi_entails
        (∀ x', ⌜x = Some x'⌝ -∗ wsim E r g RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
        (@wsim E r g R RR ps pt (st_src, unwrapU x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". unfold unwrapU. destruct x.
    { hred_l. iApply "H". auto. }
    { iApply wsim_triggerUB_src. auto. }
  Qed.

  Lemma wsim_unwrapN_src
    E r g {R} RR ps pt st_src st_tgt X (x: option X) k_src i_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @wsim E r g R RR ps pt (st_src, k_src x') (st_tgt, i_tgt))
      (wsim E r g RR ps pt (st_src, unwrapN x >>= k_src) (st_tgt, i_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]".
    subst. hred_l. iApply "H".
  Qed.

  Lemma wsim_unwrapU_tgt
    E r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∃ x', ⌜x = Some x'⌝ ∧ @wsim E r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim E r g RR ps pt (st_src, i_src) (st_tgt, unwrapU x >>= k_tgt)).
  Proof.
    iIntros "H". iDestruct "H" as (x') "[% H]". subst.
    hred_r. iApply "H".
  Qed.

  Lemma wsim_unwrapN_tgt
    E r g {R} RR ps pt st_src st_tgt X (x: option X) i_src k_tgt
  :
    bi_entails
      (∀ x', ⌜x = Some x'⌝ -∗ @wsim E r g R RR ps pt (st_src, i_src) (st_tgt, k_tgt x'))
      (wsim E r g RR ps pt (st_src, i_src) (st_tgt, unwrapN x >>= k_tgt)).
  Proof.
    iIntros "H". unfold unwrapN. destruct x.
    { hred_r. iApply "H". auto. }
    { iApply wsim_triggerNB_tgt. auto. }
  Qed.

  (********)

  Definition isim_fsem RR: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt,
             Ist st_src st_tgt ⊢ @isim ibot ibot Any.t RR false false (st_src, itr_src) (st_tgt, itr_tgt)))%signature.

  Definition isim_fnsem RR: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq (isim_fsem RR).

End WSIM.

Section WSIM_LEVEL_UP.

  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{CtxWD.t}.
  
  Variable Ist: Any.t -> Any.t -> iProp.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).

  Let wsim u b := wsim Ist fl_src fl_tgt u b.

  Lemma wsim_level_up u b b' E r g R RR ps pt src tgt
      (LE: b <= b'):
    (free_worlds u b' -∗ @wsim u b' E r g R RR ps pt src tgt)
    -∗
    (free_worlds u b -∗ @wsim u b E r g R RR ps pt src tgt).
  Proof.
    iIntros "H FA W".
    iPoseProof (closed_world_mon with "[FA W]") as "[FA' W']"; eauto.
    - iFrame.
    - iPoseProof ("H" with "FA'") as "H". iApply "H". eauto.
  Qed.

End WSIM_LEVEL_UP.

Global Opaque wsim.

Module HModSemPair.
Section WSIMMODSEM.
  Import HModSem.
  Local Notation world_id := positive.
  Local Notation level := nat.

  (* Context `{_W: CtxWD.t}. *)

  Context `{Σ: GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.

  Variable (ms_src ms_tgt: HModSem.t).
  Variable Ist: Any.t -> Any.t -> iProp.

  Let fl_src := ms_src.(fnsems).
  Let fl_tgt := ms_tgt.(fnsems).
  Let init_src := ms_src.(initial_st).
  Let init_tgt := ms_tgt.(initial_st).
  Let cond_src := ms_src.(initial_cond).
  Let cond_tgt := ms_tgt.(initial_cond).

  Let RR {R}: Any.t * R -> Any.t * R -> iProp :=
     fun '(st_src, v_src) '(st_tgt, v_tgt) => (Ist st_src st_tgt ∗ ⌜v_src = v_tgt⌝)%I.   
 
  Inductive sim: Prop := mk {
    isim_fnsems: Forall2 (isim_fnsem Ist fl_src fl_tgt RR) fl_src fl_tgt;
    isim_initial: cond_src ⊢ cond_tgt ∗ (Ist init_src init_tgt);
    (* isim_initial: cond_src ⊢ cond_tgt ∗ (isim (fun _ _ => ⌜True⌝%I) [] [] ibot ibot (fun '(_, v_src) '(_, v_tgt) => Ist v_src v_tgt) false false (tt↑, resum_itr init_src) (tt↑, resum_itr init_tgt)) *)
    (* In initial itree, states are dummy and return values are initial states of main-itree. *)
  }.     
     
End WSIMMODSEM.
End HModSemPair.

Module HModPair.
Section WSIMMOD.
  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{Σ: GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.

  Variable (md_src md_tgt: HMod.t).
  Variable Ist: Any.t -> Any.t -> iProp.
  (* Variable RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp. *)
  (* Variable Es: coPsets. *)
  (* Variable u: world_id. *)
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
    isim_initial: cond_src ⊢ #=> (cond_tgt ∗ (isim Ist [] [] bot7 bot7 isim_RR false false (tt↑, resum_itr init_src) (tt↑, resum_itr init_tgt)))
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
