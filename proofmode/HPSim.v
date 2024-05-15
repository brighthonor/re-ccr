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

Require Import HTactics.





  Lemma URA_wf_extends_add `{Σ: GRA.t} (r r' c: Σ)
    (EXT : URA.extends r r')
    (WF : URA.wf (r' ⋅ c))
    :
    URA.wf (r ⋅ c).
  Proof.
    eapply URA.wf_extends; eauto.
    eapply URA.extends_add. eauto.
  Qed.

  Lemma URA_extends_refl `{Σ: GRA.t} (r: Σ):
    URA.extends r r.
  Proof. refl. Qed.




  


Section HPSIM.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Variable Ist: Any.t -> Any.t -> iProp.

  Definition hsupd (P: Σ -> Prop) : Σ -> Prop :=
    fun fmr => URA.wf fmr ->
               exists fmr0, P fmr0 /\
               (Own fmr ⊢ #=> Own fmr0).
               (* forall ctx (WF: URA.wf (fmr ⋅ ctx)), URA.wf (fmr0 ⋅ ctx). *)

  Definition dummy_term (with_dummy: bool) : itree hAGEs unit :=
    if with_dummy then trigger (Guarantee True) else Ret tt.
  
  Variant _hpsim' {with_dummy: bool}
    (hpsimc: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    {R} {RR: Any.t * R -> Any.t * R -> iProp} (hpsimi: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    : bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsim_ret
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)      
      (HPSIM_RET: True)
      ps pt st_src st_tgt fmr
      v_src v_tgt
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsim_call
      (HPSIM_CALL: True)
      ps pt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (Ist st_src st_tgt ** FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
                 (* (WF: URA.wf fmr0) *)
                 (INV: Own fmr0 ⊢ #=> (Ist st_src0 st_tgt0 ** FR)),
          hpsimi true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | hpsim_syscall
      (HPSIM_SYSCALL: True)
      ps pt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
    hpsimi true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsim_inline_src
      (HPSIM_INLINE_SRC: True)
      ps pt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: hpsimi true pt (st_src, f varg >>= (fun x => dummy_term with_dummy;;; Ret x) >>= k_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_inline_tgt
      (HPSIM_INLINE_TGT: True)
      ps pt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: hpsimi ps true (st_src, i_src) (st_tgt, f varg >>= (fun x => dummy_term with_dummy;;; Ret x) >>= k_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_tau_src
      (HPSIM_TAU_SRC: True)
      ps pt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsimi true pt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsim_tau_tgt
      (HPSIM_TAU_TGT: True)
      ps pt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsimi ps true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsim_take_src
      (HPSIM_TAKE_SRC: True)
      ps pt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), hpsimi true pt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr
            
  | hpsim_choose_tgt
      (HPSIM_CHOOSE_TGT: True)
      ps pt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), hpsimi ps true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsim_choose_src
      (HPSIM_CHOOSE_SRC: True)
      ps pt st_src st_tgt fmr
      X x k_src i_tgt
      (K: hpsimi true pt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_take_tgt
      (HPSIM_TAKE_TGT: True)
      ps pt st_src st_tgt fmr
      X x i_src k_tgt
      (K: hpsimi ps true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsim_supdate_src
      (HPSIM_SUPDATE_SRC: True)
      ps pt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: hpsimi true pt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_supdate_tgt
      (HPSIM_SUPDATE_TGT: True)
      ps pt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: hpsimi ps true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsim_assume_src
      (HPSIM_ASSUME_SRC: True)
      ps pt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (* (WF: URA.wf fmr0) *) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsimi true pt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_guarantee_tgt
      (HPSIM_GUARANTEE_TGT: True)
      ps pt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (* (WF: URA.wf fmr0) *) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsimi ps true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
            
  | hpsim_guarantee_src
      (HPSIM_GUARANTEE_SRC: True)
      ps pt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (* (WF: URA.wf fmr0) *) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsimi true pt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_assume_tgt
      (HPSIM_ASSUME_TGT: True)
      ps pt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (* (WF: URA.wf fmr0) *) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsimi ps true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim' hpsimc hpsimi ps pt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsim_progress
      (HPSIM_PROGRESS: True)
      sti_src sti_tgt fmr
      (SIM: hpsimc R RR false false sti_src sti_tgt fmr)
    :
    _hpsim' hpsimc hpsimi true true sti_src sti_tgt fmr
  .
  Arguments _hpsim' {with_dummy} hpsimc {R} RR hpsimi.

  Inductive _hpsim {with_dummy} hpsim R RR ps pt sti_src sti_tgt fmr : Prop
    :=
  | hpsim_intro (IN: hsupd (@_hpsim' with_dummy hpsim R RR (@_hpsim with_dummy hpsim R RR) ps pt sti_src sti_tgt) fmr) 
  .

  Definition hpsim {R} RR := paco7 (@_hpsim false) bot7 R RR.

  Lemma _hpsim_tarski with_dummy hpsim R RR rel
    (FIX: forall ps pt sti_src sti_tgt fmr
            (IN: hsupd (@_hpsim' with_dummy hpsim R RR rel ps pt sti_src sti_tgt) fmr),
          rel ps pt sti_src sti_tgt fmr)
    :
    @_hpsim with_dummy hpsim R RR <5= rel.
  Proof.
    fix self 6. i.
    destruct PR. apply FIX.
    ii. specialize (IN H). rr in IN. des.
    destruct IN; try by esplits; eauto using @_hpsim' with paco.
  Qed.

  Lemma hsupd_mon P Q r
    (IN: hsupd P r)             
    (LE: P <1= Q)
    :
    hsupd Q r.
  Proof.
    unfold hsupd in *; i. specialize (IN H).
    des. esplits; eauto.
  Qed.

  Lemma _hpsim'_mon with_dummy r r' R RR s s'
    ps pt sti_src sti_tgt fmr
    (REL: @_hpsim' with_dummy r R RR s ps pt sti_src sti_tgt fmr)
    (LEr: r <7= r')
    (LEs: s <5= s')
    :
    @_hpsim' with_dummy r' R RR s' ps pt sti_src sti_tgt fmr.
  Proof.
    ii. destruct REL; des; esplits; eauto; econs; esplits; eauto.
  Qed.
  
  Lemma _hpsim_mon with_dummy: monotone7 (@_hpsim with_dummy).
  Proof.
    ii. eapply _hpsim_tarski, IN.
    i. econs. eauto using hsupd_mon, _hpsim'_mon.
  Qed.

  Lemma _hpsim_mon_auto with_dummy r r' R RR
    ps pt sti_src sti_tgt fmr
    (REL: @_hpsim with_dummy r R RR ps pt sti_src sti_tgt fmr)
    (LEr: r <7= r')
    :
    @_hpsim with_dummy r' R RR ps pt sti_src sti_tgt fmr.
  Proof. eapply _hpsim_mon; eauto. Qed.

  Hint Constructors _hpsim' _hpsim.
  Hint Unfold hpsim.
  Hint Resolve _hpsim_mon: paco.
  Hint Resolve hsupd_mon _hpsim'_mon _hpsim_mon_auto: paco.
  Hint Resolve cpn7_wcompat: paco.

  Definition hpsim_tail : Any.t*Any.t -> Any.t*Any.t -> iProp :=
    fun '(st_src, v_src) '(st_tgt, v_tgt) => Ist st_src st_tgt ** ⌜v_src = v_tgt⌝.

  Definition hpsim_body := @hpsim Any.t hpsim_tail.

  Definition hpsim_fun (i_src: itree hAGEs Any.t) (i_tgt: itree hAGEs Any.t):  Prop :=
    forall st_src st_tgt fmr (* (WF: URA.wf fmr) *)
           (INV: Own fmr ⊢ #=>Ist st_src st_tgt),
      hpsim_body false false (st_src, i_src) (st_tgt, i_tgt) fmr.

  Lemma case_itrH R (itrH: itree hAGEs R) :
    (exists v, itrH = Ret v) \/
    (exists itrH', itrH = tau;; itrH') \/
    (exists P itrH', itrH = (trigger (Assume P);;; itrH')) \/
    (exists P itrH', itrH = (trigger (Guarantee P);;; itrH')) \/
    (exists R (c: callE R) ktrH', itrH = (trigger c >>= ktrH')) \/
    (exists R (s: sE R) ktrH', itrH = (trigger s >>= ktrH')) \/
    (exists R (e: eventE R) ktrH', itrH = (trigger e >>= ktrH')).
  Proof.
    ides itrH; eauto.
    right; right.
    destruct e; [destruct h|destruct e; [|destruct s]].
    - left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - right; left. exists P, (k()). unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. destruct x. rewrite bind_ret_l. eauto.
    - do 2 right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 3 right; left. exists X, s, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - do 4 right. exists X, e, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  Qed.  

  Lemma hsupd_incl P
    :
    P <1= hsupd P.
  Proof.
    unfold hsupd; i. esplits; eauto.
  Qed.
  
  Lemma hsupd_merge P r
    (REL: hsupd (hsupd P) r)
    :
    hsupd P r.
  Proof.
    unfold hsupd in *. i. specialize (REL H). des.
    exploit REL; eauto using own_wf.
    i. des. esplits; eauto with imodL.
  Qed.

  Lemma hsupd_update P r r'
    (IN: hsupd P r)
    (UPD: Own r' ⊢ #=> Own r)
    :
    hsupd P r'.
  Proof.
    ii. exploit IN; eauto using own_wf.
    i; des. esplits; eauto with imodL.
  Qed.

  Lemma hsupd_extends P r r'
    (IN: hsupd P r)
    (UPD: URA.extends r r')
    :
    hsupd P r'.
  Proof.
    eapply hsupd_update; eauto.
    eapply Own_extends in UPD.
    iIntros "H". iApply UPD. eauto.
  Qed.

  Lemma hsupd_wf P r
    (IN: URA.wf r -> hsupd P r)
    :
    hsupd P r.
  Proof.
    ii. eapply IN; eauto.
  Qed.  

  Lemma _hpsim_flag_mon with_dummy r R RR (ps pt ps' pt': bool) st_src st_tgt fmr
    (SIM: @_hpsim with_dummy r R RR ps pt st_src st_tgt fmr)
    (LES: ps -> ps')
    (LET: pt -> pt')
    :
    @_hpsim with_dummy r R RR ps' pt' st_src st_tgt fmr.
  Proof.
    move SIM before r. revert_until SIM.
    pattern ps, pt, st_src, st_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs.
    ii. specialize (IN H). des. destruct IN;
      try by esplits; eauto; try by econs; esplits; eauto.
    hexploit LES; eauto; i. hexploit LET; eauto; i.
    destruct ps', pt'; try discriminate. 
    econs; esplits; eauto.
  Qed.

  Lemma hpsim_flag_mon R RR (ps pt ps' pt': bool) st_src st_tgt fmr
    (SIM: @hpsim R RR ps pt st_src st_tgt fmr)
    (LES: ps -> ps')
    (LET: pt -> pt')
    :
    hpsim RR ps' pt' st_src st_tgt fmr.
  Proof.
    move SIM before RR. revert_until SIM. pcofix CIH. i.
    pstep. eapply _hpsim_flag_mon; eauto.
    eapply paco7_mon_bot in SIM; eauto. punfold SIM.
  Qed.

  Lemma hpsim_progress_flag with_dummy R RR r g st_src st_tgt fmr
    (SIM: gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) g g R RR false false st_src st_tgt fmr)
    :
    gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR true true st_src st_tgt fmr.
  Proof.
    gstep. econs. r; esplits; eauto.
  Qed.


  
  Definition hpsimC with_dummy hpsim R RR ps pt sti_src sti_tgt fmr :=
    hsupd (@_hpsim' with_dummy hpsim R RR (hpsim R RR) ps pt sti_src sti_tgt) fmr.
  
  Lemma hpsimC_mon with_dummy : monotone7 (@hpsimC with_dummy).
  Proof.
    ii. specialize (IN H). des.
    destruct IN; econs; esplits; eauto; try by esplits; eauto.
  Qed.

  Lemma hpsimC_spec with_dummy:
    (@hpsimC with_dummy) <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto using hpsimC_mon; i.
    econs. ii. destruct PR; eauto. des. esplits; eauto.
    eapply _hpsim'_mon; eauto using rclo7, _hpsim_mon_auto; i.
  Qed.

  Variant hpsim_flagC 
    (r: forall (R: Type) (RR: Any.t * R -> Any.t * R -> iProp),  bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    R RR ps1 pt1 st_src st_tgt fmr : Prop :=
  | hpsim_flagC_intro
    ps0 pt0
    (SIM: r R RR ps0 pt0 st_src st_tgt fmr)
    (SRC: ps0 = true -> ps1 = true)
    (TGT: pt0 = true -> pt1 = true)
  .

  Lemma hpsim_flagC_mon r1 r2 (LE: r1 <7= r2) :
    @hpsim_flagC r1 <7= @hpsim_flagC r2.
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve hpsim_flagC_mon: paco.
  
  Lemma hpsim_flagC_spec with_dummy:
    hpsim_flagC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eauto using _hpsim_flag_mon, _hpsim_mon_auto, rclo7.
  Qed.

  Lemma hpsim_flag_down with_dummy R RR r g ps pt st_src st_tgt fmr
    (SIM: gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR false false st_src st_tgt fmr)
    :
    gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR ps pt st_src st_tgt fmr.
  Proof. 
    guclo hpsim_flagC_spec. econs; et. 
  Qed.





  
  


  Variant hpsim_bindC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_bindC_intro
      ps pt Q QQ st_src st_tgt i_src i_tgt fmr
      (SIM: r Q QQ ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)

      R RR k_src k_tgt
      (SIMK: forall st_src0 st_tgt0 vret_src vret_tgt fmr0
               (* (WF: URA.wf fmr0) *)
               (RET: Own fmr0 ⊢ #=> QQ (st_src0, vret_src) (st_tgt0, vret_tgt)),
             r R RR false false (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt) fmr0)
    :
    hpsim_bindC r R RR ps pt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt) fmr
  .

  Lemma hpsim_bindC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_bindC r1 <7= hpsim_bindC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma hpsim_bindC_wrespectful with_dummy:
    wrespectful7 (@_hpsim with_dummy) hpsim_bindC.
  Proof.
    econs; eauto using hpsim_bindC_mon; i.
    destruct PR. apply GF in SIM.
    remember (st_src, i_src) as sti_src. remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before GF. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. econs. apply hsupd_merge.
    econs; esplits; eauto. specialize (IN H). des. subst.
    depdes IN; grind;
      try (by rr; i; esplits; eauto with paco);
      try (by do 2 (econs; esplits; eauto with paco);
              repeat rewrite <-bind_bind;
              eauto 10 using rclo7, hpsim_bindC).

    assert (URA.wf fmr1); eauto using own_wf.
    exploit SIMK; eauto.
    i. apply GF in x0.
    eapply (_hpsim_flag_mon _ _ _ _ _ _ ps0 pt0) in x0; try by i; clarify.

    destruct x0. eapply hsupd_update in IN; eauto.
    eapply _hpsim_mon_auto; eauto using rclo7.
  Qed.

  Lemma hpsim_bindC_spec with_dummy:
    hpsim_bindC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco.
    apply hpsim_bindC_wrespectful.
  Qed.







  Variant hpsim_extendC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_extendC_intro
      ps pt R RR sti_src sti_tgt fmr fmr'
      (SIM: r R RR ps pt sti_src sti_tgt fmr)
      (EXT: URA.extends fmr fmr')
     :
    hpsim_extendC r R RR ps pt sti_src sti_tgt fmr'
  .

  Lemma hpsim_extendC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_extendC r1 <7= hpsim_extendC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.


  
  Lemma hpsim_extendC_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_extendC.
  Proof.
    econs; eauto using hpsim_extendC_mon.
    intros. destruct PR. destruct SIM. econs.
    eapply hsupd_extends; eauto.
    eapply _hpsim_mon_auto; eauto.
    i. econs; eauto; refl.
  Qed.
  
  Lemma hpsim_extendC_spec with_dummy:
    hpsim_extendC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_extendC_compatible.
    eapply hpsim_extendC_mon, PR; eauto with paco.
  Qed.


  



  Variant hpsim_wfC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_wfC_intro
      ps pt R RR sti_src sti_tgt fmr
      (SIM: URA.wf fmr -> r R RR ps pt sti_src sti_tgt fmr)
     :
    hpsim_wfC r R RR ps pt sti_src sti_tgt fmr
  .

  Lemma hpsim_wfC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_wfC r1 <7= hpsim_wfC r2
  .
  Proof.
    ii. destruct PR. econs; eauto using hsupd_mon.
  Qed.

  Lemma hpsim_wfC_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_wfC.
  Proof.
    econs; eauto using hpsim_wfC_mon.
    i. destruct PR. econs. eapply hsupd_wf. i.
    eapply _hpsim_mon_auto; eauto 10 using hpsim_wfC, hsupd_incl with paco.
  Qed.
  
  Lemma hpsim_wfC_spec with_dummy:
    hpsim_wfC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_wfC_compatible.
    eapply hpsim_wfC_mon, PR; eauto with paco.
  Qed.



  

  Variant hpsim_updateC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_updateC_intro
      ps pt R RR sti_src sti_tgt fmr
      (SIM: hsupd (r R RR ps pt sti_src sti_tgt) fmr)
     :
    hpsim_updateC r R RR ps pt sti_src sti_tgt fmr
  .

  Lemma hpsim_updateC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_updateC r1 <7= hpsim_updateC r2
  .
  Proof.
    ii. destruct PR. econs; eauto using hsupd_mon.
  Qed.

  Lemma hpsim_updateC_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_updateC.
  Proof.
    econs; eauto using hpsim_updateC_mon.
    i. destruct PR. econs. eapply hsupd_merge.
    eapply hsupd_mon; eauto.
    i. destruct PR.
    eauto 10 using hpsim_updateC, hsupd_incl with paco.
  Qed.
  
  Lemma hpsim_updateC_spec with_dummy:
    hpsim_updateC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_updateC_compatible.
    eapply hpsim_updateC_mon, PR; eauto with paco.
  Qed.
  


  Variant hpsim_frameC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_frameC_intro
      ps pt R RR sti_src sti_tgt fmr fmrc (CTX: iProp)
      (SIM: r R (fun s t => CTX -* RR s t) ps pt sti_src sti_tgt fmr)
      (UPD: Own fmrc ⊢ #=> (Own fmr ** CTX))
     :
    hpsim_frameC r R RR ps pt sti_src sti_tgt fmrc
  .

  Lemma hpsim_frameC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_frameC r1 <7= hpsim_frameC r2
  .
  Proof.
    ii. destruct PR. econs; eauto using hsupd_mon.
  Qed.
  
  Lemma hpsim_frameC_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_frameC.
  Proof.
    econs; eauto using hpsim_frameC_mon. i.
    destruct PR. move SIM before r. revert_until SIM.
    pattern ps, pt, sti_src, sti_tgt, fmr.
    eapply _hpsim_tarski, SIM. i. econs.
    econs; esplits; eauto.
    exploit IN.
    { eapply own_wf in H; eauto.
      iIntros "H". iPoseProof (UPD with "H") as "[H _]". eauto. }
    i. des.
    assert (Own fmrc ⊢ #=> (Own fmr1 ** CTX)).
    { iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[F C]".
      iFrame. iApply x1. eauto. }
    
    depdes x0; grind; try by econs; eauto.
    - econs; eauto.
      iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[HO HC]".
      iPoseProof (x1 with "HO") as "HO". iMod "HO".
      iPoseProof (RET with "HO") as "HO". iMod "HO".
      iApply "HO". eauto.
    - econs; eauto.
      + instantiate (1:= FR ** CTX).
        iIntros "H". iPoseProof (UPD with "H") as "H". iMod "H" as "[H HCTX]".
        iFrame. iPoseProof (x1 with "H") as "H". iMod "H".
        iPoseProof (INV with "H") as "H". eauto.
      + i. econs. apply hsupd_merge. ii. esplits; eauto.
        exploit iProp_sepconj_upd; eauto. i; des.
        exploit iProp_sepconj; eauto; i; des; subst.
        { eapply URA.wf_mon. rewrite URA.add_comm. eauto using own_wf. }
        apply iProp_Own in x5. apply iProp_Own in x6.
        eapply K.
        { instantiate (1:= rp ⋅ p).
          iIntros "H". iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
          - iApply x2. eauto.
          - iApply x5. eauto.
        }
        { iIntros "H".
          iPoseProof (x0 with "H") as "H". iMod "H" as "[Hr [Hp Hq]]".
          iSplitR "Hq". 
          { iSplitR "Hp"; eauto. }
          { iApply x6. eauto. }
        }
    - econs; eauto. i.
      econs. apply hsupd_merge. ii. esplits; eauto.
      exploit iProp_sepconj_upd; eauto. i; des.
      exploit iProp_sepconj; eauto; i; des; subst.
      { eapply URA.wf_mon. rewrite URA.add_comm. eauto using own_wf. }
      apply iProp_Own in x5. apply iProp_Own in x6.
      eapply K.
      { instantiate (1:= rp ⋅ fmr1).
        iIntros "H". iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
        - iApply x2. eauto.
        - iApply CUR. eauto.
      }
      { iIntros "H".
        iPoseProof (x0 with "H") as "H". iMod "H" as "[Hr [Hp Hq]]".
        iSplitR "Hq". 
        { iSplitR "Hp"; eauto. iApply x5; eauto. }
        { iApply x6. eauto. }
      }
    - econs; eauto. i.
      econs. apply hsupd_merge. ii. esplits; eauto.
      exploit iProp_sepconj_upd; eauto. i; des.
      exploit iProp_sepconj; eauto; i; des; subst.
      { eapply URA.wf_mon. rewrite URA.add_comm. eauto using own_wf. }
      apply iProp_Own in x5. apply iProp_Own in x6.
      eapply K.
      { instantiate (1:= rp ⋅ fmr1).
        iIntros "H". iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
        - iApply x2. eauto.
        - iApply CUR. eauto.
      }
      { iIntros "H".
        iPoseProof (x0 with "H") as "H". iMod "H" as "[Hr [Hp Hq]]".
        iSplitR "Hq". 
        { iSplitR "Hp"; eauto. iApply x5; eauto. }
        { iApply x6. eauto. }
      }
    - econs; eauto.
      { instantiate (1:= FMR ** CTX).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. eapply iProp_sepconj_upd in NEW. des.
      eapply K; eauto.
      { iIntros "H". iApply NEW0. eauto. }
      { iIntros "H". iPoseProof (NEW with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iApply NEW1. eauto. }
    - econs; eauto.
      { instantiate (1:= FMR ** CTX).
        iIntros "H". iPoseProof (H0 with "H") as "H". iMod "H" as "[F C]".
        iFrame. iStopProof; eauto. }
      i. eapply iProp_sepconj_upd in NEW. des.
      eapply K; eauto.
      { iIntros "H". iApply NEW0. eauto. }
      { iIntros "H". iPoseProof (NEW with "H") as "H". iMod "H" as "[HP HQ]".
        iFrame. iApply NEW1. eauto. }
    - eauto using hpsim_frameC with paco.
  Qed.
  
  Lemma hpsim_frameC_spec with_dummy:
    hpsim_frameC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_frameC_compatible.
    eapply hpsim_frameC_mon, PR; eauto with paco.
  Qed.






  
  

  Definition hpsim_fsem: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: Ist st_src st_tgt ε),
                hpsim_body false false (st_src, itr_src) (st_tgt, itr_tgt) ε))%signature.

  Definition hpsim_fnsem: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq hpsim_fsem.

  (* Arguments _hpsim {with_dummy} hpsim {R} RR.

  Definition hpsim {R} RR := paco7 (@_hpsim false) bot7 R RR.

  Definition hpsim_tail : Any.t*Any.t -> Any.t*Any.t -> iProp :=
    fun '(st_src, v_src) '(st_tgt, v_tgt) => I st_src st_tgt ** ⌜v_src = v_tgt⌝. *)

End HPSIM.

Hint Resolve _hpsim_mon: paco.
Hint Resolve cpn7_wcompat: paco.

(**********)

(* TODO: move *)




Lemma hpsim_refl {Σ: GRA.t} fl:
  forall src tgt fmr (WF: URA.wf fmr) (EQST: Own fmr ⊢ ⌜src = tgt⌝%I),
  hpsim_body fl fl (fun src tgt => ⌜src = tgt⌝%I) false false src tgt fmr.
Proof.
  ginit. gcofix CIH. i.
  assert (src = tgt); subst.
  { rr in EQST. uiprop in EQST. rr in EQST. uiprop in EQST.
    eapply EQST; try refl; eauto. }

  destruct tgt as [st itr].
  gstep. econs. econs. assert (CASE := case_itrH _ itr); des; subst;
    try by repeat (econs; eauto with paco).
  - esplits; eauto. destruct c; econs; eauto.
    { instantiate (1:= Own fmr). eauto. }
    i. do 2 econs; esplits; eauto.
    assert (st_src0 = st_tgt0); subst.
    { uipropall. exploit INV; i; des; try refl; eauto. rr in x2. uipropall.
    }
    econs; eauto with paco.
  - depdes s; destruct (run st) eqn: EQ.
    repeat (econs; eauto with paco).
  - depdes e; repeat (econs; eauto with paco).
Qed.








Module HModSemPair.
Section HPSIMMODSEM.

  Context `{Σ: GRA.t}.

  Variable (ms_src ms_tgt: HModSem.t).
  
  Definition fl_src := ms_src.(HModSem.fnsems).
  Definition fl_tgt := ms_tgt.(HModSem.fnsems).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    I: Any.t -> Any.t -> iProp;
    hpsim_fnsems: Forall2 (hpsim_fnsem fl_src fl_tgt I) ms_src.(HModSem.fnsems) ms_tgt.(HModSem.fnsems);
    hpsim_initial: I (ms_src.(HModSem.initial_st)) (ms_tgt.(HModSem.initial_st)) ε;
    (* sim_fnsems: Forall2 (sim_fnsem wf le fl_src fl_tgt) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems); *)
    (* sim_initial: exists w_init, wf w_init (ms_src.(HModSem.initial_st), ms_tgt.(HModSem.initial_st)); *)
  }.

End HPSIMMODSEM.

Lemma self_sim {Σ: GRA.t} (ms: HModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=(fun src tgt => ⌜src = tgt⌝%I)). (* fun p => fst p = snd p *)
    generalize (HModSem.fnsems ms).
    induction a; ii; ss.
    econs; et. econs; ss. ii; clarify.
    rr in INV. uipropall. clarify.
    eapply hpsim_refl; eauto.
    apply URA.wf_unit.
  - rr. uipropall.
Qed.

End HModSemPair.


Module HModPair.
Section HPSIMMOD.
  Context `{Σ: GRA.t}.

   Variable (md_src md_tgt: HMod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(HMod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: HModSemPair.sim (md_src.(HMod.get_modsem) sk) (md_tgt.(HMod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(HMod.sk) = md_tgt.(HMod.sk)>>;
   }.

End HPSIMMOD.
End HModPair.


