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

Section HPSIM.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Variable I: Any.t -> Any.t -> iProp.

  Inductive _hpsim {with_dummy: bool}
    (hpsim: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsim_ret
      (HPSIM_RET: True)
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
    _hpsim hpsim p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsim_call
      (HPSIM_CALL: True)
      p_src p_tgt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
                 (WF: URA.wf fmr0)
                 (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
    _hpsim hpsim true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | hpsim_syscall
      (HPSIM_SYSCALL: True)
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
    _hpsim hpsim true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsim_inline_src
      (HPSIM_INLINE_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: _hpsim hpsim true p_tgt (st_src, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_src x) else k_src)) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_inline_tgt
      (HPSIM_INLINE_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_tgt x) else k_tgt)) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_tau_src
      (HPSIM_TAU_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: _hpsim hpsim true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsim_tau_tgt
      (HPSIM_TAU_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsim_choose_src
      (HPSIM_CHOOSE_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      X x k_src i_tgt
      (K: _hpsim hpsim true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_choose_tgt
      (HPSIM_CHOOSE_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsim_take_src
      (HPSIM_TAKE_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), _hpsim hpsim true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_take_tgt
      (HPSIM_TAKE_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      X x i_src k_tgt
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsim_supdate_src
      (HPSIM_SUPDATE_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: _hpsim hpsim true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_supdate_tgt
      (HPSIM_SUPDATE_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsim_assume_src
      (HPSIM_ASSUME_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_assume_tgt
      (HPSIM_ASSUME_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsim_guarantee_src
      (HPSIM_GUARANTEE_SRC: True)
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_guarantee_tgt
      (HPSIM_GUARANTEE_TGT: True)
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr

  | hpsim_progress
      (HPSIM_PROGRESS: True)
      st_src st_tgt fmr
      i_src i_tgt
      (SIM: hpsim R RR false false (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim true true (st_src, i_src) (st_tgt, i_tgt) fmr
  .
  Arguments _hpsim {with_dummy} hpsim {R} RR.

  Definition hpsim {R} RR := paco7 (@_hpsim false) bot7 R RR.

  Lemma _hpsim_mon with_dummy: monotone7 (@_hpsim with_dummy).
  Proof. 
    ii. induction IN;
      try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _hpsim.
  Hint Unfold hpsim.
  Hint Resolve _hpsim_mon: paco.
  Hint Resolve cpn7_wcompat: paco.

  Definition hpsim_end : Any.t*Any.t -> Any.t*Any.t -> iProp :=
    fun '(st_src, v_src) '(st_tgt, v_tgt) => I st_src st_tgt ** ⌜v_src = v_tgt⌝.

  Definition hpsim_body := @hpsim Any.t hpsim_end.
  
  Lemma _hpsim_mon_progress r R RR (p_src p_tgt p_src' p_tgt': bool) st_src st_tgt fmr
    (SIM: @_hpsim false r R RR p_src p_tgt st_src st_tgt fmr)
    (LES: p_src -> p_src')
    (LET: p_tgt -> p_tgt')
    :
    @_hpsim false r R RR p_src' p_tgt' st_src st_tgt fmr.
  Proof.
    move SIM before RR. revert_until SIM.
    induction SIM; i; eauto with paco.
    pclearbot. hexploit LES; eauto; i. hexploit LET; eauto; i.
    destruct p_src', p_tgt'; clarify. eauto with paco.
  Qed.

  Lemma hpsim_mon_progress R RR (p_src p_tgt p_src' p_tgt': bool) st_src st_tgt fmr
    (SIM: @hpsim R RR p_src p_tgt st_src st_tgt fmr)
    (LES: p_src -> p_src')
    (LET: p_tgt -> p_tgt')
    :
    hpsim RR p_src' p_tgt' st_src st_tgt fmr.
  Proof.
    move SIM before RR. revert_until SIM. pcofix CIH. i.
    pstep. eapply _hpsim_mon_progress; eauto.
    eapply paco7_mon_bot in SIM; eauto. punfold SIM.
  Qed.

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



  
  
  Variant hpsimC {with_dummy: bool}
  (hpsim: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
  {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsimC_ret
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
      hpsimC hpsim p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsimC_call
      p_src p_tgt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
          (WF: URA.wf fmr0)
          (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
          hpsim _ RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | hpsimC_syscall
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
          hpsim _ RR true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsimC_inline_src
      p_src p_tgt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: hpsim _ RR true p_tgt (st_src, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_src x) else k_src)) (st_tgt, i_tgt) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_inline_tgt
      p_src p_tgt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_tgt x) else k_tgt)) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsimC_tau_src
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsimC_tau_tgt
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsimC_choose_src
      p_src p_tgt st_src st_tgt fmr
      X x k_src i_tgt
      (K: hpsim _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
       hpsimC hpsim p_src p_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_choose_tgt
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsimC_take_src
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), hpsim _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_take_tgt
      p_src p_tgt st_src st_tgt fmr
      X x i_src k_tgt
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsimC_supdate_src
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: hpsim _ RR true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_supdate_tgt
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsimC_assume_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsim _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_assume_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
      hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsimC_guarantee_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsim _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsimC hpsim p_src p_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_guarantee_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    hpsimC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr

  | hpsimC_progress
      st_src st_tgt fmr
      i_src i_tgt
      (SIM: hpsim R RR false false (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    hpsimC hpsim true true (st_src, i_src) (st_tgt, i_tgt) fmr
  .
  Arguments _hpsim {with_dummy} hpsim {R} RR.
                
  Hint Constructors hpsimC: paco.
  
  Lemma hpsimC_mon with_dummy : monotone7 (@hpsimC with_dummy).
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.

  Lemma hpsimC_spec with_dummy:
    (@hpsimC with_dummy) <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto using hpsimC_mon; i.
    inv PR; econs; et; try (i; eapply _hpsim_mon; eauto using rclo7).
    econs. eauto.
  Qed.
  
  Lemma hpsim_progress_flag with_dummy R RR r g st_src st_tgt fmr
        (SIM: gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) g g R RR false false st_src st_tgt fmr)
      :
        gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR true true st_src st_tgt fmr.
  Proof.
    gstep. destruct st_src, st_tgt. econs; et.
  Qed.

  Lemma hpsim_flag_mon with_dummy
        (hpsim: forall (R: Type) (RR: Any.t * R -> Any.t * R -> iProp),  bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
        R (RR: Any.t * R -> Any.t * R -> iProp)
        p_src0 p_tgt0 p_src1 p_tgt1 st_src st_tgt fmr
        (SIM: (@_hpsim with_dummy) hpsim _ RR p_src0 p_tgt0 st_src st_tgt fmr)
        (SRC: p_src0 = true -> p_src1 = true)
        (TGT: p_tgt0 = true -> p_tgt1 = true)
    :
        (@_hpsim with_dummy) hpsim _ RR p_src1 p_tgt1 st_src st_tgt fmr.
  Proof.
    revert p_src1 p_tgt1 SRC TGT.
    induction SIM; i; clarify; et.
    exploit SRC; et. exploit TGT; et. i. clarify. econs; et.
  Qed.              

  Variant hpsim_flagC 
    (r: forall (R: Type) (RR: Any.t * R -> Any.t * R -> iProp),  bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    {R} (RR: Any.t * R -> Any.t * R -> iProp): bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop := 
  | hpsim_flagC_intro
    p_src0 p_tgt0 p_src1 p_tgt1 st_src st_tgt fmr
    (SIM: r _ RR p_src0 p_tgt0 st_src st_tgt fmr)
    (SRC: p_src0 = true -> p_src1 = true)
    (TGT: p_tgt0 = true -> p_tgt1 = true)
  :
    hpsim_flagC r RR p_src1 p_tgt1 st_src st_tgt fmr
  .   

  Lemma hpsim_flagC_mon r1 r2 (LE: r1 <7= r2) : @hpsim_flagC r1 <7= @hpsim_flagC r2.
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve hpsim_flagC_mon: paco.
  
  Lemma hpsim_flagC_spec with_dummy: hpsim_flagC <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x2 x3 SRC TGT. induction SIM; i; clarify; et.
    exploit SRC; et. exploit TGT; et. i. clarify. econs; et.
    eapply rclo7_base; et.
  Qed.

  Lemma hpsim_flag_down with_dummy R RR r g p_src p_tgt st_src st_tgt fmr
        (SIM: gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR false false st_src st_tgt fmr)
      :
        gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g R RR p_src p_tgt st_src st_tgt fmr.
  Proof. 
    guclo hpsim_flagC_spec. econs; et. 
  Qed.


  Variant hpsim_bindC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_bindC_intro
      p_src p_tgt Q QQ st_src st_tgt i_src i_tgt fmr
      (SIM: r Q QQ p_src p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)

      R RR k_src k_tgt
      (SIMK: forall st_src0 st_tgt0 vret_src vret_tgt fmr0
               (RET: Own fmr0 ⊢ #=> QQ (st_src0, vret_src) (st_tgt0, vret_tgt)),
             r R RR false false (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt) fmr0)
    :
    hpsim_bindC r R RR p_src p_tgt (st_src, i_src >>= k_src) (st_tgt, i_tgt >>= k_tgt) fmr
  .

  Lemma hpsim_bindC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_bindC r1 <7= hpsim_bindC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma hpsim_bindC_wrespectful:
    wrespectful7 (@_hpsim false) hpsim_bindC.
  Proof.
    econs; eauto using hpsim_bindC_mon; i.
    destruct PR. apply GF in SIM.
    remember (st_src, i_src) as sti_src. remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before GF. revert_until SIM.
    induction SIM; i; depdes Heqsti_src Heqsti_tgt; grind; eauto with paco.
    - hexploit SIMK; eauto. i.
      apply GF in H. eapply _hpsim_mon; cycle 1.
      { i. econs. apply PR. }
      eapply _hpsim_mon_progress; eauto; clarify.
    - econs; eauto. rewrite <-!bind_bind. eapply IHSIM; eauto.
    - econs; eauto. rewrite <-!bind_bind. eapply IHSIM; eauto.
    - econs; eauto. eauto 10 using rclo7, hpsim_bindC.
  Qed.

  Lemma hpsim_bindC_spec:
    hpsim_bindC <8= gupaco7 (@_hpsim false) (cpn7 (@_hpsim false)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco.
    apply hpsim_bindC_wrespectful.
  Qed.




  Variant hpsim_extendC (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_extendC_intro
      p_src p_tgt R RR sti_src sti_tgt fmr fmr'
      (SIM: r R RR p_src p_tgt sti_src sti_tgt fmr)
      (EXT: URA.extends fmr fmr')
      (WF: URA.wf fmr')
    :
    hpsim_extendC r R RR p_src p_tgt sti_src sti_tgt fmr'
  .

  Lemma hpsim_extendC_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_extendC r1 <7= hpsim_extendC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma hpsim_extendC_compatible:
    compatible7 (@_hpsim false) hpsim_extendC.
  Proof. Admitted.

  Lemma hpsim_extendC_spec:
    hpsim_extendC <8= gupaco7 (@_hpsim false) (cpn7 (@_hpsim false)).
  Proof.
    intros. gclo. econs; eauto using hpsim_extendC_compatible.
    eapply hpsim_extendC_mon, PR; eauto with paco.
  Qed.

  Definition itreeH_dummy_ktree Q R (k k': Q -> itree hAGEs R) :=
    k' = k \/ k' = (fun x => trigger (Guarantee True);;; k x).
  Hint Unfold itreeH_dummy_ktree.
  
  Definition itreeH_dummy R (itr itr': itree hAGEs R) :=
    exists Q i k k',
      itr = (i >>= k) /\
      itr' = (i >>= k') /\
      itreeH_dummy_ktree Q R k k'.
  Hint Unfold itreeH_dummy.

  Lemma itreeH_dummy_refl R i:
    itreeH_dummy R i i.
  Proof.
    replace i with (x <- Ret tt;; Ret tt;;; i); cycle 1.
    { rewrite !bind_ret_l. eauto. }
    r; esplits; last left; eauto; grind.
  Qed.
  Hint Resolve itreeH_dummy_refl.
  
  Lemma itreeH_dummy_dummy Q R i (k: Q -> _):
    itreeH_dummy R (i >>= k) (x <- i ;; trigger (Guarantee True);;; k x).
  Proof.
    r; esplits; last right; eauto.
  Qed.
  Hint Resolve itreeH_dummy_dummy.

  Variant hpsim_dummyC_src (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_dummyC_src_intro R RR ps pt st_src i_src i_src' st_tgt i_tgt fmr fmr'
      (SIM: r R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
      (RELr: Own fmr' ⊢ #=> Own fmr)
      (DUMMY: itreeH_dummy R i_src i_src')
    :
    hpsim_dummyC_src r R RR ps pt (st_src, i_src') (st_tgt, i_tgt) fmr'
  .
  
  Lemma hpsim_dummyC_src_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_dummyC_src r1 <7= hpsim_dummyC_src r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma hpsim_dummyC_src_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_dummyC_src.
  Proof.
    econs; eauto using hpsim_dummyC_src_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    induction SIM; i; depdes Heqsti_src Heqsti_tgt;
      grind; eauto 7 with paco imodL; r in DUMMY; des.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      destruct DUMMY1; subst; rewrite <-x; econs; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto with imodL.
        * eapply hpsim_guarantee_src; try econs; eauto with imodL.
      + replace c with (Call fn varg).
        econs; eauto with imodL.
        i. destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_src; try econs; eauto with imodL.
      + replace e with (Syscall fn varg rvs).
        econs; eauto with imodL.
        i. destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_src; try econs; eauto with imodL.
      + replace c with (Call fn varg).
        econs; eauto with imodL.
        destruct DUMMY1; subst; destruct with_dummy; eauto.
        * eapply IHSIM; eauto.
          eexists _, (x<-f varg;; trigger (Guarantee True);;; ktrH' x), k, _.
          esplits; eauto; grind.
        * eapply IHSIM; eauto.
          eexists _, (f varg >>= ktrH'), k, _.
          esplits; eauto; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x; eauto.
        eapply hpsim_guarantee_src; eauto with imodL.
      + econs; eauto with imodL.
        destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_src; eauto with imodL.
          econs; eauto with imodL.
      + replace e with (Choose R0); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_src; eauto with imodL.
          econs; eauto with imodL.
      + replace e with (Take R0); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_src; eauto with imodL.
          econs; eauto.
      + replace s with (SUpdate run); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; try instantiate (1:=FMR); eauto with imodL.
        * eapply hpsim_guarantee_src; eauto with imodL.
          econs; try instantiate (1:=FMR); eauto with imodL.
      + econs; eauto. i. eapply H; eauto.
        { eapply imod_trans; eauto.
          iIntros "H". iDestruct "H" as "[X H]".
          iSplitL "X"; eauto. iStopProof; eauto. }
        destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_src) -bind_vis.
        * econs; eauto with imodL.
        * eapply hpsim_guarantee_src; eauto with imodL.
          econs; eauto with imodL.
      + econs; eauto with imodL.
        i. eapply H; eauto. destruct DUMMY1; subst; eauto.
    - subst. econs; eauto. destruct DUMMY1; subst; econs; eauto.
  Qed.

  Lemma hpsim_dummyC_src_spec (with_dummy:bool) :
    hpsim_dummyC_src <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_src_compatible.
    eapply hpsim_dummyC_src_mon, PR; eauto with paco.
  Qed.

  Variant hpsim_dummyC_tgt (r: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop):
    forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop
  :=
  | hpsim_dummyC_tgt_intro R RR ps pt st_src i_src st_tgt i_tgt i_tgt' fmr fmr'
      (SIM: r R RR ps pt (st_src, i_src) (st_tgt, i_tgt) fmr)
      (RELr: Own fmr' ⊢ #=> Own fmr)
      (DUMMY: itreeH_dummy R i_tgt i_tgt')
    :
    hpsim_dummyC_tgt r R RR ps pt (st_src, i_src) (st_tgt, i_tgt') fmr'
  .
  
  Lemma hpsim_dummyC_tgt_mon
        r1 r2
        (LEr: r1 <7= r2)
    :
    hpsim_dummyC_tgt r1 <7= hpsim_dummyC_tgt r2
  .
  Proof. i. destruct PR; econs; eauto. Qed.

  Lemma hpsim_dummyC_tgt_compatible with_dummy:
    compatible7 (@_hpsim with_dummy) hpsim_dummyC_tgt.
  Proof.
    econs; eauto using hpsim_dummyC_tgt_mon; i. depdes PR.
    remember (st_src, i_src) as sti_src.
    remember (st_tgt, i_tgt) as sti_tgt.
    move SIM before RR. revert_until SIM.
    induction SIM; i; depdes Heqsti_src Heqsti_tgt;
      grind; eauto 7 with paco imodL; r in DUMMY; des.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      destruct DUMMY1; subst; rewrite <-x; econs; eauto; imodIntroL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto with imodL.
        * eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
      + replace c with (Call fn varg).
        econs; eauto with imodL.
        i. destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
      + replace e with (Syscall fn varg rvs).
        econs; eauto with imodL.
        i. destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_tgt; try econs; eauto; imodIntroL.
      + replace c with (Call fn varg).
        econs; eauto with imodL.
        destruct DUMMY1; subst; destruct with_dummy; eauto.
        * eapply IHSIM; eauto.
          eexists _, (x<-f varg;; trigger (Guarantee True);;; ktrH' x), k, _.
          esplits; eauto; grind.
        * eapply IHSIM; eauto.
          eexists _, (f varg >>= ktrH'), k, _.
          esplits; eauto; grind.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x; eauto.
        eapply hpsim_guarantee_tgt; eauto; imodIntroL.
      + econs; eauto with imodL.
        destruct DUMMY1; subst; eauto with imodL.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_tgt; eauto with imodL.
          econs; eauto; imodIntroL.
      + replace e with (Choose R0); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_tgt; eauto with imodL.
          econs; eauto; imodIntroL.
      + replace e with (Take R0); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto.
        * eapply hpsim_guarantee_tgt; eauto with imodL.
          econs; eauto; imodIntroL.
      + replace s with (SUpdate run); econs; eauto.
        i. destruct DUMMY1; subst; eauto.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; try instantiate (1:=FMR); eauto with imodL.
        * eapply hpsim_guarantee_tgt; eauto with imodL.
          econs; try instantiate (1:=FMR); eauto; imodIntroL.
      + econs; eauto; imodIntroL. eapply H; eauto 10.
    - assert (CASE:= case_itrH _ i); des; subst; itree_clarify DUMMY.
      + destruct DUMMY1; subst; rewrite -x -(bind_ret_l_eta _ k_tgt) -bind_vis.
        * econs; eauto. i. eapply H; eauto.
          eapply imod_trans; eauto.
          iIntros "H". iDestruct "H" as "[X H]".
          iSplitL "X"; eauto. iStopProof; eauto.
        * eapply hpsim_guarantee_tgt; eauto. econs; eauto.
          i. eapply H; eauto.
          iIntros "H". iPoseProof (NEW0 with "H") as "H". iMod "H".
          iDestruct "H" as "[P [_ H]]". iSplitL "P"; eauto. iStopProof; eauto.
      + econs; eauto with imodL.
        i. eapply H; eauto.
        { iIntros "H". iPoseProof (NEW with "H") as "H". iMod "H".
          iDestruct "H" as "[P H]". iSplitL "P"; eauto. iStopProof; eauto. }
        destruct DUMMY1; subst; eauto.
    - subst. econs; eauto. destruct DUMMY1; subst; econs; eauto.
  Qed.

  Lemma hpsim_dummyC_tgt_spec (with_dummy:bool) :
    hpsim_dummyC_tgt <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    intros. gclo. econs; eauto using hpsim_dummyC_tgt_compatible.
    eapply hpsim_dummyC_tgt_mon, PR; eauto with paco.
  Qed.
  
  Lemma hpsim_le_gpaco with_dummy r r':
    @hpsim <7= gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r r'.
  Proof.
    gcofix CIH. i. punfold PR.
    induction PR; pclearbot; eauto with paco;
      guclo hpsimC_spec; eauto with paco.
    - econs; eauto. destruct with_dummy; eauto.
      guclo hpsim_dummyC_src_spec. econs; eauto.
    - econs; eauto. destruct with_dummy; eauto.
      guclo hpsim_dummyC_tgt_spec. econs; eauto.
  Qed.
  
  Hint Resolve hpsim_le_gpaco: paco.

  Corollary hpsim_add_dummy:
    @hpsim <7= paco7 (@_hpsim true) bot7.
  Proof. ginit. eauto with paco. Qed.


  Definition hpsim_fsem: relation (Any.t -> itree hAGEs Any.t) :=
    (eq ==> (fun itr_src itr_tgt => forall st_src st_tgt (INV: I st_src st_tgt ε),
                hpsim_body false false (st_src, itr_src) (st_tgt, itr_tgt) ε))%signature.

  Definition hpsim_fnsem: relation (string * (Any.t -> itree hAGEs Any.t)) := RelProd eq hpsim_fsem.

  (* Arguments _hpsim {with_dummy} hpsim {R} RR.

  Definition hpsim {R} RR := paco7 (@_hpsim false) bot7 R RR.

  Definition hpsim_end : Any.t*Any.t -> Any.t*Any.t -> iProp :=
    fun '(st_src, v_src) '(st_tgt, v_tgt) => I st_src st_tgt ** ⌜v_src = v_tgt⌝. *)

End HPSIM.

Hint Resolve _hpsim_mon: paco.
Hint Resolve cpn7_wcompat: paco.

(**********)


Lemma hpsim_self {Σ: GRA.t}:
  forall st itr fl fmr,
    hpsim_body fl fl (fun src tgt => ⌜src = tgt⌝%I) false false (st, itr) (st, itr) fmr.
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply hpsim_ret; ss.
    iIntros "H". et.
  }
  { guclo hpsimC_spec. econs. 
    guclo hpsimC_spec. econs. 
    eapply hpsim_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction h; rewrite <-! bind_trigger; resub.
    - guclo hpsimC_spec. econs. { instantiate (1:= ⌜True⌝%I). et. }
      guclo hpsimC_spec. econs; et.
      ii. eapply hpsim_progress_flag. gbase. et.
    - guclo hpsimC_spec. econs 17. { instantiate (1:= ⌜True⌝%I). et. }
      guclo hpsimC_spec. econs; et.
      ii. eapply hpsim_progress_flag. gbase. et.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger. resub.
    gstep.
    eapply hpsim_call; ss. { instantiate (1:= ⌜True⌝%I). et. }
    ii. econs; et.
    uipropall. hexploit INV; [et|refl|instantiate (1:= ε); r_solve; et|]. i. des.  
    rr in H1. uipropall. clarify.
    gbase. auto. 
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction s.
    destruct (run st) eqn:RUN.
    guclo hpsimC_spec. econs; et. 
    guclo hpsimC_spec. econs; et. 

      eapply hpsim_progress_flag. gbase. et.
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo hpsimC_spec. econs 9. i.
      guclo hpsimC_spec. econs.
      eapply hpsim_progress_flag. gbase. eauto.
    }
    { guclo hpsimC_spec. econs 10. i.
      guclo hpsimC_spec. econs.
      eapply hpsim_progress_flag. gbase. eauto.
    }
    { guclo hpsimC_spec. econs. i.
      eapply hpsim_progress_flag. gbase. eauto.
    }
  }
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
    eapply hpsim_self.
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


