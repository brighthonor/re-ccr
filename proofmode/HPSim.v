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

Section SIM.

  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Variable I: Any.t -> Any.t -> iProp.
  
  Inductive _hpsim {with_dummy: bool}
    (hpsim: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
    {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsim_ret
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
    _hpsim hpsim p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsim_call
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
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
    _hpsim hpsim true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsim_inline_src
      p_src p_tgt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: _hpsim hpsim true p_tgt (st_src, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_src x) else k_src)) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_inline_tgt
      p_src p_tgt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_tgt x) else k_tgt)) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_tau_src
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: _hpsim hpsim true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsim_tau_tgt
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsim_choose_src
      p_src p_tgt st_src st_tgt fmr
      X x k_src i_tgt
      (K: _hpsim hpsim true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_choose_tgt
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsim_take_src
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), _hpsim hpsim true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_take_tgt
      p_src p_tgt st_src st_tgt fmr
      X x i_src k_tgt
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsim_supdate_src
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: _hpsim hpsim true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_supdate_tgt
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: _hpsim hpsim p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsim_assume_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_assume_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsim_guarantee_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_guarantee_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
    _hpsim hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr

  | hpsim_progress
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

  Variant hpsim_stepC {with_dummy: bool}
  (hpsim: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
  {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsim_stepC_ret
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (* Note: (INV: Own fmr ⊢ #=> I st_src st_tgt) is required only for the funtion end. *)
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsim_stepC_call
      p_src p_tgt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
          (WF: URA.wf fmr0)
          (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
          hpsim _ RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | hpsim_stepC_syscall
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
          hpsim _ RR true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsim_stepC_inline_src
      p_src p_tgt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: hpsim _ RR true p_tgt (st_src, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_src x) else k_src)) (st_tgt, i_tgt) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_inline_tgt
      p_src p_tgt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_tgt x) else k_tgt)) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsim_stepC_tau_src
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_tau_tgt
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsim_stepC_choose_src
      p_src p_tgt st_src st_tgt fmr
      X x k_src i_tgt
      (K: hpsim _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
       hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_choose_tgt
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsim_stepC_take_src
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), hpsim _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_take_tgt
      p_src p_tgt st_src st_tgt fmr
      X x i_src k_tgt
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsim_stepC_supdate_src
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: hpsim _ RR true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_supdate_tgt
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: hpsim _ RR p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsim_stepC_assume_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsim _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_assume_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsim_stepC_guarantee_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          hpsim _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsim_stepC_guarantee_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          hpsim _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
      hpsim_stepC hpsim p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
  .
  
  Lemma hpsim_stepC_mon with_dummy : monotone7 (@hpsim_stepC with_dummy).
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.

  Hint Resolve hpsim_stepC_mon: paco.

  Lemma hpsim_stepC_spec with_dummy:
    (@hpsim_stepC with_dummy) <8= gupaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)).
  Proof.
    eapply wrespect7_uclo; eauto with paco.
    econs; eauto with paco; i.
    inv PR; econs; et; try (i; eapply _hpsim_mon; et; i; eapply rclo7_base; et).
  Qed.
  
  Variant hpsimC {with_dummy: bool}
  (r g: forall R (RR: Any.t * R -> Any.t * R -> iProp), bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop)
  {R} {RR: Any.t * R -> Any.t * R -> iProp}: bool -> bool -> Any.t * itree hAGEs R -> Any.t * itree hAGEs R -> Σ -> Prop :=
  | hpsimC_ret
      p_src p_tgt st_src st_tgt fmr
      v_src v_tgt
      (RET: Own fmr ⊢ #=> RR (st_src,v_src) (st_tgt,v_tgt))
    :
      hpsimC r g p_src p_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr
  | hpsimC_call
      p_src p_tgt st_src st_tgt fmr
      fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
      (K: forall vret st_src0 st_tgt0 fmr0 
          (WF: URA.wf fmr0)
          (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
          r _ RR true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr
  | hpsimC_syscall
      p_src p_tgt st_src st_tgt fmr
      fn varg rvs k_src k_tgt
      (K: forall vret, 
          r _ RR true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

  | hpsimC_inline_src
      p_src p_tgt st_src st_tgt fmr
      fn f varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: r _ RR true p_tgt (st_src, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_src x) else k_src)) (st_tgt, i_tgt) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_inline_tgt
      p_src p_tgt st_src st_tgt fmr
      fn f varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: r _ RR p_src true (st_src, i_src) (st_tgt, f varg >>= (if with_dummy then (fun x => trigger (Guarantee True) ;;; k_tgt x) else k_tgt)) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

  | hpsimC_tau_src
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: r _ RR true p_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

  | hpsimC_tau_tgt
      p_src p_tgt st_src st_tgt fmr
      i_src i_tgt
      (K: r _ RR p_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

  | hpsimC_choose_src
      p_src p_tgt st_src st_tgt fmr
      X x k_src i_tgt
      (K: r _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
       hpsimC r g p_src p_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_choose_tgt
      p_src p_tgt st_src st_tgt fmr
      X i_src k_tgt
      (K: forall (x: X), r _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

  | hpsimC_take_src
      p_src p_tgt st_src st_tgt fmr
      X k_src i_tgt
      (K: forall (x: X), r _ RR true p_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_take_tgt
      p_src p_tgt st_src st_tgt fmr
      X x i_src k_tgt
      (K: r _ RR p_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

  | hpsimC_supdate_src
      p_src p_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
      (K: r _ RR true p_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_supdate_tgt
      p_src p_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
      (K: r _ RR p_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

  | hpsimC_assume_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          r _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_assume_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          r _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

  | hpsimC_guarantee_src
      p_src p_tgt st_src st_tgt fmr
      iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          r _ RR true p_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
    :
      hpsimC r g p_src p_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

  | hpsimC_guarantee_tgt
      p_src p_tgt st_src st_tgt fmr
      iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
      (K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          r _ RR p_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
    :
      hpsimC r g p_src p_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr
  .
  
  Lemma hpsimC_spec with_dummy r g:
    (@hpsimC with_dummy) (gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g) (gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) g g)
    <7=
    gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r g.
  Proof.
    i. eapply gpaco7_gpaco; [eauto with paco|].
    eapply gpaco7_mon; [|eauto|i; eapply gupaco7_mon; et].
    inv PR; try (guclo hpsim_stepC_spec; econs; et; i; gbase; et).
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
    - econs. eauto 10 using rclo7, hpsim_bindC.
  Qed.

  Lemma hpsim_bindC_spec:
    hpsim_bindC <8= gupaco7 (@_hpsim false) (cpn7 (@_hpsim false)).
  Proof.
    intros. eapply wrespect7_uclo; eauto with paco.
    apply hpsim_bindC_wrespectful.
  Qed.

  Lemma hpsim_guarantee_true_src R RR ps pt st_src st_tgt v_src v_tgt fmr
    (REL: Own fmr ⊢ #=> RR (st_src, v_src) (st_tgt, v_tgt))
    :
    @hpsim R RR ps pt (st_src, trigger (Guarantee True);;; Ret v_src) (st_tgt, Ret v_tgt) fmr.
  Proof.
    ginit. gstep. econs.
    { instantiate (1:=Own fmr); eauto. }
    i. econs. iIntros "H". iPoseProof (NEW with "H") as "H". iMod "H".
    iPoseProof (REL with "H") as "H". eauto.
  Qed.

  Lemma hpsim_guarantee_true_tgt R RR ps pt st_src st_tgt v_src v_tgt fmr
    (REL: Own fmr ⊢ #=> RR (st_src, v_src) (st_tgt, v_tgt))
    :
    @hpsim R RR ps pt (st_src, Ret v_src) (st_tgt, trigger (Guarantee True);;; Ret v_tgt) fmr.
  Proof.
    ginit. gstep. econs.
    { instantiate (1:=Own fmr); eauto. }
    i. econs. iIntros "H". iPoseProof (NEW with "H") as "H". iMod "H".
    iDestruct "H" as "[X Y]". iPoseProof (REL with "Y") as "Y". eauto.
  Qed.

  Lemma hpsim_le_gpaco with_dummy r r':
    @hpsim <7= gpaco7 (@_hpsim with_dummy) (cpn7 (@_hpsim with_dummy)) r r'.
  Proof.
    gcofix CIH. i. punfold PR.
    gstep. induction PR; eauto.
  Admitted.
  Hint Resolve hpsim_le_gpaco: paco.

  Corollary hpsim_add_dummy:
    @hpsim <7= paco7 (@_hpsim true) bot7.
  Proof. ginit. eauto with paco. Qed.
                
  Lemma current_iProp_sepconj P Q r 
      (SAT: current_iProp r (P ** Q))
    :
      exists rp rq, URA.updatable r (rp ⋅ rq) /\ current_iProp rp P /\ current_iProp rq Q
  .
  Proof.
    destruct SAT. rr in IPROP. uipropall. des. clarify.
    hexploit UPD. i. eapply URA.updatable_wf in H; et. des.
    esplits; et; econs; et; r_solve.
    - eapply URA.wf_mon in H. et.
    - eapply URA.wf_extends in H; et. econs. instantiate (1:= a). r_solve.
  Qed.

  Lemma own_ctx a b
      (OWN: Own a ⊢ #=> Own b)
    :
      forall ctx, Own (ctx ⋅ a) ⊢ #=> Own (ctx ⋅ b)
  .
  Proof.
    i. iIntros "[H H0]".
    iPoseProof (OWN with "H0") as "H0".
    iSplitL "H"; et.
  Qed.

  Lemma own_wf (r r': Σ)
      (OWN: Own r ⊢ #=> Own r')
      (WF: URA.wf r)
    :
      URA.wf r'
  .
  Proof. 
    uipropall. hexploit OWN; et. refl.
    esplits; et. des.
    eapply URA.wf_extends; et.
    specialize (H0 ε). rewrite ! URA.unit_id in H0.
    et.
  Qed.



  Lemma not_wf_sat (r: Σ) (ILL: ¬ URA.wf r) P: Own r ⊢ P.
  Proof.
    rr. uipropall. i.
    eapply URA.wf_extends in WF; et.
    clarify.
  Qed.

  Lemma iProp_sepconj_aux P Q r 
      (SAT: Own r ⊢ #=> (P ** Q))
    :
      exists rp rq, (URA.updatable r (rp ⋅ rq)) /\ 
                    (Own rp ⊢ P) /\ 
                    (Own rq ⊢ Q)
  .
  Proof.
    destruct (classic (URA.wf r)); cycle 1.
    {
      exists r, r. esplits; eauto using not_wf_sat.
      rr. i. eapply URA.wf_mon in H0. clarify. 
    }

    uipropall.
    hexploit SAT; et. { r_solve. }
    i. des.
    esplits; et; uipropall.
    {
      instantiate (1:= b). instantiate (1:=a).
      unfold URA.updatable. subst. et. 
    }
    {
      i. destruct P. ss.
      hexploit H4. i.
      eapply URA.wf_extends in H4; et.
    }
    {
      i. destruct Q. ss.
      hexploit H4. i.
      eapply URA.wf_extends in H4; et.
    }
  Qed.

  Lemma iProp_sepconj P Q r 
      (SAT: Own r ⊢ #=> (P ** Q))
    :
      exists rp rq, (Own r ⊢ #=> Own (rp ⋅ rq)) /\ 
                    (Own rp ⊢ P) /\ 
                    (Own rq ⊢ Q)
  .
  Proof.
    eapply iProp_sepconj_aux in SAT; et. des.
    eapply Own_Upd in SAT.
    esplits; et. 	
  Qed.	

  Lemma current_iProp_sepconj' P Q r 
      (SAT: current_iProp r (P ** Q))
    :
      exists rp rq, URA.updatable r (rp ⋅ rq) /\ P rp /\ Q rq
  .
  Proof.
    destruct SAT. rr in IPROP. uipropall. des. clarify.
    hexploit UPD. i. eapply URA.updatable_wf in H; et. 
  Qed.

  Lemma current_iProp_sepconj_r P Q r 
      (SAT: current_iProp r (P ** Q))
    :
      exists rp rq, URA.updatable r (rp ⋅ rq) /\ P rp /\ current_iProp rq Q
  .
  Proof.
    destruct SAT. rr in IPROP. uipropall. des. clarify.
    hexploit UPD. i. eapply URA.updatable_wf in H; et. 
    esplits; et; econs; et; r_solve.
    des. eapply URA.wf_extends; et. econs. instantiate (1:= a). r_solve.
  Qed.

  Lemma current_iProp_conj P Q x y
      (IP: current_iProp x P)
      (IQ: current_iProp y Q)
      (WF: URA.wf (x ⋅ y))
  :
      current_iProp (x ⋅ y) (P ** Q)
  .
  Proof. 
    inv IP. inv IQ.
    econs; et.
    { uipropall. esplits; et. }
    eapply URA.updatable_add; et.
  Qed.


  Lemma current_iPropL_convert fmr P
        (CUR: current_iProp fmr P)
    :
      current_iPropL fmr [("H", P)].
  Proof.
    unfold current_iPropL. ss. unfold from_iPropL.
    eapply current_iProp_entail; eauto.
  Qed.

  Variant _sim_strict (sim_strict: forall R, relation (Any.t * R) -> relation (Any.t * itree Es R))
    : forall R, relation (Any.t * R) -> relation (Any.t * itree Es R)
  :=
  | sim_strict_ret R RR st st' v v'
      (RET: RR (st,v) (st',v'): Prop)
    :
    _sim_strict sim_strict R RR
      (st, Ret v)
      (st', Ret v')
  | sim_strict_call R RR
      st fn varg k k'
      (K: forall st0 vret,
          sim_strict R RR (st0, k vret) (st0, k' vret))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Call fn varg) >>= k)
      (st, trigger (Call fn varg) >>= k')
  | sim_strict_syscall R RR
      st st' fn varg rvs k k'
      (K: forall vret,
          sim_strict R RR (st, k vret) (st', k' vret))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Syscall fn varg rvs) >>= k)
      (st', trigger (Syscall fn varg rvs) >>= k')
  | sim_strict_tau R RR
      st st' i i'
      (K: sim_strict R RR (st, i) (st', i'))
    :
    _sim_strict sim_strict R RR
      (st, tau;; i)
      (st', tau;; i')
  | sim_strict_choose R RR
      st st' X X' k k'
      (K: forall x', exists x, sim_strict R RR (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Choose X) >>= k)
      (st', trigger (Choose X') >>= k')
  | sim_strict_take R RR
      st st' X X' k k'
      (K: forall x, exists x', sim_strict R RR (st, k x) (st', k' x'))
    :
    _sim_strict sim_strict R RR
      (st, trigger (Take X) >>= k)
      (st', trigger (Take X') >>= k')
  | sim_strict_supdate R RR
      st st' X k X' k' (run: Any.t -> Any.t * X) (run': Any.t -> Any.t * X')
      (K: sim_strict R RR
            (fst (run st), k (snd (run st)))
            (fst (run' st'), k' (snd (run' st'))))
    :
    _sim_strict sim_strict R RR
      (st, trigger (SUpdate run) >>= k)
      (st', trigger (SUpdate run') >>= k')
  .

  Definition sim_strict := paco4 _sim_strict bot4.

  Lemma sim_strict_mon: monotone4 _sim_strict.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_strict.
  Hint Unfold sim_strict.
  Hint Resolve sim_strict_mon: paco.
  Hint Resolve cpn4_wcompat: paco.

  Lemma sim_strict_refl
    R sti
    :
    sim_strict R eq sti sti.
  Proof.
    revert_until I. ginit. gcofix CIH; i.
    destruct sti as [st i]. ides i; eauto with paco.
    gstep. destruct e; [destruct c|destruct s; [destruct s|destruct e]].
    - hexploit (sim_strict_call (gpaco4 _sim_strict (cpn4 _sim_strict) r r) R eq); i.
      { instantiate (1:=k). eauto with paco. }
      unfold trigger in H. rewrite !bind_vis in H.
      erewrite f_equal2; eauto; repeat (eapply f_equal; eauto);
        extensionality x; rewrite !bind_ret_l; eauto.
    - hexploit (sim_strict_supdate (gpaco4 _sim_strict (cpn4 _sim_strict) r r) R eq); i.
      { instantiate (4:=k). eauto with paco. }
      unfold trigger in H. rewrite !bind_vis in H.
      erewrite f_equal2; eauto; repeat (eapply f_equal; eauto);
        extensionality x; rewrite !bind_ret_l; eauto.
    - hexploit (sim_strict_choose (gpaco4 _sim_strict (cpn4 _sim_strict) r r) R eq); i.
      { eexists. instantiate (4:=k). eauto with paco. }
      unfold trigger in H. rewrite !bind_vis in H.
      erewrite f_equal2; eauto; repeat (eapply f_equal; eauto);
        extensionality x; rewrite !bind_ret_l; eauto.
    - hexploit (sim_strict_take (gpaco4 _sim_strict (cpn4 _sim_strict) r r) R eq); i.
      { eexists. instantiate (4:=k). eauto with paco. }
      unfold trigger in H. rewrite !bind_vis in H.
      erewrite f_equal2; eauto; repeat (eapply f_equal; eauto);
        extensionality x; rewrite !bind_ret_l; eauto.
    - hexploit (sim_strict_syscall (gpaco4 _sim_strict (cpn4 _sim_strict) r r) R eq); i.
      { instantiate (3:=k). eauto with paco. }
      unfold trigger in H. rewrite !bind_vis in H.
      erewrite f_equal2; eauto; repeat (eapply f_equal; eauto);
        extensionality x; rewrite !bind_ret_l; eauto.
  Qed.

  Lemma sim_strict_le
    R RR RR'
    (LE: RR <2= RR')
    :
    sim_strict R RR <2= sim_strict R RR'.
  Proof.
    ginit. gcofix CIH. i. punfold PR.
    inv PR; grind; depdes H0; unfold trigger in *;
      try (rewrite !bind_vis in x); gstep; econs; i;
      try edestruct K; pclearbot; eauto with paco.
  Qed.

  Variant sim_strict_bindC (r: forall R, relation (Any.t*R) -> relation (Any.t * itree Es R)) :
    forall R, relation (Any.t*R) -> relation (Any.t * itree Es R)
  :=
  | sim_strict_bindC_intro R RR Q QQ st st' i i' k k'
      (HD: r R RR (st,i) (st',i'))
      (TL: forall st0 v0 st0' v0' (REL: RR (st0,v0) (st0',v0')),
           r Q QQ (st0, k v0) (st0', k' v0'))
    :
    sim_strict_bindC r Q QQ (st, i >>= k) (st', i' >>= k')
  .

  Lemma sim_strict_bindC_mon
        r1 r2
        (LEr: r1 <4= r2)
    :
    sim_strict_bindC r1 <4= sim_strict_bindC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_bindC_wrespectful:
    wrespectful4 _sim_strict sim_strict_bindC.
  Proof.
    econs; eauto using sim_strict_bindC_mon; i.
    destruct PR. apply GF in HD. inv HD; grind; depdes H3 H0; grind;
      try (by econs; i; econs 2; eauto; econs; eauto using rclo4).
    - eapply sim_strict_mon; eauto using rclo4.
    - econs. i. specialize (K x'). des.
      eexists. econs 2; eauto. econs; eauto using rclo4.
    - econs. i. specialize (K x). des.
      eexists. econs 2; eauto. econs; eauto using rclo4.
  Qed.

  Lemma sim_strict_bindC_spec:
    sim_strict_bindC <5= gupaco4 _sim_strict (cpn4 _sim_strict).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco.
    apply sim_strict_bindC_wrespectful.
  Qed.

  Variant sim_strict_transC (r: forall R, relation (Any.t*R) -> relation (Any.t * itree Es R)) :
    forall R, relation (Any.t*R) -> relation (Any.t * itree Es R)
  :=
  | sim_strict_transC_intro R RR0 RR1 RR st st' st'' i i' i''
      (REL0: r R RR0 (st,i) (st',i'))
      (REL1: r R RR1 (st',i') (st'',i''))
      (LE: rcompose RR0 RR1 <2= RR)
    :
    sim_strict_transC r R RR (st, i) (st'', i'')
  .

  Lemma sim_strict_transC_mon
        r1 r2
        (LEr: r1 <4= r2)
    :
    sim_strict_transC r1 <4= sim_strict_transC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Lemma sim_strict_transC_wrespectful:
    wrespectful4 _sim_strict sim_strict_transC.
  Proof.
    econs; eauto using sim_strict_transC_mon; i.
    destruct PR. apply GF in REL0. apply GF in REL1.
    inv REL0; grind; depdes H3 H0; grind; unfold trigger in *; try (rewrite !bind_vis in x; depdes x);
      inv REL1; grind; depdes H3 H0; grind; unfold trigger in *; try (rewrite !bind_vis in x; depdes x);
      econs; i; eauto using sim_strict_transC, rclo4.
    - replace k' with k0 in K; eauto using sim_strict_transC, rclo4.
      extensionality v. eapply equal_f in x. rewrite !bind_ret_l in x. eauto.
    - replace k' with k0 in K; eauto using sim_strict_transC, rclo4.
      extensionality v. eapply equal_f in x. rewrite !bind_ret_l in x. eauto.
    - replace k' with k0 in K; cycle 1.
      { extensionality v. eapply equal_f in x. rewrite !bind_ret_l in x. eauto. }
      destruct (K0 x'), (K x0). eauto using sim_strict_transC, rclo4.
    - replace k' with k0 in K; cycle 1.
      { extensionality v. eapply equal_f in x. rewrite !bind_ret_l in x. eauto. }
      destruct (K x0), (K0 x1). eauto using sim_strict_transC, rclo4.
    - replace k' with k0 in K; cycle 1; eauto using sim_strict_transC, rclo4.
      extensionality v. eapply equal_f in x. rewrite !bind_ret_l in x. eauto.
  Qed.

  Lemma sim_strict_transC_spec:
    sim_strict_transC <5= gupaco4 _sim_strict (cpn4 _sim_strict).
  Proof.
    intros. eapply wrespect4_uclo; eauto with paco.
    apply sim_strict_transC_wrespectful.
  Qed.

  Lemma sim_strict_inv_ret R RR sti st' v'
      (EQV: sim_strict R RR sti (st', Ret v')):
    exists st v, sti = (st, Ret v) /\ RR (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).      
  Qed.

  Lemma sim_strict_inv_ret' R RR st v sti'
      (EQV: sim_strict R RR (st, Ret v) sti'):
    exists st' v', sti' = (st', Ret v') /\ RR (st, v) (st', v').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
  Qed.
  
  Lemma sim_strict_inv_call R RR sti st fn varg k'
      (EQV: sim_strict R RR sti (st, trigger (Call fn varg) >>= k')):
    exists k,
    sti = (st, trigger (Call fn varg) >>= k) /\
    forall st0 vret, sim_strict R RR (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    esplits; eauto. i.
    specialize (K st0 vret). pclearbot.
    replace k' with k'0; eauto.
    extensionality v. depdes H0. eapply equal_f in x.
    rewrite !bind_ret_l in x. eauto.
  Qed.

  Lemma sim_strict_inv_call' R RR st fn varg k sti' 
      (EQV: sim_strict R RR (st, trigger (Call fn varg) >>= k) sti'):
    exists k',
    sti' = (st, trigger (Call fn varg) >>= k') /\
    forall st0 vret, sim_strict R RR (st0, k vret) (st0, k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    esplits; eauto. i.
    specialize (K st0 vret). pclearbot.
    replace k with k0; eauto.
    extensionality v. depdes H0. eapply equal_f in x.
    rewrite !bind_ret_l in x. eauto.
  Qed.
  
  Lemma sim_strict_inv_syscall R RR sti st' fn varg rvs k'
      (EQV: sim_strict R RR sti (st', trigger (Syscall fn varg rvs) >>= k')):
    exists st k,
    sti = (st, trigger (Syscall fn varg rvs) >>= k) /\
    forall vret, sim_strict R RR (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    esplits; eauto. i.
    specialize (K vret). pclearbot.
    replace k' with k'0; eauto.
    extensionality v. depdes H0. eapply equal_f in x.
    rewrite !bind_ret_l in x. eauto.
  Qed.

  Lemma sim_strict_inv_syscall' R RR st fn varg rvs k sti'
      (EQV: sim_strict R RR (st, trigger (Syscall fn varg rvs) >>= k) sti'):
    exists st' k',
    sti' = (st', trigger (Syscall fn varg rvs) >>= k') /\
    forall vret, sim_strict R RR (st, k vret) (st', k' vret).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    esplits; eauto. i.
    specialize (K vret). pclearbot.
    replace k with k0; eauto.
    extensionality v. depdes H0. eapply equal_f in x.
    rewrite !bind_ret_l in x. eauto.
  Qed.
  
  Lemma sim_strict_inv_tau R RR sti st' i'
      (EQV: sim_strict R RR sti (st', tau;; i')):
    exists st i,
    sti = (st, tau;; i) /\
    sim_strict R RR (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_tau' R RR st i sti' 
      (EQV: sim_strict R RR (st, tau;; i) sti'):
    exists st' i',
    sti' = (st', tau;; i') /\
    sim_strict R RR (st, i) (st', i').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_choose R RR sti st' X' k'
      (EQV: sim_strict R RR sti (st', trigger (Choose X') >>= k')):
    exists st X k,
    sti = (st, trigger (Choose X) >>= k) /\
    forall x', exists x, sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k' with k'0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_choose' R RR st X k sti' 
      (EQV: sim_strict R RR (st, trigger (Choose X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Choose X') >>= k') /\
    forall x', exists x, sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k with k0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    esplits; eauto.
    i. specialize (K x'). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_take R RR sti st' X' k'
      (EQV: sim_strict R RR sti (st', trigger (Take X') >>= k')):
    exists st X k,
    sti = (st, trigger (Take X) >>= k) /\
    forall x, exists x', sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k' with k'0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.

  Lemma sim_strict_inv_take' R RR st X k sti'
      (EQV: sim_strict R RR (st, trigger (Take X) >>= k) sti'):
    exists st' X' k',
    sti' = (st', trigger (Take X') >>= k') /\
    forall x, exists x', sim_strict R RR (st, k x) (st', k' x').
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k with k0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    esplits; eauto.
    i. specialize (K x). des. pclearbot. eauto.
  Qed.
  
  Lemma sim_strict_inv_update R RR sti st' X' (run': Any.t -> Any.t * X') k'
      (EQV: sim_strict R RR sti (st', trigger (SUpdate run') >>= k')):
    exists X (run: Any.t -> Any.t * X) st k,
    sti = (st, trigger (SUpdate run) >>= k) /\
    sim_strict R RR ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0 H2; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k' with k'0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    depdes H1. pclearbot. esplits; eauto.
  Qed.

  Lemma sim_strict_inv_update' R RR st X (run: Any.t -> Any.t * X) k sti'
      (EQV: sim_strict R RR (st, trigger (SUpdate run) >>= k) sti'):
    exists X' (run': Any.t -> Any.t * X') st' k',
    sti' = (st', trigger (SUpdate run') >>= k') /\
    sim_strict R RR ((run st).1, k (run st).2) ((run' st').1, k' (run' st').2).
  Proof.
    punfold EQV. inv EQV; grind; depdes H0; unfold trigger in *; eauto;
      try (rewrite !bind_vis in x; clarify).
    replace k with k0; cycle 1.
    { depdes H0. extensionality v. eapply equal_f in x.
      rewrite !bind_ret_l in x. eauto. }
    depdes H1. pclearbot. esplits; eauto.
  Qed.

  (** **)

  Variant sim_strictC
      (r: forall S_src S_tgt (RR: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> Σ -> Any.t * itree Es S_src -> Any.t * itree Es S_tgt -> Prop):
      forall S_src S_tgt (RR: Any.t -> Any.t -> S_src -> S_tgt -> Prop), bool -> bool -> Σ -> Any.t * itree Es S_src -> Any.t * itree Es S_tgt -> Prop
    :=
  | sim_strictC_intro RR p_src p_tgt w sti_src sti_tgt sti_src' sti_tgt'
      (SIM: r Any.t Any.t RR p_src p_tgt w sti_src' sti_tgt')
      (EQVSRC: sim_strict Any.t eq sti_src sti_src')
      (EQVTGT: sim_strict Any.t eq sti_tgt' sti_tgt)
    : sim_strictC r Any.t Any.t RR p_src p_tgt w sti_src sti_tgt
  .

  Lemma sim_strictC_mon r1 r2
    (LEr: r1 <8= r2)
    :
    sim_strictC r1 <8= sim_strictC r2.
  Proof. ii. destruct PR. econs; et. Qed.

  Lemma sim_strictC_compatible: forall wf le fl_src fl_tgt, 
      compatible8 (@_sim_itree Σ wf le fl_src fl_tgt) sim_strictC.
  Proof.
    econs; i; eauto using sim_strictC_mon. depdes PR.
    move SIM before RR. revert_until SIM.
    induction SIM; i; subst.
    - apply sim_strict_inv_ret in EQVSRC. apply sim_strict_inv_ret' in EQVTGT.
      des. subst. clarify. eauto using _sim_itree.
    - apply sim_strict_inv_call in EQVSRC. apply sim_strict_inv_call' in EQVTGT.
      des. subst. clarify. eauto using _sim_itree.
    - apply sim_strict_inv_syscall in EQVSRC. apply sim_strict_inv_syscall' in EQVTGT.
      des. subst. eauto using _sim_itree.
    - apply sim_strict_inv_call in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto. eapply IHSIM; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gfinal. right. apply EQVSRC0.
    - apply sim_strict_inv_call' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto. eapply IHSIM; eauto.
      ginit. guclo sim_strict_bindC_spec. econs.
      + gfinal. right. eapply sim_strict_refl.
      + i. inv REL. gfinal. right. apply EQVTGT0.
    - apply sim_strict_inv_tau in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_tau' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto.
    - apply sim_strict_inv_choose in EQVSRC. des. subst.
      specialize (EQVSRC0 x). des. destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_choose' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto. i. specialize (EQVTGT0 x). des; eauto.
    - apply sim_strict_inv_take in EQVSRC. des. subst.
      destruct sti_tgt. econs. i. specialize (EQVSRC0 x). des. eauto.
    - apply sim_strict_inv_take' in EQVTGT. des. subst.
      specialize (EQVTGT0 x). des. destruct sti_src. econs; eauto.
    - apply sim_strict_inv_update in EQVSRC. des. subst.
      destruct sti_tgt. econs; eauto.
    - apply sim_strict_inv_update' in EQVTGT. des. subst.
      destruct sti_src. econs; eauto.
    - destruct sti_src, sti_tgt. econs; eauto. econs; eauto.
  Qed.

  Lemma sim_strictC_spec: forall wf le fl_src fl_tgt,
      sim_strictC <9= gupaco8 (@_sim_itree Σ wf le fl_src fl_tgt) (cpn8 (@_sim_itree Σ wf le fl_src fl_tgt)).
  Proof.
    intros. gclo. econs; eauto using sim_strictC_compatible.
    eapply sim_strictC_mon, PR; eauto with paco.
  Qed.

  (** **)
  
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
    - right; right; left. exists X, c, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - right; right; right; left. exists X, s, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
    - right; right; right; right. exists X, e, k. unfold trigger. rewrite bind_vis.
      repeat f_equal. extensionality x. rewrite bind_ret_l. eauto.
  Qed.

  Definition hp_reconf_eq cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      <<RELr: Own fr ⊢ #=> Own (fr' ⋅ cr)>> /\      
      <<STR: str' = str>>.
  
  Definition hp_reconf_equiv cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      hp_reconf_eq cr (str,fr) (str',fr')
      \/
      (exists st (mr mr': Σ),
       <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
       <<STR: str = Any.pair st mr↑>> /\
       <<STR': str' = Any.pair st mr'↑>>).

  Definition hp_reconf_rel R (eqv: Σ -> _) cr : relation (Any.t * (Σ * R)) :=
    fun '(str,(fr,x)) '(str',(fr',x')) =>
      eqv cr (str,fr) (str',fr') /\ x = x'.

  Lemma hp_reconf_equiv_strong
    cr str str' (fr fr': Σ)
    (EQV: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    (hp_reconf_eq cr (str,fr) (str',fr') /\
     <<FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑>>)
    \/
    (exists st (mr mr': Σ),
     <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
     <<STR: str = Any.pair st mr↑>> /\
     <<STR': str' = Any.pair st mr'↑>>).
  Proof.
    ss. des; subst; [|right]; esplits; eauto.
    destruct (classic (exists stx (mrx:Σ), str = Any.pair stx mrx↑)); eauto.
    des. subst. right. esplits; eauto.
    eapply own_ctx with (ctx := mrx) in RELr. revert RELr. r_solve. i.
    rewrite-> URA.add_comm, (URA.add_comm fr' mrx). eauto.
  Qed.
  
  Lemma hp_reconf_fail
    r R RR str i i'
    (FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑)
    :
    paco4 _sim_strict r R RR
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i mr)
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i' mr).
  Proof.
    destruct (Any.split str) eqn:STR; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn:T0; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    apply Any.split_pair in STR. apply Any.downcast_upcast in T0.
    exfalso. eapply FAIL. des; subst. eauto.
  Qed.

  Lemma handle_Guarantee_reconf
    P str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_equiv cr)
      (str, handle_Guarantee P fr)
      (str', handle_Guarantee P fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget, mput.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1, c2⋅cr).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
      iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. right. esplits; eauto.
    r_solve. eauto.
  Qed.

  Lemma handle_Guarantee_reconf_true
    str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_eq cr)
      (str, handle_Guarantee True fr)
      (str', handle_Guarantee True fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget, mput.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1⋅cr, c2).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]".
      rewrite -URA.add_assoc (URA.add_comm cr c2) URA.add_assoc.
      iSplitL "X"; eauto. iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. split; eauto.
  Qed.
  
  Lemma interp_hp_reconf
    R itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel R hp_reconf_equiv cr)
      (str, interp_hp itrH fr)
      (str', interp_hp itrH fr').
  Proof.
    revert_until I. ginit. gcofix CIH; i.
    assert (CASE := case_itrH _ itrH). des; subst.
    - rewrite !interp_hp_ret.
      gstep. econs. rr. esplits; eauto.
    - rewrite-> !interp_hp_tau.
      grind; gstep; econs; i. eauto 10 with paco.
    - rewrite-> !interp_hp_bind, !interp_hp_Assume.
      unfold handle_Assume, assume, mget, mput.
      grind; gstep; econs; i. exists x.
      grind; gstep; econs; i.
      grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
      { gfinal. right. apply hp_reconf_fail. eauto. }
      rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
      grind; gstep; econs; i. eexists.
      { eapply own_ctx with (ctx := x) in RELr0. rewrite !URA.add_assoc in RELr0.
        eapply own_wf in RELr0; eauto. eapply URA.wf_mon; eauto. }
      grind; gstep; econs; i. eexists. { eauto. }
      grind; gstep; econs; i.
      gfinal. left. eapply CIH. right. esplits; eauto.
      { eapply own_ctx with (ctx := x) in RELr0.
        rewrite !URA.add_assoc in RELr0. eauto using own_wf. }
    - rewrite-> !interp_hp_bind, !interp_hp_Guarantee. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf. eauto. }
      i. grind; gstep; econs; i.
      gfinal. left. eapply CIH. destruct v0, v0'. rr in REL. des; subst. ss.
    - rewrite-> !interp_hp_bind, !interp_hp_call. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf_true. eauto. }
      i. destruct v0, v0', c. repeat (rr in REL; des; subst).
      repeat (grind; gstep; econs; i).
      gfinal. left. eapply CIH. left. s. eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggerp.
      destruct s. unfold handle_sE_tgt, pupdate.
      repeat (grind; gstep; econs; i).
      grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
      { rewrite !Any.pair_split. grind.
        gfinal. left. eapply CIH. right. esplits; eauto. }
      gfinal. left. eapply CIH.
      destruct (Any.split str) as [[]|] eqn: STR.
      { left. s. esplits; eauto. }
      left. s. esplits; eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggere.
      destruct e.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + repeat (grind; gstep; econs; i). eauto 10 with paco.
  Qed.

  Lemma hp_fun_tail_reconf
    str str' (fr fr' cr: Σ) x
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
      (str, hp_fun_tail (fr,x))
      (str', hp_fun_tail (fr',x)).
  Proof.
    ginit. unfold hp_fun_tail. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst).
    eauto with paco.
  Qed.

  Lemma interp_hp_body_reconf
    itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
      (str, interp_hp_body itrH fr)
      (str', interp_hp_body itrH fr').
  Proof.
    ginit. unfold interp_hp_body.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst); cycle 1.
    - gfinal. right. eapply hp_fun_tail_reconf. right. esplits; eauto.
    - gfinal. right. eapply hp_fun_tail_reconf. left. esplits; eauto.
      rr. esplits; eauto.
  Qed.

  Lemma interp_strict_inline_src
    itrH ktrH st (fr mr: Σ)
    :
    sim_strict Any.t eq
      (Any.pair st (fr ⋅ mr)↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (ε,x));; interp_hp_body (ktrH rv) rr)
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr).
  Proof.
    ginit. guclo sim_strict_transC_spec. econs; cycle 1.
    { gfinal. right. eapply interp_hp_body_reconf with (fr := (ε:Σ)) (cr:=(ε:Σ)).
      right. esplits; eauto. instantiate (1:= fr ⋅ mr). r_solve. eauto. }
    { i. destruct PR. subst. eauto. }
    unfold interp_hp_body. rewrite !interp_hp_bind.
    grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. apply sim_strict_refl. }
    i. depdes REL. rewrite-> interp_hp_bind, interp_hp_Guarantee.
    destruct v0' as [fr' st']. unfold hp_fun_tail at 1. grind.
    unfold handle_Guarantee, mget, mput, guarantee, sGet, sPut.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, ε, c1 ⋅ c2).
    grind; gstep; econs; i.
    ss. destruct (Any.split st0') eqn: ST0'; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn: T0; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    apply Any.split_pair in ST0'. rr in ST0'. subst.
    apply Any.downcast_upcast in T0. rr in T0. subst.
    grind; gstep; econs; i. eexists. { r_solve. eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    repeat (grind; gstep; econs; i).
    grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    gfinal. right. eapply interp_hp_body_reconf with (cr:=(ε:Σ)).
    right. esplits; eauto. r_solve. eauto.
  Qed.

  Lemma interp_strict_inline_tgt
    itrH ktrH st (fr mr fr' mr': Σ)
    (RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr'))
    :
    sim_strict Any.t eq
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr)
      (Any.pair st mr'↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (fr',x));; interp_hp_body (ktrH rv) rr).
  Proof.
    ginit. unfold interp_hp_body. rewrite-> !interp_hp_bind. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf with (cr:=fr').
      right. esplits; eauto. r_solve.
      rewrite (URA.add_comm mr' fr'). eauto. }
    i. rewrite-> !interp_hp_bind, interp_hp_Guarantee. unfold hp_fun_tail. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      destruct v0. ss. des; subst; eauto.
      right. esplits; eauto. }
    i. grind; gstep; econs; i.
    destruct v0. rr in REL; des; subst. simpl. destruct v1, v0'.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right.  eapply interp_hp_reconf with (cr:=c2).
      s in REL0; des; subst. left. s. esplits; eauto.
      rewrite URA.add_comm. eauto. }
    i. grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      r in REL1. des; subst. eauto. }
    i. gstep; econs. rr in REL1. des; subst.
    destruct v0, v0'. s in REL2; des; subst. eauto. 
  Qed.


  (*** ****)
  
  
  Variant interp_inv: Σ -> Any.t * Any.t -> Prop :=
    | interp_inv_intro
        (ctx mr_src mr_tgt: Σ) st_src st_tgt mr
        (WF: URA.wf (ctx ⋅ mr_src))
        (* (MRS: Own (ctx ⋅ mr_src) ⊢ #=> Own (ctx ⋅ mr ⋅ mr_tgt)) *)
        (MRS: Own mr_src ⊢ #=> Own (mr ⋅ mr_tgt))
        (MR: Own mr ⊢ #=> I st_src st_tgt)
      :
      interp_inv ctx (Any.pair st_src mr_src↑, Any.pair st_tgt mr_tgt↑)
  .
  
  Lemma hpsim_adequacy:
    forall
      (fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) 
      (FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
      (FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
      p_src p_tgt st_src st_tgt itr_src itr_tgt
      (ctx mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim_body p_src p_tgt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
      (WF: URA.wf (ctx ⋅ fr_src ⋅ mr_src))
      (FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (fmr ⋅ fr_tgt ⋅ mr_tgt)),
    @sim_itree Σ interp_inv (fun _ _ => True) fl_src0 fl_tgt0 p_src p_tgt ctx
      (Any.pair st_src mr_src↑, interp_hp_body itr_src fr_src)
      (Any.pair st_tgt mr_tgt↑, interp_hp_body itr_tgt fr_tgt).
  Proof.
    i. apply hpsim_add_dummy in SIM.
    revert_until I. ginit. gcofix CIH. i.
    remember (st_src, itr_src). remember (st_tgt, itr_tgt).
    move SIM before FLT. revert_until SIM.
    punfold SIM. induction SIM; i; clarify.
    - unfold interp_hp_body, hp_fun_tail, handle_Guarantee, guarantee, mget, mput.
      steps. force_l. instantiate (1 := (c0 ⋅ c1, ε, fmr ⋅ c)). steps.
      force_l.
      { 
        rewrite FMR. 
        iIntros "H". iMod "H".
        rewrite <- URA.add_assoc. 
        iDestruct "H" as "[H H0]".
        iPoseProof (x with "H0") as "H0".
        iMod "H0".
        iModIntro. r_solve.
        iDestruct "H0" as "[H0 H1]".
        iSplitR "H1"; et.
        iCombine "H0 H" as "H". et.
      } 
      steps. force_l. 
      { iIntros "H". et. } 
      steps. econs. esplits; et. econs; esplits; et.
      instantiate (1:= ctx).
      {
        eapply own_ctx in FMR, x. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
        rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
        eapply own_wf in x; et.
        replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
        eapply URA.wf_mon; et.
      }.
    - unfold interp_hp_body, hp_fun_tail, handle_Guarantee, mget, mput, guarantee.
      hexploit INV. i.
      eapply iProp_sepconj in H0; et. des. rename rq into fr. rename rp into mr.
      steps. unfold handle_Guarantee, guarantee, mget, mput. steps_safe.
      (* force_l. instantiate (1:= (ε, fr_src, mr_src)). steps_safe. *)
      force_l. instantiate (1:= (c0, fr ⋅ c1, mr ⋅ c)). steps_safe.
      rename c1 into frt. rename c into mrt.
      force_l.
      { admit. }
      steps_safe. 
      force_l; et.
      steps_safe. eapply safe_sim_sim; econs. esplits; i.
      { 
        econs.
        { instantiate (1:= ctx ⋅ fr ⋅ frt). admit. }
        { instantiate (1:= mr). admit. }
        { admit. }
      }
      steps.
      inv WF0. eapply H; [| |et|et| |].
      (* expect w1 = ctx ⋅ fr ⋅ frt *)
      all: admit.
    - admit.
    - exploit IHSIM; eauto. i.
      rewrite-> interp_hp_body_bind, interp_hp_call.
      unfold handle_Guarantee, mget, mput, guarantee. 
      steps. force_l. instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
      steps. force_l. { r_solve; et. }
      steps. force_l; et. steps.
      {	instantiate (1:= interp_hp_fun f).
  rewrite alist_find_map. rewrite FUN. et. }
      guclo sim_strictC_spec. econs; eauto.
      + apply interp_strict_inline_src.
      + apply sim_strict_refl.
    - exploit IHSIM; eauto. i.
      rewrite-> interp_hp_body_bind, interp_hp_call.
      unfold handle_Guarantee, mget, mput, guarantee.
      steps.
      {	instantiate (1:= interp_hp_fun f).
  rewrite alist_find_map. rewrite FUN. et. }
      guclo sim_strictC_spec. econs; eauto.
      + apply sim_strict_refl.      
      + apply interp_strict_inline_tgt.
        { iIntros "H". iPoseProof (x with "H") as "H". iMod "H".
          iDestruct "H" as "[[X Y] Z]". iModIntro. iSplitL "Y"; eauto. }
    -








      

      

      
      
      unfold interp_hp_fun.
      
      
      rewrite !bind_bind. 
    unfold interp_hp_fun.
    gclo. eapply compatible'8_companion; eauto with paco.
    { eapply compat8_compatible'. apply inlineSrcC_compatible. }	
    econs. { grind. }
    specialize (IHSIM st_src0 st_tgt0 ((f varg) >>= k_src) itr_tgt ctx (fr_src ⋅ mr_src) mr_tgt ε fr_tgt).
    rewrite interp_hp_fun_bind in IHSIM.
    rewrite bind_bind in IHSIM.
    (* unfold interp_hp_fun in IHSIM. *)
    eapply IHSIM; r_solve; et.
  }



  - unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee.
    steps.
    force_l. instantiate (1 := (c0 ⋅ c1, ε, fmr ⋅ c)). steps.
    unfold guarantee. force_l.
    { 
      rewrite FMR. 
      iIntros "H". iMod "H".
      rewrite <- URA.add_assoc. 
      iDestruct "H" as "[H H0]".
      iPoseProof (x with "H0") as "H0".
      iMod "H0".
      iModIntro. r_solve.
      iDestruct "H0" as "[H0 H1]".
      iSplitR "H1"; et.
      iCombine "H0 H" as "H". et.
    } 
    steps. force_l. 
    { iIntros "H". et. } 
    (* rr. uipropall. }  *)
    steps. econs. esplits; et. econs. esplits; et.
    instantiate (1:= ctx).
    {
      eapply own_ctx in FMR, x. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
      rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
      eapply own_wf in x; et.
      replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
      eapply URA.wf_mon; et.
    }

  - unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee.
    hexploit INV. i.
    eapply iProp_sepconj in H; et. 
    (* 2: { admit. } *)
    des.
    rename rq into fr. rename rp into mr.
    steps.
    unfold handle_Guarantee, mget, mput. steps_safe.
    force_l.
    instantiate (1:= (c0, ε, fr ⋅ c1 ⋅ mr ⋅ c)).
    steps_safe.
    unfold guarantee. force_l.
    { admit. }
      (* iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
      rewrite <- URA.add_assoc.
      iDestruct "H" as "[H H0]". 
      iPoseProof (H with "H") as "H".
      replace (c0 ⋅ (fr ⋅ c1) ⋅ (mr ⋅ c)) with (mr ⋅ fr ⋅ (c0 ⋅ c1 ⋅ c)). 2: { r_solve. }
      iPoseProof (_GUARANTEE with "H0") as "H0".
      iSplitL "H"; et. *)
    steps_safe. force_l.
    { et. }
    steps_safe. eapply safe_sim_sim; econs; esplits; i.
    { 
      econs. esplits; et.
      { instantiate (1:= ctx). admit. }
      { admit. }
      (* { iIntros "H". iPoseProof (H0 with "H") as "H". et. } *)
    }
    inv WF0. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee in K.
    steps.
    hexploit K; swap 1 2. 
    { 
      instantiate (1:= st_tgt). instantiate (1:= st_src).
      iIntros "[H1 H2]".
      iPoseProof (H1 with "H1") as "H1". 
      iPoseProof (MR with "H2") as "H2".
      iSplitL "H2"; et.
    }
    { admit. }
    i. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    eapply IH; et.
    {
      
    }
  - steps. hexploit K; et. i. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    eapply IH; et.
  - admit. (* need to clarify the relation between fl_src ~ fl_src0 *)
  - admit. 
  - steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
  - steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
  - steps. force_l. steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
  - steps. hexploit K; et. i. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    eapply IH; et.
  - steps. hexploit K; et. i. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    eapply IH; et.
  - steps. force_r. steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
  - steps. rewrite ! Any.pair_split. rewrite RUN. s.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    exploit IHSIM; et.
  - steps. rewrite ! Any.pair_split. rewrite RUN. s.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    exploit IHSIM; et.
  - steps. rewrite interp_hp_Assume. unfold handle_Assume, mget, mput. steps.  
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    hexploit K; et.
    { 
      instantiate (1:= x ⋅ fmr).
      iIntros "[H H0]". 
      iPoseProof (_ASSUME0 with "H") as "H".
      iPoseProof (CUR with "H0") as "H0".
      iMod "H0". iModIntro. iFrame. 
    }
    i. des. eapply IH; et.
    rewrite <- ! URA.add_assoc.
    {
      iIntros "[H H0]".
      iSplitL "H"; et.
      iPoseProof (FMR0 with "H0") as "H".
      rewrite URA.add_assoc. et.
    }
  -	steps. rewrite interp_hp_Assume. 
    hexploit CUR. i.
    apply iProp_sepconj in H. 2: { admit. }
    des. rename rq into fmr0.
    unfold handle_Assume, mget, mput, assume. steps.
    force_r.
    instantiate (1:= rp).
    steps. force_r.
    { 
      clear -H FMR0.
      assert (URA.wf (fmr ⋅ fr_tgt ⋅ mr_tgt)). { admit. }
      assert (URA.wf (fmr ⋅ fr_tgt ⋅ mr_tgt ⋅ ε)). { admit. }
      eapply own_ctx with (ctx := (fr_tgt ⋅ mr_tgt)) in H.
      uipropall.
      eapply H in H0. 2: { admit. }
      des.
      eapply URA.wf_extends in H0. admit.
      specialize (H2 ε H1).
      admit.
    }

    steps. force_r; et. 
    steps.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    hexploit K; et. 
    {
      iIntros "H". iPoseProof (H1 with "H") as "H". et.
    }
    i. des. 
    eapply IH; et.
    {
      iIntros "H". 
      iPoseProof (FMR0 with "H") as "H". iMod "H". rewrite <- ! URA.add_assoc.
      iDestruct "H" as "[H H0]".
      replace (fmr0 ⋅ (rp ⋅ (fr_tgt ⋅ mr_tgt))) with ((rp ⋅ fmr0) ⋅ (fr_tgt ⋅ mr_tgt)). 2: { r_solve. }
      iPoseProof (H with "H") as "H". iMod "H".
      iSplitL "H"; et.
    } 
  - steps. rewrite interp_hp_Guarantee.
    unfold handle_Guarantee, mget, mput, guarantee. steps.
    hexploit CUR. i.
    apply iProp_sepconj in H.  2: { admit. }
    des. rename rq into fmr0.
    force_l.
    instantiate (1:= (rp, fr_tgt, fmr0 ⋅ mr_tgt)).
    steps. force_l.
    {
      iIntros "H". 
      iPoseProof (FMR0 with "H") as "H". iMod "H".
      rewrite <- URA.add_assoc.
      iDestruct "H" as "[H H0]". 
      iPoseProof (H with "H") as "H". iMod "H".
      replace (rp ⋅ fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (rp ⋅ fmr0 ⋅ (fr_tgt ⋅ mr_tgt)). 2: { r_solve. }
      iSplitL "H"; et.
    }
    steps. force_l; et.
    steps.
    hexploit K; et.
    {
      iIntros "H". iPoseProof (H1 with "H") as "H". et.	
    }
    i. des.
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
    eapply IH; et.
    {
      replace (fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve.
      et.
    }
  - steps. rewrite interp_hp_Guarantee. unfold handle_Guarantee, mget, mput, guarantee. steps. 
    unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.			
    hexploit K; et.
    { 
      instantiate (1:= (c0 ⋅ fmr)).
      iIntros "[H H0]".
      iPoseProof (x0 with "H") as "H".
      iPoseProof (CUR with "H0") as "H0".
      iSplitL "H"; et. 	
    } 
    i. des.
    eapply IH; et.
    {
      iIntros "H".
      iPoseProof (FMR0 with "H") as "H". iMod "H".
      rewrite <- URA.add_assoc. 
      iDestruct "H" as "[H H0]".
      iPoseProof (x with "H0") as "H0". iMod "H0".
      replace (c0 ⋅ fmr ⋅ c1 ⋅ c) with (fmr ⋅ (c0 ⋅ c1 ⋅ c)). 2: { r_solve. }
      iSplitL "H"; et.
    }
  - gstep. econs. gfinal. left. eapply CIH; et. 
  
    (* (fr_src ⋅ mr_src) -> fmr in 'SIM' *)
Admitted.





  Inductive hpsim_adeq_rel : Σ -> (itree hAGEs Any.t)-> (itree Es (Σ * Any.t)) -> Σ -> (itree hAGEs Any.t)-> (itree Es (Σ * Any.t)) -> Prop :=
  | hpsim_adeq_base (fr fr': Σ) st st' 
    : hpsim_adeq_rel fr (Ret st) (@interp_hp_fun Σ Any.t (Ret st) fr)
                     fr' (Ret st') (@interp_hp_fun Σ Any.t (Ret st') fr')

  | hpsim_adeq_seq itrH0 itrH1 itrL0 itrL1 itrH0' itrH1' itrL0' itrL1' (fr fr': Σ)
      (ITR0: itrL0 = @interp_hp_fun Σ Any.t itrH0)
      (ITR0': itrL0' = @interp_hp_fun Σ Any.t itrH0')
      (ADEQ: forall st st',
              hpsim_adeq_rel ε (itrH1 st) (itrL1 st (ε:Σ)) 
                             ε (itrH1' st') (itrL1' st' (ε:Σ)))
    : hpsim_adeq_rel fr (st0 <- itrH0;; itrH1 st0) ('(_, st1) <- (itrL0 fr);; (itrL1 st1 ε))
                     fr' (st0 <- itrH0';; itrH1' st0) ('(_, st1) <- (itrL0' fr');; (itrL1' st1 ε))
  .


  Lemma hpsim_adequacy
      (fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) 
      (FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
      (FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
      p_src p_tgt st_src st_tgt itrH_src itrH_tgt itrL_src itrL_tgt
      (ctx mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim p_src p_tgt (st_src, itrH_src) (st_tgt, itrH_tgt) fmr)
      (WF: URA.wf (ctx ⋅ fr_src ⋅ mr_src))
      (FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (fmr ⋅ fr_tgt ⋅ mr_tgt))
      (REL: hpsim_adeq_rel fr_src itrH_src itrL_src fr_tgt itrH_tgt itrL_tgt)
    :

      @sim_itree Σ (mk_inv I) eq fl_src0 fl_tgt0 p_src p_tgt ctx 
      (Any.pair st_src mr_src↑, itrL_src >>= (fun r => Ret (snd r)))
      (Any.pair st_tgt mr_tgt↑, itrL_tgt >>= (fun r => Ret (snd r))).
  Proof.
    revert_until FLT.
    ginit. gcofix CIH. i.
    move REL before CIH. revert_until REL. induction REL.
    { i. punfold SIM. inv SIM; (try rewrite ! bind_trigger in H3); (try rewrite ! bind_trigger in H5); clarify.
      -	unfold interp_hp_fun, handle_Guarantee, mput, mget, guarantee. 
        steps. force_l. instantiate (1:= (c0 ⋅ c1, ε, fmr ⋅ c)).
        steps. force_l.
        {  
          rewrite FMR. 
          iIntros "H". iMod "H".
          rewrite <- URA.add_assoc. 
          iDestruct "H" as "[H H0]".
          iPoseProof (x with "H0") as "H0". iMod "H0". 
          iModIntro. r_solve.
          replace (c0 ⋅ c1 ⋅ fmr ⋅ c) with (c0 ⋅ c1 ⋅ c ⋅ fmr); r_solve.
          iSplitR "H"; et.
        }
        steps. force_l; et.
        steps.
        econs; esplits; et. econs; esplits; et.
        {  
          eapply own_ctx in FMR. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
          rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
          eapply own_ctx, own_wf in x; et.
          replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
          eapply URA.wf_mon; et.
        }
      - pclearbot. punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H3); (try rewrite ! bind_trigger in H5); clarify.
        unfold interp_hp_fun, handle_Guarantee, mput, mget, guarantee. steps.
        force_l. instantiate (1:= (c0 ⋅ c1, ε, fmr ⋅ c)).
        steps. force_l.
        {  
          rewrite FMR. 
          iIntros "H". iMod "H".
          rewrite <- URA.add_assoc. 
          iDestruct "H" as "[H H0]".
          iPoseProof (x with "H0") as "H0". iMod "H0". 
          iModIntro. r_solve.
          replace (c0 ⋅ c1 ⋅ fmr ⋅ c) with (c0 ⋅ c1 ⋅ c ⋅ fmr); r_solve.
          iSplitR "H"; et.
        }
        steps. force_l; et.
        steps.
        econs; esplits; et. econs; esplits; et.
        {  
          eapply own_ctx in FMR. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
          rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
          eapply own_ctx, own_wf in x; et.
          replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
          eapply URA.wf_mon; et.
        }
    }

    i.
    remember (st_src, ` st0 : Any.t <- itrH0;; itrH1 st0) as sti_src.
    remember (st_tgt, ` st0 : Any.t <- itrH0';; itrH1' st0) as sti_tgt.
    move SIM before CIH. revert_until SIM.
    induction SIM using hpsim_ind; i. 
    (* ; clarify; unfold interp_hp_fun, handle_Guarantee, mget, mput. *)
    - 
      steps.
      ides itrH0; ides itrH0'; revert H1 H2; try rewrite bind_vis; grind.
      unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee.
      steps. force_l.
      instantiate (1 := (c0 ⋅ c1, ε, fmr ⋅ c)).
      steps. force_l.
      {
        admit.
      }
      steps. force_l; et. steps.
      specialize (ADEQ r0 r1). depdes ADEQ; cycle 1.
      {
        eapply H.
        { rewrite <- H1. rewrite <- H2. et. }
        admit. admit.
      }
      
      rewrite <- x1. rewrite <- x.
      unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee.
      steps. force_l.
      instantiate (1 := (c3 ⋅ c4, ε, fmr ⋅ c2 )).
      steps. force_l.
      {
        admit.
      } 
      steps. force_l; et.
      steps.
      econs. esplits; et.
      {
        econs. esplits; et.	admit.
      }
      rewrite <- H1 in x2.
      rewrite <- H2 in x0.
      clarify.
      
    - steps. move K at bottom.
      ides itrH0; ides itrH0'; clarify.




      {
          
      }
        admit. steps. 
        force_l. steps. admit. steps. eapply H; et.


    unfold interp_hp_fun, handle_Guarantee, mget, mput.
      steps.

      force_l. instantiate (1 := (c0 ⋅ c1, ε, fmr ⋅ c)). steps.
      unfold guarantee. force_l.
      { 
        rewrite FMR. 
        iIntros "H". iMod "H".
        rewrite <- URA.add_assoc. 
        iDestruct "H" as "[H1 H2]".
        iPoseProof (_GUARANTEE with "H2") as "H2".
        iMod "H2".
        iModIntro. r_solve.
        iDestruct "H2" as "[H3 H4]".
        iSplitR "H4"; et.
        iCombine "H3 H1" as "H". et.
      } 
      steps. force_l. 
      { iIntros "H". et. } 
      steps. econs; esplits; et.
      + econs. esplits; et.
        eapply own_ctx with (ctx:= ctx ⋅ fmr) in _GUARANTEE.
        eapply own_ctx with (ctx:= ctx) in FMR.
        rewrite <- URA.add_assoc in WF. eapply own_wf in FMR; et.
        rewrite ! URA.add_assoc in FMR.
        rewrite URA.add_assoc in _GUARANTEE.
        eapply own_wf in _GUARANTEE; et.
        replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ (fmr ⋅ c) ⋅ c0 ⋅ c1) in _GUARANTEE. 2: { r_solve. }
        do 2 eapply URA.wf_mon; et.
    - hexploit INV. i.
      eapply iProp_sepconj in H. et.
      des.
      rename rq into fr. rename rp into mr.
      steps.
      unfold handle_Guarantee, mget, mput. steps_safe.
      force_l.
      instantiate (1:= (c0, fr ⋅ c1, mr ⋅ c)).
      rename c1 into fr_tgt'. rename c into mr_tgt'.
      steps_safe.
      unfold guarantee. force_l.
      { 
        iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
        rewrite <- URA.add_assoc.
        iDestruct "H" as "[H H0]". 
        iPoseProof (H with "H") as "H".
        replace (c0 ⋅ (fr ⋅ fr_tgt') ⋅ (mr ⋅ mr_tgt')) with (mr ⋅ fr ⋅ (c0 ⋅ fr_tgt' ⋅ mr_tgt')). 2: { r_solve. }
        iPoseProof (_GUARANTEE with "H0") as "H0".
        iSplitL "H"; et.
      }
      steps_safe. force_l.
      { et. }
      steps_safe. eapply safe_sim_sim; econs; i.
      exists (fr ⋅ ctx). esplits.
      { 
        econs. esplits; et.
        {
          eapply own_ctx with (ctx:= ctx ⋅ fmr) in _GUARANTEE.
          eapply own_ctx with (ctx:= ctx) in FMR.
          rewrite <- URA.add_assoc in WF. eapply own_wf in FMR; et.
          rewrite ! URA.add_assoc in FMR.
          rewrite URA.add_assoc in _GUARANTEE.
          eapply own_wf in _GUARANTEE; et.
          rewrite URA.add_comm in _GUARANTEE. rewrite URA.add_assoc in _GUARANTEE.
          eapply own_ctx in H. eapply own_wf in H; et.
          replace (c0 ⋅ fr_tgt' ⋅ mr_tgt' ⋅ ctx ⋅ (mr ⋅ fr)) with (fr ⋅ ctx ⋅ mr ⋅ mr_tgt' ⋅ (c0 ⋅ fr_tgt')) in H; r_solve.
          eapply URA.wf_mon; et.
        } 
        iIntros "H". iPoseProof (H0 with "H") as "H". et.
      }
      i. inv WF0. des.
      unfold interp_hp_fun, handle_Guarantee, mget, mput, guarantee in K.
      hexploit K; swap 1 2.
      { 
        iIntros "[H1 H2]".
        iPoseProof (H1 with "H1") as "H1". 
        iPoseProof (MR with "H2") as "H2".
        iSplitL "H2"; et.
      }
      {
        eapply own_ctx in MRS. eapply own_wf in MRS; et.
        replace (fr ⋅ ctx ⋅ (mr0 ⋅ mr_tgt0)) with (fr ⋅ mr0 ⋅ (ctx ⋅ mr_tgt0)) in MRS; r_solve.
        eapply URA.wf_mon; et.				
      }
      i. des.
      steps. 
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IH; et.
      { 
        iIntros "[H H0]".
        iPoseProof (MRS with "H0") as "H0".
        replace (fr ⋅ mr0 ⋅ fr_tgt' ⋅ mr_tgt0) with (fr ⋅ fr_tgt' ⋅ (mr0 ⋅ mr_tgt0)). 2: { r_solve. }  
        iSplitL "H"; et.
      }
      {
        clear IH.

        admit.	
      }
    - steps. hexploit K; et. i. des.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IH; et.
    - steps. unfold handle_Guarantee, mget, mput, guarantee. steps.
      force_l.
      instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
      steps. force_l. { r_solve. et. }
      steps. force_l; et. 
      steps. 
      { 
        instantiate (1:= interp_hp_fun f).
        rewrite alist_find_map. rewrite FUN. et.
      }
      unfold interp_hp_fun, interp_hp_fun. steps.
      do 3 rewrite <- bind_bind in *.
      (* set (` x : Σ * Any.t <- interp_hp (f varg) ε;; (let '(_, x0) := x in Ret x0)) as itr. *)
      (* assert () *)
      set ((` x : Σ * Any.t <- (` x : Any.t <- (` x : Σ * Any.t <- interp_hp (f varg) ε;; (let '(_, x0) := x in Ret x0));; (tau;; Ret (fr_src, x)));;
      interp_hp (k_src x.2) x.1)) as itr0.
      set (interp_hp (` x : Any.t <- (f varg);; k_src x) fr_src) as itr1.
      assert (itr0 = itr1 ). {
        unfold itr0, itr1. grind. rewrite interp_hp_bind.	
      admit. }
      rewrite H. unfold itr1.
      (* assert (itr_src = interp_hp (` x : Any.t <- (f varg);; ` x : Σ * Any.t <- (k_src x)) fr_src).
      { unfold itr_src. grind. }
      rewrite <- interp_hp_bind. *)
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IHSIM; et.
  
    - admit. 
    - steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
    - steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
    - steps. force_l. steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
    - steps. hexploit K; et. i. des.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IH; et.
    - steps. hexploit K; et. i. des.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IH; et.
    - steps. force_r. steps. unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
    - steps. rewrite ! Any.pair_split. rewrite RUN. s.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IHSIM; et.
    - steps. rewrite ! Any.pair_split. rewrite RUN. s.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IHSIM; et.
    - steps. rewrite interp_hp_Assume. unfold handle_Assume, mget, mput. steps.  
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      (* hexploit K. *)
      hexploit (K (x ⋅ fmr)). et.
      { 
        eapply own_ctx in FMR0. eapply own_wf in FMR0; cycle 1.
        { rewrite URA.add_assoc; et.  }
        { rewrite ! URA.add_assoc in FMR0. do 2 eapply URA.wf_mon; et.  }
      }
      et.
      {
        iIntros "[H H0]". 
        iPoseProof (_ASSUME0 with "H") as "H".
        iPoseProof (CUR with "H0") as "H0".
        iMod "H0". iModIntro. iFrame. 
      }
      i. des. eapply IH; et.
      {
        rewrite <- ! URA.add_assoc.
        iIntros "[H H0]".
        iSplitL "H"; et.
        iPoseProof (FMR0 with "H0") as "H".
        rewrite URA.add_assoc. et.
      }
      {
        clear IH. admit.
      }
    -	steps. rewrite interp_hp_Assume. 
      hexploit CUR. i.
      apply iProp_sepconj in H.
      des. rename rq into fmr0.
      unfold handle_Assume, mget, mput, assume. steps.
      force_r.
      instantiate (1:= rp).
      steps. force_r.
      { 
        eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
        replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
        eapply own_ctx in H. eapply own_wf in H; et.
        replace (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ (rp ⋅ fmr0)) with (rp ⋅ fr_tgt ⋅ mr_tgt ⋅ (ctx ⋅ fmr0)) in H; r_solve.
        eapply URA.wf_mon; et.	
      }
      steps. force_r; et. 
      steps.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      hexploit (K fmr0).
      {
        eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0; et. eapply own_wf in FMR0; et.
        replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt )) with (fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) in FMR0; r_solve.
        eapply URA.wf_mon in FMR0. eapply own_wf in H; et.
        rewrite URA.add_comm in H. eapply URA.wf_mon; et.
      }
      { 
        iIntros "H". iPoseProof (H1 with "H") as "H". et.
      }
      i. des.
      eapply IH; et.
      {
        clear IH.
        iIntros "H". iPoseProof (FMR0 with "H") as "H".
        rewrite <- URA.add_assoc. iMod "H". iDestruct "H" as "[H H0]".
        r_solve. rewrite <- URA.add_assoc. iSplitL "H"; et.
        iPoseProof (H with "H") as "H". iMod "H".
        iDestruct "H" as "[H H0]". iSplitL "H0"; et.  				
      }
    - steps. rewrite interp_hp_Guarantee.
      unfold handle_Guarantee, mget, mput, guarantee. steps.
      hexploit CUR. i.
      apply iProp_sepconj in H.
      des. rename rq into fmr0.
      force_l.
      instantiate (1:= (rp, fr_tgt, fmr0 ⋅ mr_tgt)).
      steps. force_l.
      {
        iIntros "H". 
        iPoseProof (FMR0 with "H") as "H". iMod "H".
        rewrite <- URA.add_assoc.
        iDestruct "H" as "[H H0]". 
        iPoseProof (H with "H") as "H". iMod "H".
        replace (rp ⋅ fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (rp ⋅ fmr0 ⋅ (fr_tgt ⋅ mr_tgt)). 2: { r_solve. }
        iSplitL "H"; et.
      }
      steps. force_l; et.
      steps.
      hexploit (K fmr0); et.
      {
        eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
        replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
        eapply own_ctx, own_wf in H; et.
        rewrite URA.add_assoc in H.
        eapply URA.wf_mon. rewrite URA.add_comm. et.
      }
      {
        iIntros "H". iPoseProof (H1 with "H") as "H". et.	
      }
      i. des.
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
      eapply IH; et.
      {
        replace (fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve.
        et.
      }
      {
        clear IH. 
        eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
        replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
        eapply own_ctx, own_wf in H; et.
        replace (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ (rp ⋅ fmr0)) with (ctx ⋅ fr_tgt ⋅ fmr0 ⋅ mr_tgt ⋅ rp) in H; r_solve.
        eapply URA.wf_mon; et.
      }
    - steps. rewrite interp_hp_Guarantee. unfold handle_Guarantee, mget, mput, guarantee. steps. 
      unfold interp_hp_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.			
      hexploit (K (c0 ⋅ fmr)). 
      {
        eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
        rewrite <- URA.add_assoc in FMR0. rewrite URA.add_assoc in FMR0.
        eapply own_ctx, own_wf in x; et.
        replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (c0 ⋅ fmr ⋅ (ctx ⋅ c1 ⋅ c)) in x; r_solve.
        eapply URA.wf_mon; et.
      }
      { 
        iIntros "[H H0]".
        iPoseProof (x0 with "H") as "H".
        iPoseProof (CUR with "H0") as "H0".
        iSplitL "H"; et. 	
      } 
      i. des.
      eapply IH; et.
      {
        iIntros "H".
        iPoseProof (FMR0 with "H") as "H". iMod "H".
        rewrite <- URA.add_assoc. 
        iDestruct "H" as "[H H0]".
        iPoseProof (x with "H0") as "H0". iMod "H0".
        replace (c0 ⋅ fmr ⋅ c1 ⋅ c) with (fmr ⋅ (c0 ⋅ c1 ⋅ c)). 2: { r_solve. }
        iSplitL "H"; et.
      }
    - gstep. econs. gfinal. left. eapply CIH; et. 
  Admitted.






