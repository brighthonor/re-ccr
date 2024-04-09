Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
Require Import Behavior.
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
Require Import Any.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIM.
  Let st_local: Type := (Any.t).

  Variable world: Type.

  Let W: Type := (Any.t) * (Any.t).
  Variable wf : world -> W -> Prop.
  Variable le: relation world.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree Es Any.t).



  Inductive _sim_itree (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)

  | sim_itree_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          _sim_itree sim_itree RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          _sim_itree sim_itree RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_inline_src
      f_src f_tgt w st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: _sim_itree sim_itree RR true f_tgt w (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_inline_tgt
      f_src f_tgt w st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: _sim_itree sim_itree RR f_src true w (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w (st_src, i_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itree_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: _sim_itree sim_itree RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), _sim_itree sim_itree RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)

  | sim_itree_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)

  | sim_itree_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: _sim_itree sim_itree RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)  

  | sim_itree_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: _sim_itree sim_itree RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      _sim_itree sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  | sim_itree_progress
      w0 st_src st_tgt 
      i_src i_tgt
      (SIM: sim_itree _ _ RR false false w0 (st_src, i_src) (st_tgt, i_tgt))

    :
      _sim_itree sim_itree RR true true w0 (st_src, i_src) (st_tgt, i_tgt)
  .

  Definition lift_rel {R_src R_tgt} (w0: world) (RR: R_src -> R_tgt -> Prop)
             st_src st_tgt (ret_src ret_tgt: Any.t) :=
    exists w1 : world,
      (<<WLE: le w0 w1 >> /\ <<WF: wf w1 (st_src, st_tgt) >> /\ <<RET: ret_src = ret_tgt >>).

  Definition sim_itree o_src o_tgt w0 : relation _ :=
    paco8 _sim_itree bot8 _ _ (lift_rel w0 (@eq Any.t)) o_src o_tgt w0.

  Lemma sim_itree_mon: monotone8 _sim_itree.
  Proof.
    ii. induction IN; try (econs; et; ii; exploit K; i; des; et).
  Qed.

  Hint Constructors _sim_itree.
  Hint Unfold sim_itree.
  Hint Resolve sim_itree_mon: paco.
  Hint Resolve cpn8_wcompat: paco.

  Lemma sim_itree_ind
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop) 
        (P: bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        (RET: forall
            f_src f_tgt w0 st_src st_tgt
            v_src v_tgt
            (RET: RR st_src st_tgt v_src v_tgt),
            P f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt))
        (CALL: forall
            f_src f_tgt w w0 st_src st_tgt
            fn varg k_src k_tgt
            (WF: wf w0 (st_src, st_tgt))
            (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
                paco8 _sim_itree bot8 _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret)),
            P f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
              (st_tgt, trigger (Call fn varg) >>= k_tgt))
        (SYSCALL: forall
            f_src f_tgt w0 st_src st_tgt
            fn varg rvs k_src k_tgt
            (K: forall vret,
                paco8 _sim_itree bot8 _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret)),
            P f_src f_tgt w0 (st_src, trigger (Syscall fn varg rvs) >>= k_src)
              (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt))
        (INLINESRC: forall
            f_src f_tgt w0 st_src st_tgt
            f fn varg k_src i_tgt
            (FUN: alist_find fn fl_src = Some f)
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt))
        (INLINETGT: forall
            f_src f_tgt w0 st_src st_tgt
            f fn varg i_src k_tgt
            (FUN: alist_find fn fl_tgt = Some f)
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt)),
            P f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt))            
        (TAUSRC: forall
            f_src f_tgt w0 st_src st_tgt
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt))
        (TAUTGT: forall
            f_src f_tgt w0 st_src st_tgt
            i_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt))            
        (CHOOSESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X x k_src i_tgt
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
              (st_tgt, i_tgt))
        (CHOOSETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X i_src k_tgt
            (K: forall (x: X), <<SIMH: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)>> /\ <<IH: P f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)>>),
            P f_src f_tgt w0 (st_src, i_src)
              (st_tgt, trigger (Choose X) >>= k_tgt))
        (TAKESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X k_src i_tgt
            (K: forall (x: X), <<SIM: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)>> /\ <<IH: P true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt)>>),
            P f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
              (st_tgt, i_tgt))
        (TAKETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X x i_src k_tgt
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
            (IH: P f_src true w0 (st_src, i_src) (st_tgt, k_tgt x)),
            P f_src f_tgt w0 (st_src, i_src)
              (st_tgt, trigger (Take X) >>= k_tgt))
        (SUPDATESRC: forall
            f_src f_tgt w0 st_src st_tgt
            X k_src i_tgt
            (run: st_local -> st_local * X )
            (K: paco8 _sim_itree bot8 _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
            (IH: P true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt)),
            P f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt))
        (SUPDATETGT: forall
            f_src f_tgt w0 st_src st_tgt
            X i_src k_tgt
            (run: st_local -> st_local * X )
            (K: paco8 _sim_itree bot8 _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
            (IH:  P f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt)))),

            P f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt))       
        (PROGRESS: forall
            w0 st_src st_tgt
            i_src i_tgt
            (SIM: paco8 _sim_itree bot8 _ _ RR false false w0 (st_src, i_src) (st_tgt, i_tgt)),
            P true true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      forall f_src f_tgt w0 st_src st_tgt
             (SIM: paco8 _sim_itree bot8 _ _ RR f_src f_tgt w0 st_src st_tgt),
        P f_src f_tgt w0 st_src st_tgt.
  Proof.
    i. punfold SIM. induction SIM; et.
    { eapply CHOOSETGT; eauto. }
    { eapply TAKESRC; eauto. }
    { eapply PROGRESS; eauto. pclearbot. auto. }
  Qed.

  Variant sim_itree_indC (sim_itree: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itree_indC_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  | sim_itree_indC_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          sim_itree _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                     (st_tgt, trigger (Call fn varg) >>= k_tgt)
  | sim_itree_indC_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          sim_itree _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Syscall fn varg rvs) >>= k_src)
                     (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itree_indC_inline_src
      f_src f_tgt w0 st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_inline_tgt
      f_src f_tgt w0 st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)
 
  | sim_itree_indC_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itree_indC_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)

  | sim_itree_indC_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: sim_itree _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src)
                     (st_tgt, trigger (Choose X) >>= k_tgt)

  | sim_itree_indC_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), sim_itree _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                     (st_tgt, i_tgt)
  | sim_itree_indC_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src)
                     (st_tgt, trigger (Take X) >>= k_tgt)
  
  | sim_itree_indC_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: sim_itree _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itree_indC_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: sim_itree _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itree_indC  sim_itree RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)
  .

  Lemma sim_itree_indC_mon: monotone8 sim_itree_indC.
  Proof.
    ii. inv IN; try (by des; econs; ss; et).
  Qed.
  Hint Resolve sim_itree_indC_mon: paco.

  Lemma sim_itree_indC_spec:
    sim_itree_indC <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    { econs 1; eauto. }
    { econs 2; eauto. i. eapply sim_itree_mon; et. i. eapply rclo8_base. et. }
    { econs 3; eauto. i. eapply sim_itree_mon; et. i. eapply rclo8_base. eauto. }
    { econs 4; et. eapply sim_itree_mon; et. eapply rclo8_base. }
    { econs 5; et. eapply sim_itree_mon; et. eapply rclo8_base. }
    { econs 6; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 7; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 8; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 9; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 10; eauto. i. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 11; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto. }
    { econs 12; eauto. des. esplits; eauto. eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
    { econs 13; eauto. des. esplits; eauto.  eapply sim_itree_mon; eauto. i. eapply rclo8_base. eauto.  }
  Qed.

  Variant sim_itreeC (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | sim_itreeC_ret
      f_src f_tgt w0 st_src st_tgt
      v_src v_tgt
      (RET: RR st_src st_tgt v_src v_tgt)
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, Ret v_src) (st_tgt, Ret v_tgt)
  | sim_itreeC_call
      f_src f_tgt w w0 st_src st_tgt
      fn varg k_src k_tgt
      (WF: wf w0 (st_src, st_tgt))
      (K: forall w1 vret st_src0 st_tgt0 (WLE: le w0 w1) (WF: wf w1 (st_src0, st_tgt0)),
          r _ _ RR true true w (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      sim_itreeC r g RR f_src f_tgt w (st_src, trigger (Call fn varg) >>= k_src)
                 (st_tgt, trigger (Call fn varg) >>= k_tgt)
  | sim_itreeC_syscall
      f_src f_tgt w0 st_src st_tgt
      fn varg rvs k_src k_tgt
      (K: forall vret,
          r _ _ RR true true w0 (st_src, k_src vret) (st_tgt, k_tgt vret))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Syscall fn varg rvs) >>= k_src)
                 (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt)

  | sim_itreeC_inline_src
      f_src f_tgt w0 st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (* (IN: In (fn, f) fl_src) *)
      (K: r _ _ RR true f_tgt w0 (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_inline_tgt
      f_src f_tgt w0 st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (* (IN: In (fn, f) fl_tgt) *)
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)

  | sim_itreeC_tau_src
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR true f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, tau;; i_src) (st_tgt, i_tgt)

  | sim_itreeC_tau_tgt
      f_src f_tgt w0 st_src st_tgt
      i_src i_tgt
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, tau;; i_tgt)


  | sim_itreeC_choose_src
      f_src f_tgt w0 st_src st_tgt
      X x k_src i_tgt
      (K: r _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Choose X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_choose_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Choose X) >>= k_tgt)
  | sim_itreeC_take_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true f_tgt w0 (st_src, k_src x) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (Take X) >>= k_src)
                 (st_tgt, i_tgt)
  | sim_itreeC_take_tgt
      f_src f_tgt w0 st_src st_tgt
      X x i_src k_tgt
      (K: r _ _ RR f_src true w0 (st_src, i_src) (st_tgt, k_tgt x))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src)
                 (st_tgt, trigger (Take X) >>= k_tgt)
  | sim_itreeC_supdate_src
      f_src f_tgt w0 st_src st_tgt
      X k_src i_tgt
      (run: st_local -> st_local * X )
      (K: r _ _ RR true f_tgt w0 (fst (run st_src), k_src (snd (run st_src))) (st_tgt, i_tgt))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt)

  | sim_itreeC_supdate_tgt
      f_src f_tgt w0 st_src st_tgt
      X i_src k_tgt
      (run: st_local -> st_local * X )
      (K: r _ _ RR f_src true w0 (st_src, i_src) (fst (run st_tgt), k_tgt (snd (run st_tgt))))
    :
      sim_itreeC r g RR f_src f_tgt w0 (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt)

  .

  Lemma sim_itreeC_spec_aux:
    sim_itreeC <10= gpaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    i. inv PR.
    { gstep. econs 1; eauto. }
    { guclo sim_itree_indC_spec. econs 2; et. i. gbase. et. }
    { guclo sim_itree_indC_spec. econs 3; et. i. gbase. et. }
    { guclo sim_itree_indC_spec. econs 4; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 5; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 6; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 7; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 8; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 9; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 10; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 11; eauto. des. esplits; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 12; eauto. gbase. eauto. }
    { guclo sim_itree_indC_spec. econs 13; eauto.  gbase. eauto. }
  Qed.

  Lemma sim_itreeC_spec r g
    :
      @sim_itreeC (gpaco8 (_sim_itree) (cpn8 _sim_itree) r g) (gpaco8 (_sim_itree) (cpn8 _sim_itree) g g)
      <8=
      gpaco8 (_sim_itree) (cpn8 _sim_itree) r g.
  Proof.
    i. eapply gpaco8_gpaco; [eauto with paco|].
    eapply gpaco8_mon.
    { eapply sim_itreeC_spec_aux. eauto. }
    { auto. }
    { i. eapply gupaco8_mon; eauto. }
  Qed.

  Lemma sim_itree_progress_flag R0 R1 RR w r g st_src st_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) g g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR true true w st_src st_tgt.
  Proof.
    gstep. destruct st_src, st_tgt. econs; eauto. 
  Qed.


  Lemma sim_itree_flag_mon
        (sim_itree: forall (R_src R_tgt: Type)
                           (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
        R_src R_tgt (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
        f_src0 f_tgt0 f_src1 f_tgt1 w st_src st_tgt
        (SIM: @_sim_itree sim_itree _ _ RR f_src0 f_tgt0 w st_src st_tgt)
        (SRC: f_src0 = true -> f_src1 = true)
        (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      @_sim_itree sim_itree _ _ RR f_src1 f_tgt1 w st_src st_tgt.
  Proof.
    revert f_src1 f_tgt1 SRC TGT.
    induction SIM; i; clarify; et.
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs; eauto. }
  Qed.


  Definition sim_fsem: relation (Any.t -> itree Es Any.t) :=
    (eq ==> (fun it_src it_tgt => forall w mrs_src mrs_tgt (SIMMRS: wf w (mrs_src, mrs_tgt)),
                 sim_itree false false w (mrs_src, it_src)
                           (mrs_tgt, it_tgt)))%signature
  .

  Definition sim_fnsem: relation (string * (Any.t -> itree Es Any.t)) := RelProd eq sim_fsem.

  Variant lflagC (r: forall (R_src R_tgt: Type)
    (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | lflagC_intro
      f_src0 f_src1 f_tgt0 f_tgt1 w st_src st_tgt
      (SIM: r _ _ RR f_src0 f_tgt0 w st_src st_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
    :
      lflagC r RR f_src1 f_tgt1 w st_src st_tgt
  .

  Lemma lflagC_mon
        r1 r2
        (LE: r1  <8= r2)
    :
      @lflagC r1  <8= @lflagC r2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Hint Resolve lflagC_mon: paco.

  Lemma lflagC_spec: lflagC  <9= gupaco8 (_sim_itree) (cpn8 _sim_itree).
  Proof.
    eapply wrespect8_uclo; eauto with paco.
    econs; eauto with paco. i. inv PR.
    eapply GF in SIM.
    revert x3 x4 SRC TGT. induction SIM; i; clarify; et.
    { exploit SRC; auto. exploit TGT; auto. i. clarify. econs 14; eauto.
      eapply rclo8_base; auto. }
  Qed.

  Lemma sim_itree_flag_down  R0 R1 RR r g w st_src st_tgt f_src f_tgt
        (SIM: gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR false false w st_src st_tgt)
    :
      gpaco8 _sim_itree (cpn8 _sim_itree) r g R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    guclo lflagC_spec. econs; eauto.
  Qed.

  Lemma sim_itree_bot_flag_up  R0 R1 RR w st_src st_tgt f_src f_tgt
        (SIM: paco8 _sim_itree bot8 R0 R1 RR true true w st_src st_tgt)
    :
      paco8 _sim_itree bot8 R0 R1 RR f_src f_tgt w st_src st_tgt.
  Proof.
    ginit. remember true in SIM at 1. remember true in SIM at 1.
    clear Heqb Heqb0. revert w st_src st_tgt f_src f_tgt b b0 SIM.
    gcofix CIH. 
    i. revert f_src f_tgt.

    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern b, b0, w, st_src, st_tgt.
    match goal with
    | |- ?P b b0 w st_src st_tgt => set P
    end.
    revert b b0 w st_src st_tgt SIM.
    eapply (@sim_itree_ind R0 R1 RR P); subst P; ss; i; clarify; try (guclo sim_itree_indC_spec; econs; et).
    { i. gstep. econs; et. gfinal. left. et. }
    { i. gstep. econs; et. gfinal. left. et. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { i. hexploit K; eauto. i. des. esplits; eauto. }
    { eapply sim_itree_flag_down. gfinal. right. eapply paco8_mon; eauto. ss. }
  Qed.

  Variant lbindR (r s: forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop):
    forall S_src S_tgt (SS: st_local -> st_local -> S_src -> S_tgt -> Prop), bool -> bool -> world -> st_local * itree Es S_src -> st_local * itree Es S_tgt -> Prop :=
  | lbindR_intro
      f_src f_tgt w0 w1
      R_src R_tgt RR
      (st_src st_tgt: st_local)
      (i_src: itree Es R_src) (i_tgt: itree Es R_tgt)
      (SIM: r _ _ RR f_src f_tgt w0 (st_src, i_src) (st_tgt, i_tgt))

      S_src S_tgt SS
      (k_src: ktree Es R_src S_src) (k_tgt: ktree Es R_tgt S_tgt)
      (SIMK: forall st_src0 st_tgt0 vret_src vret_tgt (SIM: RR st_src0 st_tgt0 vret_src vret_tgt), s _ _ SS false false w1 (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt))
    :
      lbindR r s SS f_src f_tgt w1 (st_src, ITree.bind i_src k_src) (st_tgt, ITree.bind i_tgt k_tgt)
  .

  Hint Constructors lbindR: core.

  Lemma lbindR_mon 
        r1 r2 s1 s2
        (LEr: r1  <8= r2) (LEs: s1  <8= s2)
    :
      lbindR r1 s1  <8= lbindR r2 s2
  .
  Proof. ii. destruct PR; econs; et. Qed.

  Definition lbindC r := lbindR r r.
  Hint Unfold lbindC: core.

  Lemma lbindC_wrespectful: wrespectful8 (_sim_itree) lbindC.
  Proof.
    econs.
    { ii. eapply lbindR_mon; eauto. }
    i. rename l into llll. inv PR; csc.
    remember (st_src, i_src). remember(st_tgt, i_tgt).
    revert st_src i_src st_tgt i_tgt Heqp Heqp0.
    revert k_src k_tgt SIMK. eapply GF in SIM.
    induction SIM; i; clarify; grind; try (econs; et).
    - exploit SIMK; eauto. i.
      eapply sim_itree_flag_mon with (f_src0 := false) (f_tgt0 := false); ss.
      { eapply sim_itree_mon; eauto. i. eapply rclo8_base. auto. }
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et. 
    - exploit IHSIM; et. i. rewrite ! bind_bind in *. et. 
    - eapply rclo8_clo_base. econs; eauto.
  Qed.

  Lemma lbindC_spec: lbindC  <9= gupaco8 (_sim_itree) (cpn8 (_sim_itree)).
  Proof.
    intros. eapply wrespect8_uclo; eauto with paco. eapply lbindC_wrespectful.
  Qed.

End SIM.


Hint Resolve sim_itree_mon: paco.
Hint Resolve cpn8_wcompat: paco.

Lemma self_sim_itree:
  forall st itr fl,
    sim_itree (fun _ '(src, tgt) => src = tgt) top2 fl fl false false tt (st, itr) (st, itr).
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. eapply sim_itree_ret; ss. }
  { guclo sim_itree_indC_spec. econs.
    guclo sim_itree_indC_spec. econs.
    eapply sim_itree_progress_flag. gbase. auto.
  }
  destruct e.
  { dependent destruction c. rewrite <- ! bind_trigger.
    gstep.
    eapply sim_itree_call; ss. ii. subst. econs; et.
    eapply sim_itree_flag_down. gbase. auto.
  }
  destruct s.
  { rewrite <- ! bind_trigger. resub. dependent destruction s.
    { guclo sim_itree_indC_spec. econs.
      guclo sim_itree_indC_spec. econs.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
  { rewrite <- ! bind_trigger. resub. dependent destruction e.
    { guclo sim_itree_indC_spec. econs 9. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs 10. i.
      guclo sim_itree_indC_spec. econs. eexists.
      eapply sim_itree_progress_flag. gbase. eauto.
    }
    { guclo sim_itree_indC_spec. econs. i.
      eapply sim_itree_progress_flag. gbase. auto.
    }
  }
Qed.


(*** desiderata: (1) state-aware simulation relation !!!! ***)
(*** (2) not whole function frame, just my function frame !!!! ***)
(*** (3) would be great if induction tactic works !!!! (study itree case study more) ***)



Module ModSemPair.
Section SIMMODSEM.

  Variable (ms_src ms_tgt: ModSem.t).
  
  Definition fl_src := ms_src.(ModSem.fnsems).
  Definition fl_tgt := ms_tgt.(ModSem.fnsems).

  Let W: Type := (Any.t) * (Any.t).
  Inductive sim: Prop := mk {
    world: Type;
    wf: world -> W -> Prop;
    le: world -> world -> Prop;
    le_PreOrder: PreOrder le;
    sim_fnsems: Forall2 (sim_fnsem wf le fl_src fl_tgt) ms_src.(ModSem.fnsems) ms_tgt.(ModSem.fnsems);
    sim_initial: exists w_init, wf w_init (ms_src.(ModSem.init_st), ms_tgt.(ModSem.init_st));
  }.

End SIMMODSEM.

Lemma self_sim (ms: ModSem.t):
  sim ms ms.
Proof.
  econs; et.
  - instantiate (1:=fun (_ _: unit) => True). ss.
  - instantiate (1:=(fun (_: unit) '(src, tgt) => src = tgt)). (* fun p => fst p = snd p *)
    generalize (ModSem.fnsems ms).
    induction a; ii; ss.
    econs; et. econs; ss. ii; clarify.
    destruct w. exploit self_sim_itree; et.
  - ss.
Qed.

End ModSemPair.








Module ModPair.
Section SIMMOD.
   Variable (md_src md_tgt: Mod.t).
   Inductive sim: Prop := mk {
     sim_modsem:
       forall sk
              (SKINCL: Sk.incl md_tgt.(Mod.sk) sk)
              (SKWF: Sk.wf sk),
         <<SIM: ModSemPair.sim (md_src.(Mod.get_modsem) sk) (md_tgt.(Mod.get_modsem) sk)>>;
     sim_sk: <<SIM: md_src.(Mod.sk) = md_tgt.(Mod.sk)>>;
   }.

End SIMMOD.

End ModPair.



Section SIMMOD.

  Context {CONF: EMSConfig}.

  Lemma Mod_add_fnsems md0 md1 sk
    :
      (ModSem.fnsems (Mod.get_modsem (Mod.add md0 md1) sk)) =
      ModSem.add_fnsems (Mod.get_modsem md0 sk) (Mod.get_modsem md1 sk).
  Proof.
    ss.
  Qed.

  Lemma Mod_add_sk md0 md1
    :
      Mod.sk (Mod.add md0 md1) = Mod.sk md0 ++ Mod.sk md1.
  Proof.
    ss.
  Qed.
(* 
  Lemma Mod_list_incl_sk (mds: list Mod.t) md
        (IN: In md mds)
    :
      Sk.incl (Mod.sk md) (Mod.sk (Mod.add_list mds)).
  Proof.
    rewrite Mod.add_list_sk. revert IN. induction mds; ss.
    i. des; clarify.
    { ii. eapply in_or_app. auto. }
    { ii. eapply in_or_app. right. eapply IHmds; et. }
  Qed.

  Lemma Mod_add_list_get_modsem (mds: list Mod.t) sk
    :
      Mod.get_modsem (Mod.add_list mds) sk
      =
      fold_right ModSem.add {| ModSem.fnsems := []; ModSem.initial_mrs := [] |}
                 (List.map (fun (md: Mod.t) => Mod.get_modsem md sk) mds).
  Proof.
    induction mds; ss. f_equal. rewrite <- IHmds. ss.
  Qed. *)

End SIMMOD.





Require Import SimGlobal.
Require Import Red IRed.

Module TAC.
  Ltac ired_l := try (prw _red_gen 2 0).
  Ltac ired_r := try (prw _red_gen 1 0).

  Ltac ired_both := ired_l; ired_r.

  Ltac step := ired_both; guclo simg_safe_spec; econs; et; i.
  Ltac steps := (repeat step); ired_both.

  Ltac force := ired_both; guclo simg_indC_spec; econs; et.
End TAC.
Import TAC.

Section SEMPAIR.
  Variable ms_src: ModSem.t.
  Variable ms_tgt: ModSem.t.
  Definition fl_src := ms_src.(ModSem.fnsems).
  Definition fl_tgt := ms_tgt.(ModSem.fnsems).
  Variable world: Type.
  Variable wf: world -> Any.t * Any.t -> Prop.
  Variable le: world -> world -> Prop.
  Hypothesis le_PreOrder: PreOrder le.
  
  Hypothesis fnsems_find_iff:
    forall fn,
      (<<NONE: alist_find fn ms_src.(ModSem.fnsems) = None>>) \/
      (exists (f_src f_tgt: _ -> itree _ _),
          (<<SRC: alist_find fn ms_src.(ModSem.fnsems) = Some f_src>>) /\
          (<<TGT: alist_find fn ms_tgt.(ModSem.fnsems) = Some f_tgt>>) /\
          (<<SIM: sim_fsem wf le fl_src fl_tgt f_src f_tgt>>)).
          
  Variant g_lift_rel
          (w0: world) st_src st_tgt: Prop :=
  | g_lift_rel_intro
      w1
      (LE: le w0 w1)
      (MN: wf w1 (st_src, st_tgt))
      
      (* (NMN: forall mn' (NIN: mn <> mn'), st_local mn' = st_local mn') *)
  .

  Variant my_r0:
    forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop :=
  | my_r0_intro
      w0
      (itr_src itr_tgt: itree Es Any.t)
      st_src st_tgt o_src o_tgt
      (SIM: sim_itree wf le fl_src fl_tgt o_src o_tgt w0 (st_src, itr_src) (st_tgt, itr_tgt))
      (* (STATE: forall mn' (MN: mn <> mn'), st_local mn' = st_local mn') *)
    :
      my_r0 (fun '(st_src, ret_src) '(st_tgt, ret_tgt) =>
                g_lift_rel w0 st_src st_tgt /\ ret_src = ret_tgt)
            o_src o_tgt
            (interp_Es (ModSem.prog ms_src) (itr_src) st_src)
            (interp_Es (ModSem.prog ms_tgt) (itr_tgt) st_tgt)
  .

  Let sim_lift: my_r0 <7= simg.
  Proof.
    ginit.
    { i. eapply cpn7_wcompat; eauto with paco. }
    gcofix CIH. i. destruct PR.
    unfold sim_itree in SIM.
    remember (st_src, itr_src).
    remember (st_tgt, itr_tgt).
    remember w0 in SIM at 2.
    revert st_src itr_src st_tgt itr_tgt Heqp Heqp0 Heqw.
    (* TODO: why induction using sim_itree_ind doesn't work? *)
    pattern o_src, o_tgt, w, p, p0.
    match goal with
    | |- ?P o_src o_tgt w p p0 => set P
    end.
    revert o_src o_tgt w p p0 SIM.
    eapply (@sim_itree_ind world wf le fl_src fl_tgt Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; clarify.
    - rr in RET. des. step. splits; auto. econs; et.
    - hexploit (fnsems_find_iff fn). i. des.
      { steps. rewrite NONE. unfold unwrapU, triggerUB. grind. step. ss. }

      { hexploit (SIM (varg) (varg)); et. i. des. ired_both. 
        steps. grind. rewrite SRC. rewrite TGT. unfold unwrapU. ired_both.
        apply simg_progress_flag.
        guclo bindC_spec. econs.
        { gbase. eapply CIH. econs; ss. grind. et. }
        { i. ss. destruct vret_src, vret_tgt. des; clarify. inv SIM0.
          hexploit K; et. i. des. pclearbot. ired_both.
          steps. gbase. eapply CIH. econs; et.
          eapply sim_itree_bot_flag_up. et.           
        }
      }
    - step. i. subst. apply simg_progress_flag.
      hexploit (K x_tgt). i. des. pclearbot.
      steps. gbase. eapply CIH. econs; et.
    - steps. unfold fl_src in FUN. rewrite FUN. grind.
      rewrite <- interp_Es_bind.
      eapply IH; et.
    - steps. unfold fl_tgt in FUN. rewrite FUN. grind.
      rewrite <- interp_Es_bind.
      eapply IH; et.
    - steps.
    - steps. 
    - des. force. exists x. steps. eapply IH; eauto. 
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - steps. i. hexploit K. i. des. steps. eapply IH; eauto.
    - des. force. exists x. steps. eapply IH; eauto.
    - steps. destruct run. steps. eapply IH; eauto.
    - steps. destruct run. steps. eapply IH; eauto.
    - eapply simg_progress_flag. gbase. eapply CIH. econs; eauto.
  Qed.
  (* Admitted. *)

  Context `{CONF: EMSConfig}.
  Hypothesis INIT:
    exists w, g_lift_rel w (ModSem.init_st ms_src) (ModSem.init_st ms_tgt).
  Lemma adequacy_local_aux (P Q: Prop)
        (* (wf: world -> W -> Prop)  *)
        (WF: Q -> P)
    :
      (Beh.of_program (ModSem.compile ms_tgt (Some P)))
      <1=
      (Beh.of_program (ModSem.compile ms_src (Some Q))).
  Proof. 
    eapply adequacy_global_itree; ss.
    hexploit INIT. i. 
    des. ginit.
    { eapply cpn7_wcompat; eauto with paco. }
    unfold ModSem.initial_itr, assume. generalize "main" as fn. i.
    hexploit (fnsems_find_iff fn). i. des.
    { steps. unshelve esplits; et. unfold ITree.map, unwrapU, triggerUB.
    (* rewrite interp_Es_bind. steps. *)
      rewrite NONE. steps. ss. }
    (* { admit. } *)
 
    { 
      inv H. 
      hexploit (SIM (initial_arg) (initial_arg)) ; et; cycle 1. i. des.
      steps. force. esplits; et.
      steps. unfold ITree.map, unwrapU.
      rewrite ! interp_Es_bind. rewrite ! bind_bind.
      rewrite SRC. rewrite TGT. steps. guclo bindC_spec. econs.
      { eapply simg_flag_down. gfinal. right. eapply sim_lift. econs; et. }
      { i. destruct vret_src, vret_tgt. des; clarify. steps. }
    }
  Qed.




End SEMPAIR.

Section SIMCTX.
Import ModSem.

Definition wf_lift {world} wf  :=
  fun (w:world) => 
  (fun '(src, tgt) =>
    match (Any.split src), (Any.split tgt) with
    | Some (l1, r1), Some (l2, r2) => ( wf w (l1, l2) /\ r1 = r2)
    | _, _ => False
    end
  ).

Definition addf f1 f2 : alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l f1) ++ (List.map trans_r f2).


Lemma sim_ctx_aux {world}
      w wf le
      a b c
      fa fb fc 
      ol or stl str itl itr

      (SRC: Any.split stl = Some (b, a))
      (TGT: Any.split str = Some (c, a))

      (SIM: sim_itree wf le fb fc ol or w (b, itl) (c, itr))
:
      @sim_itree world (wf_lift wf) le (addf fb fa) (addf fc fa) ol or w (stl, translate (emb_ run_l) itl) 
                                              (str, translate (emb_ run_l) itr)
.
Proof.
  ginit.

  revert_until wf.

  gcofix CIH. i.

  hexploit SIM. intros SIM'.

  remember (b, itl) eqn:PL.
  remember (c, itr) eqn:PR.
  remember w eqn:Weq.
  unfold sim_itree in SIM'.
  rewrite Weq in SIM' at 2.
  revert a b c stl str itl itr SRC TGT PL PR Weq SIM.
  pattern ol, or, w, p, p0.
  match goal with
  | |- ?P ol or w p p0 => set P
  end.
  eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify.

  - rr in RET. des. clarify.
    rewrite translate_emb_ret.
    gstep. apply sim_itree_ret.
    econs; et. esplits; et.
    unfold wf_lift. rewrite SRC, TGT. split; et.

  - remember (` x : _ <- trigger (Call fn varg);; k_src x). 
    remember (` x : _ <- trigger (Call fn varg);; k_tgt x). 
    remember (b, ` x : _ <- trigger (Call fn varg);; k_src x) eqn:PL.
    remember (c, ` x : _ <- trigger (Call fn varg);; k_tgt x) eqn:PR.
    remember w1 eqn:Weq.
    hexploit SIM. intros SIM0.
    unfold sim_itree in SIM0.
    rewrite Weq in SIM0 at 2.

    revert a b c stl str i i0 WF SRC TGT PL PR Weq SIM SIM0 Heqi Heqi0.
    pattern ol, or, w, p, p0.
    match goal with
    | |- ?P ol or w p p0 => set P
    end.
    eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify;
    rewrite ! translate_emb_bind, translate_emb_callE; gstep; econs;
    try (match goal with
    | |- wf_lift _ _ (_, _) =>  unfold wf_lift; rewrite SRC, TGT; et
    end).
    all: ii; econs; gfinal; left; ss; des_ifs; try rename WF0 into WF1; inv WF1; eapply CIH; et;
         specialize (K _ vret _ _ WLE H); pclearbot; apply sim_itree_bot_flag_up; apply K.
    
  - punfold SIM. inv SIM; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
    + apply inj_pair2 in H0, H1.
      rewrite ! translate_emb_bind, translate_emb_eventE.
      gstep. econs. i. econs. 
      gfinal. left. eapply CIH; et.
      apply sim_itree_bot_flag_up. pfold. apply K0. 

    + pclearbot. punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
      apply inj_pair2 in H0, H1.
      rewrite ! translate_emb_bind, translate_emb_eventE.
      gstep. econs. ii. econs.
      gfinal. left. eapply CIH; et.
      apply sim_itree_bot_flag_up. pfold. apply K0.

  - rewrite ! translate_emb_bind, translate_emb_callE.
    guclo sim_itree_indC_spec.
    econs; et.
    { 
      unfold addf. apply alist_find_app.
      unfold trans_l. rewrite alist_find_map. unfold o_map.
      rewrite FUN. et.
    }
    ss. rewrite <- ! translate_emb_bind.
    eapply IH; et. 
  - rewrite ! translate_emb_bind, translate_emb_callE.
    guclo sim_itree_indC_spec. econs; et.
    { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
    ss. rewrite <- ! translate_emb_bind.
    eapply IH; et. 
  - rewrite ! translate_emb_tau. 
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_tau. 
    guclo sim_itree_indC_spec. econs; et.    
  - rewrite ! translate_emb_bind, translate_emb_eventE.
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_bind, translate_emb_eventE.
    guclo sim_itree_indC_spec. econs; et.
    i. specialize (K x). des. et.
  - rewrite ! translate_emb_bind, translate_emb_eventE.
    guclo sim_itree_indC_spec. econs; et.
    i. specialize (K x). des. et.    
  - rewrite ! translate_emb_bind, translate_emb_eventE.
    guclo sim_itree_indC_spec. econs; et.
  - rewrite ! translate_emb_bind, translate_emb_sE.
    guclo sim_itree_indC_spec. econs; et.
    unfold run_l. rewrite SRC. des_ifs; ss. 
    eapply IH; et. rewrite Any.pair_split; et.
  - rewrite ! translate_emb_bind, translate_emb_sE.
    guclo sim_itree_indC_spec. econs; et.
    unfold run_l. rewrite TGT. des_ifs; ss. 
    eapply IH; et. rewrite Any.pair_split; et. 
  - remember (true) as o_src.
    remember (true) as o_tgt.
    rewrite Heqo_src at 2.
    rewrite Heqo_src in SIM0 at 2.
    rewrite Heqo_tgt in Heqo_src.
    remember (b, itl) eqn:PL.
    remember (c, itr) eqn:PR.
    remember w1 eqn:Weq.
    hexploit SIM0. intros SIM0'.
    unfold sim_itree in SIM0'.
    rewrite Weq in SIM0' at 2.

    revert a b c stl str itl itr SRC TGT PL PR Weq Heqo_src Heqo_tgt SIM0.
    pattern o_src, o_tgt, w1, p1, p2.
    match goal with
    | |- ?P o_src o_tgt w1 p1 p2 => set P
    end.
    eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify.
    + rr in RET. des. clarify.
      rewrite ! translate_emb_ret.
      gstep. apply sim_itree_ret.
      econs; et. esplits; et.
      unfold wf_lift. rewrite SRC, TGT. split; et.
    + remember (` x : _ <- trigger (Call fn varg);; k_src x). 
      remember (` x : _ <- trigger (Call fn varg);; k_tgt x). 
      remember (b, ` x : _ <- trigger (Call fn varg);; k_src x) eqn:PL.
      remember (c, ` x : _ <- trigger (Call fn varg);; k_tgt x) eqn:PR.
      remember w2 eqn:Weq.
      hexploit SIM. intros SIM''.
      unfold sim_itree in SIM''.
      rewrite Weq in SIM'' at 2.

      revert a b c stl str i i0 WF SRC TGT PL PR Weq SIM SIM0 SIM'' Heqi Heqi0.
      pattern ol, or, w, p, p0.
      match goal with
      | |- ?P ol or w p p0 => set P
      end.
      eapply (@sim_itree_ind world wf le fb fc Any.t Any.t (lift_rel wf le w0 (@eq Any.t)) P); subst P; ss; i; des; clarify;
      rewrite ! translate_emb_bind, translate_emb_callE; gstep; econs; 
      try (match goal with 
          | |- wf_lift _ _ _ => unfold wf_lift; rewrite SRC, TGT; et
          end
      ).
      all: ii; econs; gfinal; left; ss; des_ifs; try rename WF0 into WF1; inv WF1; eapply CIH; et;
      specialize (K _ vret _ _ WLE H); pclearbot; apply sim_itree_bot_flag_up; apply K.
    + punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
      * apply inj_pair2 in H0, H1.
        rewrite ! translate_emb_bind, translate_emb_eventE.
        gstep. econs. i. econs.
        gfinal. left. eapply CIH; et.
        apply sim_itree_bot_flag_up. pfold. eapply K0.

      * pclearbot. punfold SIM1. inv SIM1; (try rewrite ! bind_trigger in H4); (try rewrite ! bind_trigger in H6); clarify.
        apply inj_pair2 in H0, H1.
        rewrite ! translate_emb_bind, translate_emb_eventE.
        gstep. econs. i. econs.
        gfinal. left. eapply CIH; et.
        apply sim_itree_bot_flag_up. pfold. eapply K0.
    + rewrite ! translate_emb_bind, translate_emb_callE.
      guclo sim_itree_indC_spec. econs; et.
      { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
      ss. rewrite <- ! translate_emb_bind.
      eapply IH; et.
    + rewrite ! translate_emb_bind, translate_emb_callE.
      guclo sim_itree_indC_spec. econs; et.
      { unfold addf. apply alist_find_app. unfold trans_l. rewrite alist_find_map. unfold o_map. rewrite FUN. et. }
      ss. rewrite <- ! translate_emb_bind.
      eapply IH; et.
    + rewrite ! translate_emb_tau. 
      guclo sim_itree_indC_spec. econs. et. 
    + rewrite ! translate_emb_tau. 
      guclo sim_itree_indC_spec. econs. et. 
    + rewrite ! translate_emb_bind, translate_emb_eventE.
      guclo sim_itree_indC_spec. econs. et.
    + rewrite! translate_emb_bind, translate_emb_eventE.
      guclo sim_itree_indC_spec. econs. et.
      i. specialize (K x). des. et.
    + rewrite! translate_emb_bind, translate_emb_eventE.
      guclo sim_itree_indC_spec. econs. et.
      i. specialize (K x). des. et.    
    + rewrite ! translate_emb_bind, translate_emb_eventE.
      guclo sim_itree_indC_spec. econs. et.
    + rewrite ! translate_emb_bind, translate_emb_sE.
      guclo sim_itree_indC_spec. econs; et.
      unfold run_l. rewrite SRC. des_ifs; ss.
      eapply IH; et. rewrite Any.pair_split. et.
    + rewrite ! translate_emb_bind, translate_emb_sE.
      guclo sim_itree_indC_spec. econs; et.
      unfold run_l. rewrite TGT. des_ifs; ss.
      eapply IH; et. rewrite Any.pair_split. et.      
    + gstep. econs; et.
      gfinal. left. eapply CIH; et.
Qed.

Theorem sim_ctx
      ctx ms1 ms2
      (SIM: ModSemPair.sim ms1 ms2)
    :
      ModSemPair.sim (add ms1 ctx) (add ms2 ctx)
.
Proof.
  inv SIM. inv sim_initial.
  econs; et.
  2: { exists x. instantiate (1:= wf_lift wf0). s.
       rewrite ! Any.pair_split.
       splits; et.
  }
  s. unfold add_fnsems, trans_l, trans_r.
  apply Forall2_app; eapply Forall2_apply_Forall2; et; cycle 1.
  - instantiate (1:= eq). induction (fnsems ctx); et.
  - i. clarify. econs; et. ii; clarify.
    destruct b. ss.
    destruct (Any.split mrs_src) eqn: SRC; destruct (Any.split mrs_tgt) eqn:TGT; clarify.
    2: { destruct p. clarify. }
    destruct p, p0. des. clarify.
    assert (exists w1, le w w1 /\ wf0 w1 (t0, t2)).
    { exists w. splits; et. refl. }
    clear SIMMRS.
    des.
    ginit.
    revert_until w1.
    revert w1 w.
    
    revert SRC TGT.
    revert t0 t2 t3.
    revert mrs_src mrs_tgt.
    
    generalize (i y) as it.
    revert_until wf0.
    gcofix CIH. i.
    apply Any.split_pair in SRC. 
    apply Any.split_pair in TGT.
    des. clarify.  
    ides it.
    + rewrite ! translate_emb_ret.
      gstep. apply sim_itree_ret.
      unfold lift_rel. esplits; et.
      s. rewrite ! Any.pair_split. et.     
    + rewrite ! translate_emb_tau.
      gstep. 
      apply sim_itree_tau_src. apply sim_itree_tau_tgt. 
      eapply sim_itree_progress; et.
      gfinal. left. 
      eapply CIH; et; des; clarify; rewrite ! Any.pair_split; et.
    + erewrite ! (bisimulation_is_eq _ _ (translate_vis _ _ _ _)).
      rewrite <- ! bind_trigger.
      destruct e as [c|[s'|e']].
      * (* callE *)
        gstep. destruct c.
        eapply sim_itree_call; clarify.
        { s. rewrite ! Any.pair_split. esplits; et. }
        i. econs. gfinal. left.
        ss. destruct (Any.split st_src0) eqn: SPL1; destruct (Any.split st_tgt0) eqn: SPL2; clarify.
        2: { destruct p. clarify. }
        destruct p, p0, WF.
        eapply CIH.
        9: { etrans; et. }
        all: clarify; et. 
      * (* sE *)
         gstep. destruct s'.
         apply sim_itree_supdate_src. apply sim_itree_supdate_tgt.
         eapply sim_itree_progress; et.
         unfold ModSem.run_r. rewrite ! Any.pair_split.
         gfinal. left. destruct (run t3). ss. eapply CIH; et; rewrite ! Any.pair_split; et.
      * (* eventE *)
        gstep. destruct e'.
        -- (* Choose *)
           apply sim_itree_choose_tgt. i. eapply sim_itree_choose_src.
           eapply sim_itree_progress; et.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
        -- (* Take *)
           apply sim_itree_take_src. i. eapply sim_itree_take_tgt. 
           eapply sim_itree_progress; et.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
        -- (* Syscall *)
           apply sim_itree_syscall. i. econs.
           gfinal. left. eapply CIH; et; rewrite ! Any.pair_split; et.
  - i. destruct H0. r in H0. rr in H1. 
    destruct a, b. econs; et. ss.
    ii; clarify. ss. 
    destruct (Any.split mrs_src) eqn: SRC; destruct (Any.split mrs_tgt) eqn:TGT; clarify.
    2: { destruct p. clarify. }
    destruct p, p0. des. clarify.
    specialize H1 with (x:=y) (y:=y) (w:=w) (mrs_src := t0) (mrs_tgt := t2).
    specialize (H1 eq_refl SIMMRS).
    eapply sim_ctx_aux; et.
Qed.

End SIMCTX.
