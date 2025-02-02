Require Import Coqlib.
Require Import ITreelib.
Require Import Any.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Coq.Relations.Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From Ordinal Require Import Ordinal Arithmetic.
Require Import SimSTS.

Set Implicit Arguments.







Section SIM.

Section TY.
(* Context `{R: Type}. *)
Inductive _simg
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: @_simg simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: @_simg simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    _simg simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_chooseL
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (SIM: exists x, _simg simg RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, _simg simg RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, _simg simg RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_takeR
    X itr_src0 ktr_tgt0
    (TAKER: True)
    (SIM: exists x, _simg simg RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)

| simg_progress
    itr_src itr_tgt
    (SIM: simg _ _ RR false false itr_src itr_tgt)
    (SRC: f_src = true)
    (TGT: f_tgt = true)
  :
    _simg simg RR f_src f_tgt itr_src itr_tgt
.

Lemma _simg_ind2 (r: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      R0 R1 (RR: R0 -> R1 -> Prop)
      (P: bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src f_tgt
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), r _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: _simg r RR true f_tgt itr_src0 itr_tgt0)
          (IH: P true f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: _simg r RR f_src true itr_src0 itr_tgt0)
          (IH: P f_src true itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: _simg r RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: _simg r RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: _simg r RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: _simg r RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src f_tgt
          itr_src itr_tgt
          (SIM: r _ _ RR false false itr_src itr_tgt)
          (SRC: f_src = true)
          (TGT: f_tgt = true),
          P f_src f_tgt itr_src itr_tgt)
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: _simg r RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  fix IH 5. i. inv SIM.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. }
  { eapply TAUL; eauto. }
  { eapply TAUR; eauto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. }
  { eapply CHOOSER; eauto. }
  { eapply TAKEL; eauto. }
  { eapply TAKER; eauto. des. esplits; eauto. }
  { eapply PROGRESS; eauto. }
Qed.

Definition simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop := paco7 _simg bot7.

Lemma simg_mon: monotone7 _simg.
Proof.
  ii. induction IN using _simg_ind2.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. des. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. des. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
Qed.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.


Inductive simg_indC
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_indC_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    simg_indC simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_indC_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    simg_indC simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_indC_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_indC_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_indC_chooseL
    X ktr_src0 itr_tgt0
    (CHOOSEL: True)
    (SIM: exists x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0)
| simg_indC_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_indC_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    simg_indC simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
| simg_indC_takeR
    X itr_src0 ktr_tgt0
    (TAKER: True)
    (SIM: exists x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    simg_indC simg RR f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0)
.

Lemma simg_indC_mon: monotone7 simg_indC.
Proof.
  ii. inv IN.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. }
  { econs 7; eauto. }
  { econs 8; eauto. des. esplits; eauto. }
Qed.
Hint Resolve simg_indC_mon: paco.

Lemma simg_indC_spec:
  simg_indC <8= gupaco7 _simg (cpn7 _simg).
Proof.
  eapply wrespect7_uclo; eauto with paco.
  econs; eauto with paco. i. inv PR.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base. auto. }
  { econs 3; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { econs 4; eauto. eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
  { des. econs 5; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 6; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { econs 7; eauto. i. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
  { des. econs 8; eauto. esplits. eapply simg_mon; eauto. i. eapply rclo7_base; eauto. }
Qed.

Lemma simg_ind R0 R1 (RR: R0 -> R1 -> Prop)
      (P: bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
      (RET: forall
          f_src f_tgt
          r_src r_tgt
          (SIM: RR r_src r_tgt),
          P f_src f_tgt (Ret r_src) (Ret r_tgt))
      (SYSCALL: forall
          f_src f_tgt
          ktr_src0 ktr_tgt0 fn varg rvs
          (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt)),
          P f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0))
      (TAUL: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUL: True)
          (SIM: simg RR true f_tgt itr_src0 itr_tgt0)
          (IH: P true f_tgt itr_src0 itr_tgt0),
          P f_src f_tgt (tau;; itr_src0) (itr_tgt0))
      (TAUR: forall
          f_src f_tgt
          itr_src0 itr_tgt0
          (TAUR: True)
          (SIM: simg RR f_src true itr_src0 itr_tgt0)
          (IH: P f_src true itr_src0 itr_tgt0),
          P f_src f_tgt (itr_src0) (tau;;itr_tgt0))
      (CHOOSEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (CHOOSEL: True)
          (SIM: exists x, <<SIM: simg RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Choose X) >>= ktr_src0) (itr_tgt0))
      (CHOOSER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (CHOOSER: True)
          (SIM: forall x, <<SIM: simg RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0))
      (TAKEL: forall
          f_src f_tgt
          X ktr_src0 itr_tgt0
          (TAKEL: True)
          (SIM: forall x, <<SIM: simg RR true f_tgt (ktr_src0 x) itr_tgt0>> /\ <<IH: P true f_tgt (ktr_src0 x) itr_tgt0>>),
          P f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0))
      (TAKER: forall
          f_src f_tgt
          X itr_src0 ktr_tgt0
          (TAKER: True)
          (SIM: exists x, <<SIM: simg RR f_src true itr_src0 (ktr_tgt0 x)>> /\ <<IH: P f_src true itr_src0 (ktr_tgt0 x)>>),
          P f_src f_tgt (itr_src0) (trigger (Take X) >>= ktr_tgt0))
      (PROGRESS: forall
          f_src f_tgt
          itr_src itr_tgt
          (SIM: simg RR false false itr_src itr_tgt)
          (SRC: f_src = true)
          (TGT: f_tgt = true),
          P f_src f_tgt itr_src itr_tgt)
  :
    forall f_src f_tgt itr_src itr_tgt
           (SIM: simg RR f_src f_tgt itr_src itr_tgt),
      P f_src f_tgt itr_src itr_tgt.
Proof.
  i. punfold SIM. induction SIM using _simg_ind2; i; clarify.
  { eapply RET; eauto. }
  { eapply SYSCALL; eauto. i. exploit SIM; eauto. i. des. pclearbot. eauto. }
  { eapply TAUL; eauto. pfold. auto. }
  { eapply TAUR; eauto. pfold. auto. }
  { eapply CHOOSEL; eauto. des. esplits; eauto. pfold. auto. }
  { eapply CHOOSER; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
  { eapply TAKEL; eauto. i. exploit SIM; eauto. i. des. esplits; eauto. pfold. auto. }
  { eapply TAKER; eauto. des. esplits; eauto. pfold. auto. }
  { eapply PROGRESS; eauto. pclearbot. auto. }
Qed.

End TY.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Resolve cpn7_wcompat: paco.

Variant flagC (r: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| flagC_intro
    f_src0 f_src1 f_tgt0 f_tgt1 R0 R1 (RR: R0 -> R1 -> Prop) itr_src itr_tgt
    (SRC: f_src0 = true -> f_src1 = true)
    (TGT: f_tgt0 = true -> f_tgt1 = true)
    (SIM: r _ _ RR f_src0 f_tgt0 itr_src itr_tgt)
  :
    flagC r RR f_src1 f_tgt1 itr_src itr_tgt
.
Hint Constructors flagC: core.

Lemma flagC_mon
      r1 r2
      (LE: r1 <7= r2)
  :
    flagC r1 <7= flagC r2
.
Proof. ii. destruct PR; econs; et. Qed.
Hint Resolve flagC_mon: paco.

Lemma flagC_wrespectful: wrespectful7 (_simg) flagC.
Proof.
  econs; eauto with paco.
  ii. inv PR. csc.
  eapply GF in SIM.
  revert x3 x4 SRC TGT. induction SIM using _simg_ind2; i; clarify.
  { econs 1; eauto. }
  { econs 2; eauto. i. eapply rclo7_base; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. eapply rclo7_clo_base. econs; eauto. }
Qed.

Lemma flagC_spec: flagC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply flagC_wrespectful.
Qed.

Lemma simg_flag
      r R0 R1 RR itr_src itr_tgt f_src0 f_tgt0 f_src1 f_tgt1
      (SIM: @_simg r R0 R1 RR f_src0 f_tgt0 itr_src itr_tgt)
      (SRC: f_src0 = true -> f_src1 = true)
      (TGT: f_tgt0 = true -> f_tgt1 = true)
  :
    @_simg r R0 R1 RR f_src1 f_tgt1 itr_src itr_tgt.
Proof.
  revert f_src1 f_tgt1 SRC TGT. induction SIM using _simg_ind2; i.
  { econs 1; eauto. }
  { econs 2; eauto. }
  { econs 3; eauto. }
  { econs 4; eauto. }
  { econs 5; eauto. des. esplits; eauto. }
  { econs 6; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 7; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { econs 8; eauto. des. esplits; eauto. }
  { econs 9; eauto. }
Qed.

Lemma simg_progress_flag R0 R1 RR r g itr_src itr_tgt
      (SIM: gpaco7 _simg (cpn7 _simg) g g R0 R1 RR false false itr_src itr_tgt)
  :
    gpaco7 _simg (cpn7 _simg) r g R0 R1 RR true true itr_src itr_tgt.
Proof.
  gstep. econs; eauto.
Qed.

Lemma simg_flag_down R0 R1 RR r g itr_src itr_tgt f_src f_tgt
      (SIM: gpaco7 _simg (cpn7 _simg) r g R0 R1 RR false false itr_src itr_tgt)
  :
    gpaco7 _simg (cpn7 _simg) r g R0 R1 RR f_src f_tgt itr_src itr_tgt.
Proof.
  guclo flagC_spec. econs; [..|eauto]; ss.
Qed.

Lemma simg_bot_flag_up R0 R1 RR st_src st_tgt f_src f_tgt
      (SIM: @simg R0 R1 RR true true st_src st_tgt)
  :
    simg RR f_src f_tgt st_src st_tgt.
Proof.
  ginit. remember true in SIM at 1. remember true in SIM at 1.
  clear Heqb Heqb0. revert st_src st_tgt f_src f_tgt b b0 SIM.
  gcofix CIH. i. revert f_src f_tgt.
  induction SIM using simg_ind.
  { guclo simg_indC_spec. econs 1; eauto. }
  { gstep. econs 2; eauto. i. gbase. eapply CIH; eauto. }
  { guclo simg_indC_spec. econs 3; eauto. }
  { guclo simg_indC_spec. econs 4; eauto. }
  { guclo simg_indC_spec. econs 5; eauto. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 6; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 7; eauto. i. hexploit SIM; eauto. i. des. esplits; eauto. }
  { guclo simg_indC_spec. econs 8; eauto. des. esplits; eauto. }
  { i. eapply simg_flag_down. gfinal. right.
    eapply paco7_mon; eauto. ss.
  }
Qed.


Variant bindR (r s: forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop):
  forall S0 S1 (SS: S0 -> S1 -> Prop), bool -> bool -> (itree eventE S0) -> (itree eventE S1) -> Prop :=
| bindR_intro
    f_src f_tgt

    R0 R1 RR
    (i_src: itree eventE R0) (i_tgt: itree eventE R1)
    (SIM: r _ _ RR f_src f_tgt i_src i_tgt)

    S0 S1 SS
    (k_src: ktree eventE R0 S0) (k_tgt: ktree eventE R1 S1)
    (SIMK: forall vret_src vret_tgt (SIM: RR vret_src vret_tgt), s _ _ SS false false (k_src vret_src) (k_tgt vret_tgt))
  :
    bindR r s SS f_src f_tgt (ITree.bind i_src k_src) (ITree.bind i_tgt k_tgt)
.

Hint Constructors bindR: core.

Lemma bindR_mon
      r1 r2 s1 s2
      (LEr: r1 <7= r2) (LEs: s1 <7= s2)
  :
    bindR r1 s1 <7= bindR r2 s2
.
Proof. ii. destruct PR; econs; et. Qed.

Definition bindC r := bindR r r.
Hint Unfold bindC: core.



Lemma bindC_wrespectful: wrespectful7 (_simg) bindC.
Proof.
  econs.
  { ii. eapply bindR_mon; eauto. }
  i. inv PR. csc. eapply GF in SIM.
  revert k_src k_tgt SIMK. induction SIM using _simg_ind2; i.
  { irw. hexploit SIMK; eauto. i. eapply GF in H.
    eapply simg_mon; eauto. eapply simg_flag.
     { eapply simg_mon; eauto. i. eapply rclo7_base. auto. }
    { ss. }
    { ss. }
  }
  { rewrite ! bind_bind. econs; eauto. ii.
    { econs 2; eauto with paco. econs; eauto with paco. }
  }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_tau. econs; eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { rewrite ! bind_bind. econs; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. i. exploit SIM; eauto. i. des. eauto. }
  { rewrite ! bind_bind. econs; eauto. des. esplits; et. }
  { clarify. econs; eauto. eapply rclo7_clo_base. econs; eauto. }
Qed.

Lemma bindC_spec: bindC <8= gupaco7 (_simg) (cpn7 (_simg)).
Proof.
  intros. eapply wrespect7_uclo; eauto with paco. eapply bindC_wrespectful.
Qed.

Lemma self_simg:
  forall (wf: Any.t -> Any.t -> Prop) (WF: forall x, wf x x) (itr: itree eventE Any.t), simg wf false false itr itr.
Proof.
  ginit. gcofix CIH. i. ides itr.
  { gstep. econs; eauto. }
  { gstep. econs; eauto. econs; eauto. econs; eauto. gbase. eauto. }
  destruct e; rewrite <- bind_trigger; resub.
  { 
    gstep. econs 6; eauto. i. econs 5; eauto. exists x. 
    econs; eauto. gbase. eauto.
  }
  {
    gstep. econs; eauto. i. econs; eauto. exists x.
    econs; eauto. gbase. eauto. 
  }
  {
    gstep. econs; eauto. i. subst.
    eapply simg_flag_down. gbase. eauto.  
  }
Qed.




Lemma step_trigger_choose_iff X k itr e
      (STEP: ModSem.step (trigger (Choose X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_trigger_take_iff X k itr e
      (STEP: ModSem.step (trigger (Take X) >>= k) e itr)
  :
    exists x,
      e = None /\ itr = k x.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et.  }
  { eapply f_equal with (f:=observe) in H0. ss. }
Qed.

Lemma step_tau_iff itr0 itr1 e
      (STEP: ModSem.step (Tau itr0) e itr1)
  :
    e = None /\ itr0 = itr1.
Proof.
  inv STEP. et.
Qed.

Lemma step_ret_iff rv itr e
      (STEP: ModSem.step (Ret rv) e itr)
  :
    False.
Proof.
  inv STEP.
Qed.

Lemma step_trigger_syscall_iff fn args rvs k e itr
      (STEP: ModSem.step (trigger (Syscall fn args rvs) >>= k) e itr)
  :
    exists rv, itr = k rv /\ e = Some (event_sys fn args rv)
               /\ <<RV: rvs rv>> /\ <<SYS: syscall_sem (event_sys fn args rv)>>.
Proof.
  inv STEP.
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss. }
  { eapply f_equal with (f:=observe) in H0. ss.
    unfold trigger in H0. ss. cbn in H0.
    dependent destruction H0. ired. et. }
Qed.


Lemma itree_eta_eq E R (itr0 itr1: itree E R)
    (OBSERVE: observe itr0 = observe itr1)
  :
    itr0 = itr1.
Proof.
  rewrite (itree_eta_ itr0).
  rewrite (itree_eta_ itr1).
  rewrite OBSERVE. auto.
Qed.

Lemma step_trigger_choose X k x
  :
    ModSem.step (trigger (Choose X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSem.step ?itr _ _] =>
    replace itr with (Subevent.vis (Choose X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_take X k x
  :
    ModSem.step (trigger (Take X) >>= k) None (k x).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSem.step ?itr _ _] =>
    replace itr with (Subevent.vis (Take X) k)
  end; ss.
  { econs. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_trigger_syscall fn args (rvs: Any.t -> Prop) k rv
      (RV: rvs rv) (SYS: syscall_sem (event_sys fn args rv))
  :
    ModSem.step (trigger (Syscall fn args rvs) >>= k) (Some (event_sys fn args rv)) (k rv).
Proof.
  unfold trigger. ss.
  match goal with
  | [ |- ModSem.step ?itr _ _] =>
    replace itr with (Subevent.vis (Syscall fn args rvs) k)
  end; ss.
  { econs; et. }
  { eapply itree_eta_eq. ss. cbv. f_equal.
    extensionality x0. eapply itree_eta_eq. ss. }
Qed.

Lemma step_tau itr
  :
    ModSem.step (Tau itr) None itr.
Proof.
  econs.
Qed.

Context {CONFS CONFT: EMSConfig}.
Hypothesis (FINSAME: (@finalize CONFS) = (@finalize CONFT)).

Theorem adequacy_global_itree itr_src itr_tgt
        (SIM: simg eq false false itr_src itr_tgt)
  :
    Beh.of_program (@ModSem.compile_itree CONFT itr_tgt)
    <1=
    Beh.of_program (@ModSem.compile_itree CONFS itr_src).
Proof.
  unfold Beh.of_program. ss.
  remember false as o_src0 in SIM at 1.
  remember false as o_tgt0 in SIM at 1. clear Heqo_src0 Heqo_tgt0.
  i. eapply adequacy_aux; et.
  instantiate (1:=o_tgt0). instantiate (1:=o_src0). clear x0 PR.
  generalize itr_tgt at 1 as md_tgt.
  generalize itr_src at 1 as md_src. i. ginit.
  revert o_src0 o_tgt0 itr_src itr_tgt SIM. gcofix CIH.
  i. induction SIM using simg_ind; i; clarify.
  { gstep. destruct (finalize r_tgt) eqn:T.
    { eapply sim_fin; ss; cbn; des_ifs; rewrite FINSAME in *; clarify. }
    { eapply sim_angelic_src.
      { cbn. des_ifs; rewrite FINSAME in *; clarify. }
      i. exfalso. inv STEP.
    }
  }
  { gstep. eapply sim_vis; ss. i.
    eapply step_trigger_syscall_iff in STEP. des. clarify.
    esplits.
    { eapply step_trigger_syscall; et. }
    { gbase. eapply CIH. hexploit SIM; et. }
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_tau; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss. i.
    eapply step_tau_iff in STEP. des. clarify.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_demonic_src; ss.
    esplits; eauto. eapply step_trigger_choose; et.
  }
  { guclo sim_indC_spec. eapply sim_indC_demonic_tgt; ss.
    i.  eapply step_trigger_choose_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; eauto.
  }
  { guclo sim_indC_spec. eapply sim_indC_angelic_src; ss. i.
    eapply step_trigger_take_iff in STEP. des. clarify.
    hexploit (SIM x); et. i. des. esplits; et.
  }
  { des. guclo sim_indC_spec. eapply sim_indC_angelic_tgt; ss.
    esplits; eauto. eapply step_trigger_take; et.
  }
  { gstep. eapply sim_progress; eauto. gbase. auto. }
Qed.


Variable md_src md_tgt: Mod.t.
Let ms_src: ModSem.t := md_src.(Mod.enclose).
Let ms_tgt: ModSem.t := md_tgt.(Mod.enclose).

Section ADEQUACY.
(* Hypothesis (SIM: simg eq false false (@ModSem.initial_itr ms_src CONFS ) (@ModSem.initial_itr ms_tgt CONFT )). *)
Hypothesis (SIM: simg eq false false (@ModSem.initial_itr ms_src CONFS (Some (Mod.wf md_src))) (@ModSem.initial_itr ms_tgt CONFT (Some (Mod.wf md_tgt)))).


Theorem adequacy_global: Beh.of_program (@Mod.compile _ CONFT md_tgt) <1= Beh.of_program (@Mod.compile _ CONFS md_src).
Proof.
  eapply adequacy_global_itree. eapply SIM.
Qed.
End ADEQUACY.
End SIM.

Hint Constructors _simg.
Hint Unfold simg.
Hint Resolve simg_mon: paco.
Hint Constructors flagC: core.
Hint Resolve flagC_mon: paco.
Hint Constructors bindR: core.
Hint Unfold bindC: core.
Hint Constructors simg_indC: core.
Hint Resolve sim_indC_mon: paco.


Variant _simg_safe
          (simg: forall R0 R1 (RR: R0 -> R1 -> Prop), bool -> bool -> (itree eventE R0) -> (itree eventE R1) -> Prop)
          {R0 R1} (RR: R0 -> R1 -> Prop) (f_src f_tgt: bool): (itree eventE R0) -> (itree eventE R1) -> Prop :=
| simg_safe_ret
    r_src r_tgt
    (SIM: RR r_src r_tgt)
  :
    _simg_safe simg RR f_src f_tgt (Ret r_src) (Ret r_tgt)
| simg_safe_syscall
    ktr_src0 ktr_tgt0 fn varg rvs
    (SIM: forall x_src x_tgt (EQ: x_src = x_tgt), simg _ _ RR true true (ktr_src0 x_src) (ktr_tgt0 x_tgt))
  :
    _simg_safe simg RR f_src f_tgt (trigger (Syscall fn varg rvs) >>= ktr_src0) (trigger (Syscall fn varg rvs) >>= ktr_tgt0)

| simg_safe_tauL
    itr_src0 itr_tgt0
    (TAUL: True)
    (SIM: simg _ _ RR true f_tgt itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (tau;; itr_src0) (itr_tgt0)
| simg_safe_tauR
    itr_src0 itr_tgt0
    (TAUR: True)
    (SIM: simg _ _ RR f_src true itr_src0 itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (tau;; itr_tgt0)

| simg_safe_chooseR
    X itr_src0 ktr_tgt0
    (CHOOSER: True)
    (SIM: forall x, simg _ _ RR f_src true itr_src0 (ktr_tgt0 x))
  :
    _simg_safe simg RR f_src f_tgt (itr_src0) (trigger (Choose X) >>= ktr_tgt0)

| simg_safe_takeL
    X ktr_src0 itr_tgt0
    (TAKEL: True)
    (SIM: forall x, simg _ _ RR true f_tgt (ktr_src0 x) itr_tgt0)
  :
    _simg_safe simg RR f_src f_tgt (trigger (Take X) >>= ktr_src0) (itr_tgt0)
.

Lemma simg_safe_spec:
  _simg_safe <8= gupaco7 _simg (cpn7 _simg).
Proof.
  i. eapply simg_indC_spec. inv PR.
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
  { econs; eauto. }
Qed.

(* Lemma simg_map R0 R1 RR R0' R1' RR' f_src f_tgt itl itr (f0: R0 -> R0') (f1: R1 -> R1')
      (SIM: @simg R0 R1 RR f_src f_tgt itl itr)
      (IMPL: forall r0 r1, RR r0 r1 -> RR' (f0 r0) (f1 r1): Prop)
:
      @simg R0' R1' RR' f_src f_tgt (f0 <$> itl) (f1 <$> itr)
.
Proof.
  revert_until RR'.
  pcofix CIH. i.
  (* punfold SIM.  *)
  induction SIM using simg_ind; s.
  - erewrite ! (bisimulation_is_eq _ _ (map_ret _ _)). eauto with paco.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_syscall. i. right. eapply CIH; et.
    (* specialize (SIM _ _ EQ). pclearbot. et. *)
    (* edestruct SIM; et. inv H. *)
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)).
    pfold. apply simg_tauL; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_tau _ _)). 
    pfold. apply simg_tauR; et. punfold IHSIM.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseL; et. 
    des. exists x. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_chooseR; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeL; et.
    i. exploit SIM. esplits. des. punfold IH.
  - erewrite ! (bisimulation_is_eq _ _ (map_bind _ _ _)).
    pfold. apply simg_takeR; et.
    des. exists x. punfold IH.
  - pfold. apply simg_progress; et. right. eapply CIH; et.
Qed. *)