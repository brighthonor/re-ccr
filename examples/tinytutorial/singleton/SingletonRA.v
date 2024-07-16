(*** RA ***)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef IPM.
Require Import sProp sWorld World SRF.

Set Implicit Arguments.

(* Same RA with Cannon example *)
Section RA.
  Context `{_W: CtxWD.t}.
  Definition SingletonRA: URA.t := Auth.t (Excl.t unit).
  Context `{@GRA.inG SingletonRA Γ}. 
  Definition Ready_r: SingletonRA := Auth.black (M:=(Excl.t _)) (Some tt).
  Definition Ready : iProp := OwnM (Ready_r).
  Definition Ball_r : SingletonRA := Auth.white (M:=(Excl.t _)) (Some tt).
  Definition Ball : iProp := OwnM (Ball_r).
  Definition Fired_r : SingletonRA := Auth.excl (M:=(Excl.t _)) (Some tt) (Some tt).
  Definition Fired : iProp := OwnM (Fired_r).


  Lemma ReadyBall_r: Ready_r ⋅ Ball_r = Fired_r.
  Proof.
    ur. rewrite URA.unit_idl. ss.
  Qed.

  Lemma ReadyBall: Ready ∗ Ball ⊢ Fired.
  Proof.
    iIntros "[A B]". iCombine "A B" as "B".
    rewrite ReadyBall_r. eauto.
  Qed.

  Lemma FiredReady_r: ~ URA.wf (Fired_r ⋅ Ready_r).
  Proof.
    ur. ss.
  Qed.

  Lemma FiredReady : Fired -∗ Ready -∗ False%I.
  Proof.
    iIntros "F R". iCombine "F R" as "H".
    iOwnWf "H". exfalso. eapply FiredReady_r. eauto.
  Qed.

  Lemma FiredBall_r: ~ URA.wf (Fired_r ⋅ Ball_r).
  Proof.
    ur. ii. des. ur in H0. red in H0. des. ur in H0. destruct ctx; ss.
  Qed.

  Lemma FiredBall: Fired -∗ Ball -∗ False%I.
  Proof.
    iIntros "F B". iCombine "F B" as "H".
    iOwnWf "H". exfalso. eapply FiredBall_r. eauto.
  Qed.

  Lemma BallReady_wf: URA.wf (Ball_r ⋅ Ready_r).
  Proof.
    ur. split.
    { eexists. rewrite ! URA.unit_id. ss. }
    { ur. ss. }
  Qed.
End RA.

Module SingletonRA.
  Class t
    `{_W: CtxWD.t}
    `{@GRA.inG SingletonRA Γ}
    := SingletonRA: unit.

End SingletonRA.