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

  Definition pendingRA: URA.t := Excl.t unit.
  Context `{@GRA.inG pendingRA Γ}. 
  Definition pending_r : pendingRA := Excl.just tt.
  Definition pending := OwnM pending_r.

  Definition callableRA : URA.t := Excl.t unit.
  Context `{@GRA.inG callableRA Γ}.
  Definition callable_r :(@URA.car callableRA) := Some tt.
  Definition callable : iProp := OwnM callable_r.

  Lemma pending_unique:
    pending -∗ pending -∗ False%I.
  Proof.
    iIntros "P0 P1". iCombine "P0 P1" as "P".
    iOwnWf "P" as P. exfalso. ur in P. ss. 
  Qed.
  
  Lemma callable_unique:
    pending -∗ pending -∗ False%I.
  Proof.
    iIntros "C0 C1". iCombine "C0 C1" as "C".
    iOwnWf "C" as C. exfalso. ur in C. ss. 
  Qed.

End RA.

Module InitRA.
  Class t
    `{_W: CtxWD.t}
    `{@GRA.inG pendingRA Γ}
    `{@GRA.inG callableRA Γ}
    := InitRA: unit.
End InitRA.