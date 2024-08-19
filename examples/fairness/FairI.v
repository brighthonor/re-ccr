Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Require Import FairCounter WFLibLarge.

Set Implicit Arguments.

Section I.

  Context `{_W: CtxWD.t}.

  Variable initial_map : iimap nat nat_wf.

  Definition ff (n: nat): Flag.t :=
    if (n =? 0) then Flag.success else 
      if (n =? 1) then Flag.fail else Flag.emp.

  Definition fairF: list val -> itree hAGEs val :=
    fun varg =>
      tau;; _ <- 
      (ITree.iter
        (fun (_: unit) =>
          `b: bool <- trigger (Choose bool);;
          if b
          then
            ii <- trigger sGet;; ii <- ii↓?;;
            ni <- trigger (Choose (iimap nat nat_wf));;
            _ <- trigger (Fair ff ii ni);;
            _ <- trigger (sPut ni↑);;
            _ <- trigger (Syscall "print" [Vint 42]↑ top1);;
            Ret (inl tt: unit + unit)
          else 
            ii <- trigger sGet;; ii <- ii↓?;;
            ni <- trigger (Choose (iimap nat nat_wf));;
            _ <- trigger (Fair ff ii ni);;
            _ <- trigger (sPut ni↑);;
            Ret (inl tt: unit + unit)
      ) tt);;
      Ret Vundef
  .

  Definition FairSem: HModSem.t := {|
    HModSem.fnsems := [("fair", cfunU fairF)];
    HModSem.initial_st := initial_map↑;
    HModSem.initial_cond := emp
  |}
  .

  Definition _Fair: HMod.t := {|
    HMod.get_modsem := fun _ => FairSem;
    HMod.sk := [("fair", Gfun↑)];
  |}
  .
  Definition Fair := _Fair.
  
  Lemma Fair_unfold: Fair = _Fair.
  Proof. eauto. Qed.

  Global Opaque Fair.

End I.
