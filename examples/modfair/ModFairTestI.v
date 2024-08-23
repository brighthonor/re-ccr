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

Require Import FairCounter WFLibLarge ModFairA.

Set Implicit Arguments.

Section I.

  Context `{_W: CtxWD.t}.

  Definition ff (b: bool): nat -> Flag.t :=
    fun n => 
      if (n =? 0) 
      then (if b then Flag.success else Flag.fail)
      else Flag.emp.

  Definition testF: list val -> itree hAGEs val :=
    fun varg =>
      (* tau for progress *)
      tau;; _ <- 
      (ITree.iter
        (fun (_: unit) =>
          `b: bool <- trigger (Choose bool);;
          if b
          then
            `_: val <- (ccallU "fair" [ff true]);;
            _ <- trigger (Syscall "print" [Vint 42]↑ top1);;
            Ret (inl tt: unit + unit)
          else 
            `_: val <- (ccallU "fair" [ff false]);;
            Ret (inl tt: unit + unit)
      ) tt);;
      Ret Vundef
  .

  Definition FairSem: HModSem.t := {|
    HModSem.fnsems := [("test", cfunU testF)];
    HModSem.initial_st := tt↑;
    HModSem.initial_cond := emp
  |}
  .

  Definition _Fair: HMod.t := {|
    HMod.get_modsem := fun _ => FairSem;
    HMod.sk := [("test", Gfun↑)];
  |}
  .
  Definition Fair := _Fair.
  
  Lemma Fair_unfold: Fair = _Fair.
  Proof. eauto. Qed.

  Global Opaque Fair.

End I.
