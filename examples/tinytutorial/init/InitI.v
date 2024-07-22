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

Section INIT.
  Context `{_W: CtxWD.t}.
  
  (*
    *** pseudo-code ***

  *)

  Definition initF 
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      _ <- trigger (sPut (Vint 1)↑);;
    Ret Vundef.

  Definition incrF
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      st <- trigger sGet;; st <- st↓?;; v <- (vadd st (Vint 1))?;;
      _ <- trigger (sPut v↑);;
    Ret Vundef.
  
  Definition finalF
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      _ <- trigger (sPut Vundef↑);;
    Ret Vundef.

  Definition InitSem (sk: Sk.t): HModSem.t := {|
    HModSem.fnsems := [("init", cfunU initF); ("incr", cfunU incrF); ("final", cfunU finalF)];
    HModSem.initial_st := Ret tt↑;
    HModSem.initial_cond := emp%I;
  |}
  .

  Definition Init: HMod.t := {|
    HMod.get_modsem := InitSem;
    HMod.sk := [("init", Gfun↑); ("incr", Gfun↑); ("final", Gfun↑)];
  |}
  .
  
End INIT.