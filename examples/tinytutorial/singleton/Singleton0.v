(*** IMP ***)

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

Section IMP.
  Context `{_W: CtxWD.t}.
  
  (*
    *** Exmaple in pseudo-code style ***

        int a = 1;
        def singleton(): int :=
            assume(a == 1); // if a <> 1 then the target goes UB
            a = a - 1;
            return 1;
   *)

  Definition singletonF 
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      a <- trigger sGet;; `a: Z <- a↓?;;
      assume(a = 1%Z);;;
      _ <- trigger (sPut (a - 1: Z)%Z↑);;
      Ret (Vint 1).

  Definition SingletonSem (sk: Sk.t): HModSem.t := {|
    HModSem.fnsems := [("singleton", cfunU singletonF)];
    HModSem.initial_st := Ret (1: Z)%Z↑;
    HModSem.initial_cond := emp%I;
  |}
  .

  Definition Singleton: HMod.t := {|
    HMod.get_modsem := SingletonSem;
    HMod.sk := [("singleton", Gfun↑)];
  |}
  .
  
End IMP.