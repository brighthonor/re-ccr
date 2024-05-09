Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Set Implicit Arguments.






Section CANNON.
  Context `{Σ: GRA.t}.
  Definition div (n m: Z): option Z :=
    if Z_zerop m then None else Some (Z.div n m).

  Definition fire_body {E} `{hAGE -< E} `{callE -< E} `{sE -< E} `{eventE -< E}
    : list val -> itree E Z :=
    fun args =>
      powder <- trigger sGet;; powder <- powder↓?;;
      r <- (div 1 powder)?;;
      _ <- trigger (Syscall "print" [r]↑ top1);;
      _ <- trigger (sPut (powder - 1)%Z↑);;
      Ret r
  .

  Definition CannonSem: HModSem.t := {|
    HModSem.fnsems := [("fire", cfunU fire_body)];
    HModSem.initial_st := (1: Z)%Z↑;
  |}
  .

  Definition Cannon: HMod.t := {|
    HMod.get_modsem := fun _ => CannonSem;
    HMod.sk := [("fire", Gfun↑)];
  |}
  .
End CANNON.
