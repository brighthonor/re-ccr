Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import STB.
Require Import CannonRA Cannon0.

Set Implicit Arguments.



Section CANNON.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Definition fire_body {E} `{callE -< E} `{pE -< E} `{eventE -< E}
    : list val -> itree E Z :=
    fun args =>
      let r := 1%Z in
      _ <- trigger (Syscall "print" [r]↑ top1);;
      Ret r
  .

  Definition fire_spec:    fspec :=
    mk_simple (X:=unit)
              (fun _ => (
                   ord_top,
                   (fun varg =>
                      (⌜varg = ([]: list val)↑⌝)
                        ∗ (OwnM (Ball))%I
                   ),
                   (fun vret =>
                      (⌜vret = (1: Z)%Z↑⌝)%I
                   )
              )).

  Definition CannonSbtb: list (gname * fspecbody) :=
    [("fire", mk_specbody fire_spec (cfunN fire_body))].

  Definition SCannonSem: SModSem.t := {|
    SModSem.fnsems := CannonSbtb;
    SModSem.initial_mr := GRA.embed Ready;
    SModSem.initial_st := (1: Z)%Z↑;
  |}
  .

  Definition SCannon: SMod.t := {|
    SMod.get_modsem := fun _ => SCannonSem;
    SMod.sk := [("fire", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Cannon: Mod.t := (SMod.to_tgt GlobalStb) SCannon.
End CANNON.
