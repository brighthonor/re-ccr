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
Require Import CannonRA CannonMain0.

Set Implicit Arguments.



Section CANNONMAIN.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Variable num_fire: nat.

  Definition main_spec:    fspec :=
    mk_simple (X:=unit)
              (fun _ => (
                   ord_top,
                   (fun varg =>
                      (⌜varg = ([]: list val)↑⌝)
                        ** (OwnM (Ball))
                   ),
                   (fun vret =>
                      (⌜vret = tt↑⌝)%I
                   )
              )).

  Definition MainSbtb: list (gname * fspecbody) :=
    [("main", mk_specbody main_spec (cfunN (main_body num_fire)))].

  Definition SMainSem: SModSem.t := {|
    SModSem.fnsems := MainSbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMain: SMod.t := {|
    SMod.get_modsem := fun _ => SMainSem;
    SMod.sk := [("main", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Main: Mod.t := (SMod.to_tgt GlobalStb) SMain.
End CANNONMAIN.
