Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import MutHeader.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  Definition Fsbtb: list (string * fspecbody) := [("f", mk_specbody f_spec (fun _ => trigger (Choose _)))].

  Definition SFSem: SModSem.t := {|
    SModSem.fnsems := Fsbtb;
    SModSem.initial_mr := ε;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SF: SMod.t := {|
    SMod.get_modsem := fun _ => SFSem;
    SMod.sk := [("f", Gfun↑)];
  |}
  .

  Definition F: Mod.t := (SMod.to_tgt (fun _ => GlobalStb)) SF.

End PROOF.
