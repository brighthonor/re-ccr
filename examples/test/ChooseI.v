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

Set Implicit Arguments.

Section I.

  Context `{_W: CtxWD.t}.

  Definition testF: list val -> itree hAGEs val :=
    fun varg =>
      Ret (Vint 2)
  .

  Definition ChooseSem: HModSem.t := {|
    HModSem.fnsems := [("test", cfunU testF)];
    HModSem.initial_st := tt↑;
    HModSem.initial_cond := emp
  |}
  .

  Definition _Choose: HMod.t := {|
    HMod.get_modsem := fun _ => ChooseSem;
    HMod.sk := [("test", Gfun↑)];
  |}
  .
  Definition Choose := _Choose.
  
  Lemma Choose_unfold: Choose = _Choose.
  Proof. eauto. Qed.

  Global Opaque Choose.

End I.


