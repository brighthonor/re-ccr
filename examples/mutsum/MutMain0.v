Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.

  (***
    main() := return f(10)
  ***)
  Definition mainF:  Any.t -> itree Es Any.t :=
    fun varg =>
      r <- trigger (Call "f" [Vint 10]↑);;
      Ret r.

  Definition MainSem: ModSem.t := {|
    ModSem.fnsems := [("main", mainF)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition Main: Mod.t := {|
    Mod.get_modsem := fun _ => MainSem;
    (* Mod.sk := [("Main", Gfun↑)]; *)
    Mod.sk := Sk.unit;
  |}
  .
End PROOF.
