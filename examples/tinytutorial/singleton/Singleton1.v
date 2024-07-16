(*** SPC ***)
Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef IPM.
Require Import sProp sWorld World SRF.
Require Import Singleton0 SingletonRA.
Require Import IProofMode.

Set Implicit Arguments.

Section SPC.
  Context `{_S: SingletonRA.t}.
  (* Goal False. *)

  (*
   *** Exmaple in pseudo-code style ***

        def singleton(): int :=
            return 1;
   *)
  
  Definition singletonA: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      Ret (Vint 1).

  Definition singleton_spec: fspec :=
    mk_fspec_inv 0 (
      fun _ _ => mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun varg => (⌜varg = ([]: list val)↑⌝ ∗ Ball)%I),
           (fun vret => (⌜vret = (Vint 1)↑⌝)%I)
      ))).

  Definition SingletonSbtb: list (string * fspecbody) :=
    [("singleton", mk_specbody singleton_spec (cfunU singletonA))].

  Definition SSingletonSem: SModSem.t :=
    {|
      SModSem.fnsems := SingletonSbtb;
      SModSem.initial_cond := Ready;
      SModSem.initial_st := Ret tt↑;
    |}.

  Definition SSingleton: SMod.t :=
    {|
      SMod.get_modsem := fun _ => SSingletonSem;
      SMod.sk := [("singleton", Gfun↑)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Singleton: HMod.t := (SMod.to_hmod GlobalStb SSingleton).

End SPC.