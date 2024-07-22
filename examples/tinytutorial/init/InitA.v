Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef IPM.
Require Import sProp sWorld World SRF.
Require Import InitI InitRA.
Require Import IProofMode.

Set Implicit Arguments.

Section SPC.
  Context `{_I: InitRA.t}.


  (****** function body ******)
  Definition initF: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      _ <- trigger (sPut (1:Z)↑);;
    Ret Vundef.

  Definition incrF: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      st <- trigger sGet;; st <- st↓?;;
      _ <- trigger (sPut (st + 1)%Z↑);;
    Ret Vundef.

  Definition finalF: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      _ <- trigger (sPut 0↑)%Z;;
    Ret Vundef.


  (****** specs ******)
  Definition init_spec: fspec :=
    mk_fspec_inv 0 (
      fun _ _ => mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun _ => pending),
           (fun _ => callable)
    ))).

  Definition incr_spec: fspec := 
    mk_fspec_inv 0 (
      fun _ _ => mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun _ => callable),
           (fun _ => callable)
    ))).

  Definition final_spec: fspec :=
    mk_fspec_inv 0 (
      fun _ _ => mk_simple (X:=unit)
      (fun _ =>
         (ord_top,
           (fun varg => callable),
           (fun _ => emp%I)
    ))).


  Definition InitSbtb: list (string * fspecbody) :=
    [
      ("init", mk_specbody init_spec (cfunU initF));
      ("incr", mk_specbody incr_spec (cfunU incrF));
      ("final", mk_specbody final_spec (cfunU finalF))
    ].

  Definition InitSem: SModSem.t :=
    {|
      SModSem.fnsems := InitSbtb;
      SModSem.initial_cond := callable;
      SModSem.initial_st := Ret tt↑;
    |}.

  Definition SInit: SMod.t :=
    {|
      SMod.get_modsem := fun _ => InitSem;
      SMod.sk := [("init", Gfun↑); ("incr", Gfun↑); ("final", Gfun↑)];
    |}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Init: HMod.t := (SMod.to_hmod GlobalStb SInit).

End SPC.