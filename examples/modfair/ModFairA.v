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
Require Import ProofMode IProofMode.

Require Import FairCounter WFLibLarge.

Set Implicit Arguments.


Section A.
  Context `{_W: CtxWD.t}.

  Variable id: ID.
  Variable wf: WF.

  Variable initial_map: iimap id wf.

  (* Let Es := (hAPCE +' Es). *)

  Definition fargs (args: list (id -> Flag.t)) :=
    match args with
    | [] => None
    | hd :: _ => Some hd
    end.
    
  Definition fairF: list (id -> Flag.t) -> itree hEs val :=
    fun args =>
      `f: (id -> Flag.t) <- (fargs args)?;;
      prev <- trigger sGet;; prev <- prev↓?;;
      next <- trigger (Choose (iimap id wf));;
      _ <- trigger (Fair f prev next);;
      _ <- trigger (sPut next↑);;
      Ret Vundef
  .

  Definition fair_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => 
        mk_simple (X := unit)
          (fun _ =>
            (ord_top,
            (fun varg => (⌜exists ff: id -> Flag.t, varg = [ff]↑⌝)%I),
            (fun _ => (True)%I)))).

  Definition FairStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("fair", fair_spec)].
  Defined.

  Definition FairSbtb: list (string * fspecbody) :=
    [("fair", mk_specbody fair_spec (cfunU fairF))].

  Definition SFairSem: SModSem.t := {|
    SModSem.fnsems := FairSbtb;
    SModSem.initial_cond := emp;
    SModSem.initial_st := initial_map↑;
  |}
  .

  Definition SFair: SMod.t := {|
    SMod.get_modsem := fun _ => SFairSem;
    SMod.sk := [("fair", Gfun↑)];
  |}
  .

  Definition _HFair: HMod.t := (SMod.to_hmod (fun _ => to_stb []) SFair).
  Definition HFair := _HFair.

  Lemma HFair_unfold: HFair = _HFair.
  Proof. eauto. Qed.

  Global Opaque HFair.

End A.
Global Hint Unfold FairStb: stb.
