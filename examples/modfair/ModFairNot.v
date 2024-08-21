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

  Definition unfairF: list (id -> Flag.t) -> itree hEs val :=
    fun _ =>
      Ret Vundef.

  Definition unfair_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => 
        mk_simple (X := nat)
          (fun (k: nat) =>
            (ord_top,
            (fun varg => (⌜exists ff: id -> Flag.t, varg = [ff]↑⌝)%I),
            (fun _ => (True)%I)))).

  Definition UnFairStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("fair", unfair_spec)].
  Defined.

  Definition UnFairSbtb: list (string * fspecbody) :=
    [("fair", mk_specbody unfair_spec (cfunU unfairF))].

  Definition SUnFairSem: SModSem.t := {|
    SModSem.fnsems := UnFairSbtb;
    SModSem.initial_cond := emp;
    SModSem.initial_st := initial_map↑;
  |}
  .

  Definition SUnFair: SMod.t := {|
    SMod.get_modsem := fun _ => SUnFairSem;
    SMod.sk := [("fair", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _HUnFair: HMod.t := (SMod.to_hmod GlobalStb SUnFair).
  Definition HUnFair := _HUnFair.

  Lemma HUnFair_unfold: HUnFair = _HUnFair.
  Proof. eauto. Qed.

  Global Opaque HUnFair.

End A.
Global Hint Unfold UnFairStb: stb.