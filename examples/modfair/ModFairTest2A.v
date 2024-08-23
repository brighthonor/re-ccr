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

Require Import FairCounter WFLibLarge ModFairA.

Set Implicit Arguments.


Section A.

  Context `{_W: CtxWD.t}.

  Definition ff (n: nat): Flag.t :=
    if (n =? 0)%nat then Flag.success else 
      if (n =? 1)%nat then Flag.fail else Flag.emp.

  Definition testF: list val -> itree hEs val :=
    fun _ =>
      (* tau for progress *)
      tau;; _ <- 
      (ITree.iter
        (fun (_: unit) =>
          `b: bool <- trigger (Choose bool);;
          if b
          then
            `_: val <- (ccallU "fair" [ff]);;
            _ <- trigger (Syscall "print" [Vint 42]↑ top1);;
            Ret (inl tt: unit + unit)
          else 
            `_: val <- (ccallU "fair" [ff]);;
            Ret (inl tt: unit + unit)
      ) tt);;
      Ret Vundef
  .

  Definition fair_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => 
        mk_simple (X := nat)
          (fun (k: nat) =>
            (ord_top,
            (fun varg => (⌜varg = (@nil val)↑⌝)%I),
            (fun _ => (True)%I)))).

  Definition FairStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("test", fair_spec)].
  Defined.

  Definition FairSbtb: list (string * fspecbody) :=
    [("test", mk_specbody fair_spec (cfunU testF))].

  Definition SFairSem: SModSem.t := {|
    SModSem.fnsems := FairSbtb;
    SModSem.initial_cond := emp;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SFair: SMod.t := {|
    SMod.get_modsem := fun _ => SFairSem;
    SMod.sk := [("test", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _HFair: HMod.t := (SMod.to_hmod GlobalStb SFair).
  Definition HFair := _HFair.

  Lemma HFair_unfold: HFair = _HFair.
  Proof. eauto. Qed.

  Global Opaque HFair.

End A.
Global Hint Unfold FairStb: stb.