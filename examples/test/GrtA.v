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

Set Implicit Arguments.


Section A.
  Context `{_W: CtxWD.t}.

  (* Let Es := (hAPCE +' Es). *)

  Definition testF: list val -> itree hEs val :=
    fun varg =>
      Ret (Vint 2)
  .

  Definition test_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => 
        mk_simple (X := unit)
          (fun _ =>
            (ord_pure 0,
            (fun varg => (⌜varg = (@nil val)↑⌝)%I),
            (fun _ => (False)%I)))).

  Definition ChooseSbtb: list (string * fspecbody) :=
    [("test", mk_specbody test_spec (cfunU testF))].

  Definition SChooseSem: SModSem.t := {|
    SModSem.fnsems := ChooseSbtb;
    SModSem.initial_cond := emp;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SChoose: SMod.t := {|
    SMod.get_modsem := fun _ => SChooseSem;
    SMod.sk := [("test", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition _HChoose: HMod.t := (SMod.to_hmod GlobalStb SChoose).
  Definition HChoose := _HChoose.

  Lemma HChoose_unfold: HChoose = _HChoose.
  Proof. eauto. Qed.

  Global Opaque HChoose.

End A.
