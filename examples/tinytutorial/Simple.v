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
Require Import SimModSem.
Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
Require Import OpenDef STB.
Require Import sProp sWorld World SRF.

Require Import IProofMode ITactics.

From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.

(*** IMP ***)
Section SIMPLE0.
  Context `{_W: CtxWD.t}.

  Definition simple0_prog
    : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      let r := (Vint 1) in
      r <- (vadd r (Vint 2))?;;
      Ret r.

  Definition simple0_call : list val -> itree hAGEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      r <- ccallU "sim" (nil: list val);;
      Ret r.

  Definition Simple0Sem: HModSem.t := {|
    HModSem.fnsems := [("sim", cfunU simple0_prog); ("call", cfunU simple0_call)]; (* function semantics *)
    HModSem.initial_st := Ret tt↑; (* initial state *)
    HModSem.initial_cond := emp
  |}.

  Definition Simple0: HMod.t := {|
    HMod.get_modsem := fun _ => Simple0Sem; (* Module Semantics *)
    HMod.sk := [("sim", Gfun↑); ("call", Gfun↑)]; (* same with module semantics *)
  |}.

End SIMPLE0.

(*** SPC ***)
Section SIMPLE1.
  Context `{_W: CtxWD.t}.

  Definition simple1_prog
    : list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      Ret (Vint 3).
    
  Definition simple1_call: list val -> itree hEs val :=
    fun args =>
      _ <- (pargs [] args)?;;
      r <- ccallU "sim" (nil: list val);;
      Ret r.

  Definition simple1_prog_spec: fspec :=
    mk_fspec_inv 0 
    (fun _ _ => mk_simple (X:=unit)
              (fun _ => (
                   ord_top,
                   (fun varg =>
                      (⌜varg = ([]: list val)↑⌝)%I
                   ),
                   (fun vret =>
                      (⌜vret = (Vint 3)↑⌝)%I
                   )
              ))).
  
  Definition simple1_call_spec: fspec :=
    mk_fspec_inv 0 
    (fun _ _ => mk_simple (X:=unit)
              (fun _ => (
                   ord_top,
                   (fun varg =>
                      (⌜varg = ([]: list val)↑⌝)%I
                   ),
                   (fun vret =>
                      (⌜vret = (Vint 3)↑⌝)%I
                   )
              ))).              

  Definition SimpleSbtb: list (gname * fspecbody) :=
    [("sim", mk_specbody simple1_prog_spec (cfunN simple1_prog)); ("call", mk_specbody simple1_call_spec (cfunU simple1_call))].

  Definition SSimpleSem: SModSem.t := {|
    SModSem.fnsems := SimpleSbtb;
    SModSem.initial_cond := emp;
    SModSem.initial_st := Ret tt↑;
  |}
  .

  Definition SSimple: SMod.t := {|
    SMod.get_modsem := fun _ => SSimpleSem;
    SMod.sk := [("sim", Gfun↑); ("call", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition Simple: HMod.t := (SMod.to_hmod GlobalStb) SSimple.
  
End SIMPLE1.


(*** PROOF ***)

Section PROOF.

  Context `{_W: CtxWD.t}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Hypothesis STB_sim: forall sk, (GlobalStb sk) "sim" = Some simple1_call_spec.



  Let Ist: Any.t -> Any.t -> iProp :=
    fun _ _ => emp%I.

  (* Refinement Proof *)
  Theorem sim: HModPair.sim (Simple GlobalStb) (Simple0) Ist.
  Proof.
    sim_init.
    - (* invaraint *)
      iIntros. iSplit; eauto. steps. eauto.
    - (* fun 1 *)
      unfold simple0_prog, simple1_prog, interp_sb_hp, cfunU, cfunN, HoareFun. s.
      steps. iDestruct "ASM" as "(W & % & %)". subst.
      steps. force. force. iSplitL "W".
      { iFrame. eauto.  }
      steps. iFrame. eauto.
    - (* fun 2 *)
      unfold simple0_call, simple1_call, interp_sb_hp, cfunU, cfunN, ccallU, HoareFun. s.
      steps. iDestruct "ASM" as "(W & % & %)". subst. rewrite STB_sim.
      steps. unfold HoareCall.
      steps. 
      force. instantiate (1:= mk_meta _ _ _).
      force. force. iSplitL "W".
      { iFrame. iSplit; eauto. }
      steps. call. { eauto. }
      steps. iDestruct "ASM" as "(W & % & %)". subst.
      rewrite Any.upcast_downcast in G1. inv G1.
      force. force. iSplitL "W".
      { iFrame. eauto. }
      steps. iFrame. eauto.
      Unshelve. eauto.
  Qed. 



