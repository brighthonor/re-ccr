Require Import HoareDef SimModSem SimModSemFacts.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import HTactics ProofMode IPM.
Require Import OpenDef.
Require Import Mem1 MemOpen STB.

Require Import Imp.
Require Import ImpNotations.
Require Import ImpProofs.

Require Import Client0 ClientImp.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.

  Import ImpNotations.

  Context `{Σ: GRA.t}.

  Let W: Type := Any.t * Any.t.

  Let wf: unit -> W -> Prop :=
    fun _ '(mrps_src0, mrps_tgt0) =>
      (<<SRC: mrps_src0 = tt↑>>) /\
      (<<TGT: mrps_tgt0 = tt↑>>)
  .

  Theorem correct:
    refines2 [ClientImp.Client] [Client0.Client].
  Proof.
    eapply adequacy_local2. econs; ss. i.
    Local Transparent syscalls.
    econstructor 1 with (wf:=wf) (le:=top2); et; ss.
    econs; ss.
    { init.
      unfold getintF, getint, cfunU.
      steps.
      rewrite unfold_eval_imp. steps.
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      red. esplits; et.
    }
    econs; ss.
    { init.
      steps.
      unfold putintF, putint, cfunU.
      steps.
      rewrite unfold_eval_imp. steps.
      destruct (intrange_64 z) eqn:WFZ.
      2:{ steps. }
      des_ifs.
      2:{ exfalso; apply n. solve_NoDup. }
      imp_steps.
      red. esplits; et.
    }
    Local Opaque syscalls.
    Unshelve. all:try exact 0. all: ss.
  Qed.

End SIMMODSEM.
