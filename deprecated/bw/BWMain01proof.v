Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import Relation_Definitions.
Require Import HoareDef STB BW1 BWMain0 BWMain1 SimModSem.

(*** TODO: export these in Coqlib or Universe ***)
Require Import Relation_Operators.
Require Import RelationPairs.
From ITree Require Import
     Events.MapDefault.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import TODOYJ.
Require Import HTactics.
Require Import ProofMode.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG BW1.bwRA Σ}.

  Let W: Type := Any.t * Any.t.

  Let wf: _ -> W -> Prop :=
    @mk_wf
      _
      unit
      (fun _ _ _ => (True)%I)
  .

  Theorem correct: ModSemPair.sim BWMain1.MainSem BWMain0.MainSem.
  Proof.
    econstructor 1 with (wf:=wf) (le:=top2); et; swap 2 3.
    { ss. }
    { exists tt. ss. red. econs; et; ss. red. uipropall. }

    econs; ss.
    { unfold mainbody, mainF, ccallU, hcall. init. harg.
      mDesAll. des; clarify. steps.
      destruct (to_stb (BWStb ++ ClientStb ++ MainStb) "getbool") eqn:T; unfold to_stb in T; stb_tac; clarify.
      steps. hcall _ _ _ with ""; ss.
      { splits; ss. ss. }
      mDesAll. clarify. steps.
      steps. unfold unbool in *.
      (* rewrite _UNWRAPN. *)
      steps. astart 3.
      (* TODO: use bind rule to reduce redundancy *)
      des_ifs.
      { steps. acatch.
        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify. steps.
        acatch.

        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify.
        rewrite Any.upcast_downcast in *. clarify. steps.
        astop. steps. force_l. eexists. steps.
        force_l; et. steps.
        destruct (to_stb (BWStb ++ ClientStb ++ MainStb) "putint") eqn:T; stb_tac; clarify.
        steps.

        hcall ord_top _ _ with ""; auto.
        mDesAll. steps. rewrite _UNWRAPN1. steps.
        steps. hret _; ss.
      }
      { steps. acatch.
        hcall _ _ _ with "*"; auto.
        { eauto with ord_step. }
        mDesAll. clarify. steps. astop.
        steps. force_l. eexists. steps.
        force_l; et. steps.
        destruct (to_stb (BWStb ++ ClientStb ++ MainStb) "putint") eqn:T; stb_tac; clarify.
        steps.

        hcall ord_top _ _ with ""; auto.
        mDesAll. subst. steps. rewrite _UNWRAPN0. steps.
        steps. hret _; ss.
      }
    }
    Unshelve. all: ss.
  Qed.

End SIMMODSEM.
