Require Import Events MapHeader MapI MapM MapA SimModSem MapIMproof MapMAproof.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM IPM.
Require Import Behavior.
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

Require Import STB.
Require Import Mem1.

Require Import SimModSemFacts ISim Mod.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.


Set Implicit Arguments.

Local Open Scope nat_scope.

Section PROOF.
  (**** TODO: State theorem & lemmas required for proof's transitivity. ****)

  (* Context `{_M: MapRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Theorem correct: refines2 [MapI.Map] [MapA.Map (fun _ => to_stb (MemStb ++ MapStb))].
  Proof.
    etrans.
    { eapply MapIMproof.correct.
      { i. eapply app_incl. }
      { instantiate (1:=MapStbM). i. ss. stb_tac. auto. }
    }
    { eapply MapMAproof.correct.
      { i. stb_tac. auto. }
      { i. stb_tac. auto. }
      { r. i.
        autounfold with stb in FIND; autorewrite with stb in FIND. ss.
        rewrite ! eq_rel_dec_correct in *. ss.
        repeat match goal with
               | H: context[ match (string_Dec ?x ?y) with _ => _ end ] |- _ =>
                   destruct (string_Dec x y);
                   [subst; ss; clarify;
                    try by (r in PURE; des; ss; unfold is_pure in *; des_ifs;
                            r in PURE; uipropall; des; clarify; r in PURE1; uipropall; des; clarify);
                    try by (stb_tac; ss)|]
               end.
        all: stb_tac; ss.
      }
    }
  Qed. *)
End PROOF.
