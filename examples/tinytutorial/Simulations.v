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

Section PROOF.
  Context `{_W: CtxWD.t}.
  Section ASSUME.
    Let Ist: Any.t -> Any.t -> iProp := fun _ _ => True%I.
    Let RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun '(sts, vs) '(stt, vt) => (Ist sts stt ∗ ⌜vs = vt⌝)%I.

    Variable DummyRA: URA.t. 
    Context `{@GRA.inG DummyRA Γ}. 
    Variable p q r: DummyRA.

    Definition dummy_src : itree hAGEs Any.t :=
      trigger (Assume (OwnM (p ⋅ r)));;;
      trigger (Guarantee (OwnM (q ⋅ r)));;;
      Ret tt↑.

    Definition dummy_tgt : itree hAGEs Any.t :=
      trigger (Assume (OwnM p));;;
      trigger (Guarantee (OwnM q));;;
      Ret tt↑.

    Goal ⊢ isim Ist [] [] ibot ibot RR false false (tt↑, dummy_src) (tt↑, dummy_tgt).
    Proof. 
      unfold dummy_src, dummy_tgt. iIntros.
      asm. iDestruct "ASM" as "[P R]".
      iSplitL "P". { iFrame. }
      grt. iSplitL "R GRT".
      { iCombine "GRT R" as "QR". iFrame. }
      steps. iSplit; eauto.
    Qed.
  End ASSUME.

  Section STATE.
    Let Ist: Any.t -> Any.t -> iProp := fun s t => ⌜s = t⌝%I.
    Let RR : (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun '(sts, vs) '(stt, vt) => (Ist sts stt ∗ ⌜vs = vt⌝)%I.

    Definition square: nat -> nat := fun i => i * i.

    Fixpoint square' i := 
      match i with
      | 0 => 0
      | S i' => square' i' + 2 * i' + 1
      end.

    Definition state_src : itree hAGEs Any.t :=
      st <- trigger sGet;;
      i <- st↓?;;
      let st := (square i)↑ in
      trigger (sPut st);;;
      Ret st.
    Definition state_tgt : itree hAGEs Any.t :=
      st <- trigger sGet;;
      i <- st↓?;;
      let st := (square' i)↑ in
      trigger (sPut st);;;
      Ret st.

    Goal ⊢ isim Ist [] [] ibot ibot RR false false (7↑, state_src) (7↑, state_tgt).
    Proof. 
      unfold state_src, state_tgt. iIntros.
      (* Try not to use 'steps' tactic *)
      steps. iSplit; eauto.
    Qed.

  End STATE.

  (* Make more examples using same template *)

  Section TEST.
    Let Ist: Any.t -> Any.t -> iProp := fun _ _ => emp%I. (* TODO *)
    Let RR : (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun '(sts, vs) '(stt, vt) => (Ist sts stt ∗ ⌜vs = vt⌝)%I.

    (*** Write your own (src/tgt) functions and prove the simulation ***)

    Definition src : itree hAGEs Any.t :=
      (* WRITE YOUR OWN CODE *)
      Ret tt↑.

    Definition tgt : itree hAGEs Any.t :=
      (* WRITE YOUR OWN CODE *)
      Ret tt↑.

    Goal ⊢ isim Ist [] [] ibot ibot RR false false (tt↑, state_src) (tt↑, state_tgt).
    Proof. Admitted.

  End TEST.

End PROOF.
