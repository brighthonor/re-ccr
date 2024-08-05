Require Import Coqlib.
Require Import STS.
Require Import Behavior.

Require Import Skeleton.
Require Import PCM IPM.
Require Import Any.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import HPSim.
Require Import World sWorld.
Require Import ISimCore ITacticsInternal.
Require Import ModuleInternal.
Require Import BasicEvents Events.

From stdpp Require Import coPset gmap.

(************ User Tactics **************)
Ltac sim_init := econs; eauto; ii; econs; cycle 1; [s|sim_split].
Tactic Notation "simF_init" constr(LS) constr(LT) reference(FS) reference(FT) :=
  unfold HModPair.sim_fun; i;
  rewrite// [in alist_find _ _]LS; s;
  rewrite// [in alist_find _ _]LT; s;
  unfold FS; unfold FT;
  i; iIntros "IST"; unfold cfunU, interp_sb_hp, HoareFun, ccallU; s.

Ltac st := repeat _st.

Ltac force_l := try (prep; _force_l).
Ltac force_r := try (prep; _force_r).

Ltac inline_l := prep; iApply isim_inline_src; [eauto|]; unfold interp_sb_hp, HoareFun.
Ltac inline_r := prep; iApply isim_inline_tgt; [eauto|]; unfold interp_sb_hp, HoareFun.

Ltac call := prep; iApply isim_call; iSplitL "IST"; [ |iIntros "% % %"; iIntrosFresh "IST"]. 

(* COMMENT: Should st_l, st_r be kept in here, or moved to temporary? *)
Ltac st_l := let IT := fresh "__IT" in
  match goal with [|- _ (_ (_, _) (_, ?itgt))] => set (IT := itgt) end;
  st;
  unfold IT; clear IT.
Ltac st_r := let IT := fresh "__IT" in
  match goal with [|- _ (_ (_, ?isrc) (_, _))] => set (IT := isrc) end;
  st;
  unfold IT; clear IT.

Ltac apc_r :=
  rewrite interp_hAGEs_hapc;
  st_r; unfold HoareAPC; st_r; rewrite unfold_APC; st_r;
  match goal with [b: bool|-_] => destruct b end;
  [|unfold guarantee, triggerNB; st_r;
    match goal with [v: void|-_] => destruct v end].

Ltac hss :=
  ss;
  try (unfold run_l; rewrite !Any.pair_split; fold run_l);
  try (unfold run_r; rewrite !Any.pair_split; fold run_r);
  try (rewrite !Any.upcast_downcast in * );
  (repeat match goal with [G: Any.downcast _ = Some _ |-_] =>
    apply Any.downcast_upcast in G; inv G; ss
   end);
  (repeat match goal with [G: Any.upcast (_:?T) = Any.upcast (_:?T) |-_] =>
    apply Any.upcast_inj in G; destruct G as [_ G]; red in G; depdes G; ss
   end);
  (repeat match goal with [G: Some _ = Some _ |- _] =>
    depdes G; ss
   end).

(***** Temporary Tactics ( Not recommended in a final proof. Use only for excersize. ) *****)
Ltac prep := cbn; ired_both.
Ltac steps := repeat _steps.
Ltac ired := repeat _ired.
Ltac choose_l := iApply isim_choose_src.
Ltac choose_r := iApply isim_choose_tgt; iIntros "%".
Ltac take_l := iApply isim_take_src; iIntros "%".
Ltac take_r := iApply isim_take_tgt.
Ltac asm_l := iApply isim_assume_src; iIntrosFresh "ASM".
Ltac asm_r := iApply isim_assume_tgt.
Ltac grt_l := iApply isim_guarantee_src.
Ltac grt_r := iApply isim_guarantee_tgt; iIntrosFresh "GRT".
Ltac choose := prep; choose_r; choose_l.
Ltac take := prep; take_l; take_r.
Ltac asm := prep; asm_l; asm_r.
Ltac grt := prep; grt_r; grt_l.

(**** TODO ****)
(* A tactic to handle meta variables *)
(* Tactics to handle APC. (APC in src / in tgt / ord_pure 0 / ord_pure n / ....  ) *)

(************ User Notations **************)


From iris.proofmode Require Import coq_tactics environments.

Global Arguments Envs _ _%proof_scope _%proof_scope _.
Global Arguments Enil {_}.
Global Arguments Esnoc {_} _%proof_scope _%string _%I.

Local Notation world_id := positive.
Local Notation level := nat.

(*** TODO: 
          What else should be displayed? 
          Simplify (hide) k-trees

***)

(*** isim ***)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 E2 _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (_ _ (isim Ist _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

(* additional *) 
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_sep P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '∗'  'ISIM' ").

Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------isim-------------------------------'  P '-∗' 'ISIM'"
:=
  (environments.envs_entails (Envs E1 E2 _) (bi_wand P (isim _ _ _ _ _ _ _ _ (st_src, _) (st_tgt, _))))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------isim-------------------------------' '//' P  '-∗'  'ISIM' ").


(****************************************************************************************************)

(* Section TEST.
Context `{CtxWD.t}.

Let Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
Let RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.
Variable iP: iProp.

Goal ⊢ ((⌜False⌝∗iP∗iP) -∗ iP ∗ isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "(#A & B & C)". Unset Printing Notations.
iAssert (iP -* world 1 0 ⊤) as "H". { admit. }
iPoseProof ("H" with "B") as "B". iRevert "B". Unset Printing Notations. 
clarify. Admitted.
Goal ⌜False⌝%I ⊢ (isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "#H". Admitted.
Goal ⊢ (iP -∗ isim Ist [] [] ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "H". Admitted.
Goal ⊢ (isim Ist [] [] ibot ibot RR false false (tt↑, trigger (Assume (⌜False⌝%I));;; Ret tt↑ >>= (fun r => Ret r)) (tt↑, Ret tt↑)).
Proof. iIntros. steps. Admitted.



Goal ⊢ ((⌜False⌝**iP) -∗ wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "[#A B]". clarify. Qed.
Goal ⌜False⌝%I ⊢ (wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "#H". Admitted.
Goal ⊢ (iP -∗ wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, Ret tt↑) (tt↑, Ret tt↑)).
Proof. iIntros "H". Admitted.
Goal ⊢ (wsim Ist [] [] 1 0 ⊤ ibot ibot RR false false (tt↑, trigger (Assume (⌜False⌝%I));;; Ret tt↑ >>= (fun r => Ret r)) (tt↑, Ret tt↑)).
Proof. iIntros. steps. Admitted.



End TEST. *)


