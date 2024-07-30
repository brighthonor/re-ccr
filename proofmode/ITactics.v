Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef OpenDef STB SimModSem.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode Invariant.
Require Import HPSim.
Require Import World sWorld.
Require Import IProofMode ITacticsAux.

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
Ltac inline_l := prep; _inline_l; [eauto|]; unfold interp_sb_hp, HoareFun.
Ltac inline_r := prep; _inline_r; [eauto|]; unfold interp_sb_hp, HoareFun.
Ltac call := prep; _call; iSplitL "IST"; [ |iIntros "% % %"; iIntrosFresh "IST"]. 
(* Ltac call H := prep; _call; iSplitL H; [ |iIntros "% % %"; iIntrosFresh H]. *) (* Try to overload 'call "string"' *)
Ltac apc :=
  st; rewrite interp_hAGEs_hapc;
  st; unfold HoareAPC; st; rewrite unfold_APC; st;
  match goal with [b: bool|-_] => destruct b end;
  [|unfold guarantee, triggerNB; st;
    match goal with [v: void|-_] => destruct v end].

Ltac hss :=
  try (unfold ModSem.run_l; rewrite !Any.pair_split; fold ModSem.run_l);
  try (unfold ModSem.run_r; rewrite !Any.pair_split; fold ModSem.run_r);
  try (rewrite !Any.upcast_downcast in * ).

(***** Temp *****)
Ltac prep := cbn; ired_both.
Ltac steps := repeat _steps.
Ltac ired := repeat _ired.
Ltac force := force_l; force_r.
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
(* destruct? simplify? the linked module states *)
Ltac des_link := unfold ModSem.run_l, ModSem.run_r; rewrite ! Any.pair_split; fold ModSem.run_l; fold ModSem.run_r. 
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





(*** wsim ***)
Notation "E1 '------------------------------------------------------------------□' E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 E2 _) (wsim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E1 '------------------------------------------------------------------□' st_src st_tgt '-------------------------------wsim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs E1 Enil _) (wsim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E1 '------------------------------------------------------------------□' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "E2 '------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil E2 _) (wsim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
    (at level 50,
     format "E2 '------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").

Notation "'------------------------------------------------------------------∗' st_src st_tgt '-------------------------------wsim-------------------------------'  itr_src itr_tgt"
:=
  (environments.envs_entails (Envs Enil Enil _) (wsim _ _ _ _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt)))
  (* (environments.envs_entails (Envs Enil _) (world _ _ _ -* isim _ _ _ _ _ _ _ _ (st_src, itr_src) (st_tgt, itr_tgt))) *)
    (at level 50,
     format "'------------------------------------------------------------------∗' '//' st_src '//' st_tgt '//' '-------------------------------wsim-------------------------------' '//' itr_src '//' '//' '//' itr_tgt '//' ").



(****************************************************************************************************)





(*** TODO: move the following lemma ***)

  Lemma isim_reflR `{Σ: GRA.t} R Ist fnsems_src fnsems_tgt st_src st_tgt (itr: itree _ R):
    IstProd Ist IstEq st_src st_tgt -∗
      isim (IstProd Ist IstEq) fnsems_src fnsems_tgt ibot ibot
      (λ '(st_src, v_src) '(st_tgt, v_tgt), IstProd Ist IstEq st_src st_tgt ** ⌜v_src = v_tgt⌝) false false
      (st_src, translate (HModSem.emb_ ModSem.run_r) itr)
      (st_tgt, translate (HModSem.emb_ ModSem.run_r) itr).
  Proof.
    Local Ltac CIH :=
      iApply isim_progress; iApply isim_base;
      match goal with [|- context[_ ?R _ _ _ (?st_src, _ _ ?itr) (?st_tgt, _)]] =>
         iApply ("CIH" $! (@existT _ (λ _, _) itr (@existT _ (λ _, _) st_src st_tgt))); eauto
      end.
      
    revert st_src st_tgt. apply combine_quant.
    revert itr. apply combine_quant.
    
    eapply isim_coind. i. destruct a as [itr [st_src st_tgt]]. s.
    iIntros "(#(_ & CIH) & IST)".
    assert (CASE := case_itrH _ itr); des; subst.
    - st. eauto.
    - st. CIH.
    - st. force. iFrame. CIH.
    - st. force. iFrame. CIH.
    - destruct c. st. call; eauto. CIH.
    - destruct s. st.
      iPoseProof (ist_eq_run_r with "IST") as "(%EQ & IST)". rewrite <-EQ.
      CIH.
    - destruct e; st; force; CIH.
  Qed.












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



(* Section TEST.
  Import HModSem HMod.
  Local Notation world_id := positive.
  Local Notation level := nat.

  Context `{CtxWD.t}.

  Definition mss0: HModSem.t := {|
    fnsems := [("f0", (fun _ => Ret tt↑))];
    initial_st := Ret tt↑;
    initial_cond := ⌜True⌝%I;
  |}.

  Definition mss1: HModSem.t := {|
    fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
    initial_st := Ret tt↑;
    initial_cond := ⌜True⌝%I;
  |}.

  Definition mtt0: HModSem.t := {|
    fnsems := [("f0", (fun _ => Ret tt↑))];
    initial_st := Ret tt↑;
    initial_cond := ⌜True⌝%I;
  |}.

  Definition mtt1: HModSem.t := {|
    fnsems := [("f1", (fun _ => Ret tt↑)); ("main", (fun _ => trigger (Call "f0" tt↑) >>= (fun _ => trigger (Call "f1" tt↑))))];
    initial_st := Ret tt↑;
    initial_cond := ⌜True⌝%I;
  |}.

  Definition ms0 := {|
    get_modsem := fun _ => mss0;
    sk := Sk.unit;
  |}.

  Definition ms1 := {|
    get_modsem := fun _ => mss1;
    sk := Sk.unit;
  |}.

  Definition mt0 := {|
    get_modsem := fun _ => mtt0;
    sk := Sk.unit;
  |}.

  Definition mt1 := {|
    get_modsem := fun _ => mtt1;
    sk := Sk.unit;
  |}.

  Definition Ist: Any.t -> Any.t -> iProp := fun _ _ => ⌜True⌝%I.
  Definition RR: (Any.t * Any.t) -> (Any.t * Any.t) -> iProp := fun _ _ => ⌜True⌝%I.

  Goal HModPair.sim (HMod.add ms0 ms1) (HMod.add mt0 mt1) Ist.
  Proof.
    (* econs; ss.
    ii. econs. 
    { econs.
      { econs; ss.  
        grind. iIntros. steps. eauto. 
      }
      econs.
      { econs; ss. grind.
        iIntros. steps; et. 
      }
      econs; ss. econs; ss. grind.
      iIntros. steps!. iSplitL; et. iIntros.
      steps. inline_l. inline_r. steps; eauto.
    }
    ss. iIntros.
    iSplitL; eauto. steps; eauto. *)
  Admitted.
  (* Qed. *)


End TEST.
 *)
