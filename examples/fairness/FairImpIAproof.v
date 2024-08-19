Require Import FairA FairI.
Require Import HoareDef SimModSem.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem ModSemE Behavior.
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
Require Import Mem1 STB Invariant.

Require Import IProofMode IRed ITactics.

Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Require Import WFLibLarge FairCounter.

Set Implicit Arguments.

Local Open Scope nat_scope.

Section SIMMODSEM.
  Context `{_W: CtxWD.t}.
        
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Definition Ist: Any.t -> Any.t -> iProp :=
    fun st_src st_tgt => (⌜st_src = tt↑ ∧ exists (iii: iimap nat nat_wf), st_tgt = iii↑⌝)%I.

  Ltac coapply :=
    iApply isim_progress;
    iApply isim_base;
    match goal with [|- context[_ _ _ _ _ (?st_src, _) (?st_tgt, _)]] =>
      iApply ("CIH" $! (@existT _ (λ _, _) st_src st_tgt)); eauto
    end.

  Lemma simF_fair:
    forall ii, 
    HModPair.sim_fun
      (FairA.HFair GlobalStb) (FairI.Fair ii)
      Ist "fair".
  Proof.
    simF_init FairA.HFair_unfold FairI.Fair_unfold FairA.fairF FairI.fairF.

    st_l. hss. iDestruct "ASM" as "(W & (% & %Y))". subst. hss. st_r. grind.
    iApply isim_progress.
        
    (* To prove a situation of infinity, use coinduction *)
    iStopProof.
    revert st_src st_tgt. apply combine_quant. (* boilerplate for coinduction *)
    eapply isim_coind.
    i. destruct a as [st_src st_tgt]. s.
    iIntros "(#(_ & CIH) & [IST W])".
    (* Now we can use a coinduction hypothesis *)
    
    rewrite// [X in isim _ _ _ _ _ _ _ _ (_, (interp_hEs_hAGEs _ _ X) >>= _) (_, _)] unfold_iter_eq.
    rewrite// [X in isim _ _ _ _ _ _ _ _ (_, _) (_, X >>= _)] unfold_iter_eq.
    st_r. destruct y.
    
    (* CASE 1: fair case *)
    {
      (* unneccessary part *)
      
      unfold FairCounter.Fair at 3. st_r.
      iDestruct "IST" as "%". des. subst. hss. st_r.
      iDestruct "GRT" as "%".
      st_l. st.
      coapply.
    }
    (* CASE 2: unfair case *)
    {
      unfold FairCounter.Fair at 3. st_r.
      iDestruct "IST" as "%"; des; subst; hss. st_r.
      iDestruct "GRT" as "%".
      des. unfold FairCounter.fair_update, ff in H. specialize (H 1). ss.

      (* induction on consecutive unfair case *)
      remember (iii 1) as chance. clear Heqchance. gen y.
      induction chance.
      { ii. inv H. }
      {
        ii. rewrite// [X in isim _ _ _ _ _ _ _ _ (_, _) (_, X >>= _)] unfold_iter_eq.
        st_r. destruct y2.
        (* If the next is fair case, the previous unfair case isn't the problem *)
        {
          st_r. unfold Fair at 3. st.
          iDestruct "GRT" as "%".
          coapply.
        }

        (* Consecutive unfair case *)
        {
          st_r. unfold Fair at 3. st_r.
          iDestruct "GRT" as "%". apply IHchance. clear IHchance.
          specialize (H0 1). ss. nia.
        }
      }
    }
  Qed.
  
  Theorem sim: forall ii, HModPair.sim (FairA.HFair GlobalStb) (FairI.Fair ii) Ist.
  Proof.
    ii. sim_init.
    - rewrite// FairA.HFair_unfold FairI.Fair_unfold. s.
      iIntros "E"; iFrame. unfold Ist. et.
    - iApply simF_fair. ss.
  Qed.
  
End SIMMODSEM.
