Require Import HoareDef STB HCannonRA HCannon0 HCannon1.
Require Import Coqlib.
Require Import ImpPrelude.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
Require Import ProofMode.
Require Import HPSim IProofMode.

Set Implicit Arguments.



Section SIMMODSEM.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG CannonRA Σ}.

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Variable o: ord.

  (* state Invariant *)
  Let Ist: Any.t -> Any.t -> iProp :=
        fun st_src st_tgt => ((⌜st_src = (1: Z)↑ /\ st_tgt = (1: Z)↑⌝ ** OwnM (Ready))
                                ∨ OwnM (Fired))%I
  .

  (* return relation *)
  Let RR : (Any.t * Any.t) -> (Any.t * Any.t) -> iProp :=
    fun '(st_src, ret_src) '(st_tgt, ret_tgt) => ⌜st_src = (1: Z)↑ /\ st_tgt = (1: Z)↑⌝ ** ⌜ret_src = ret_tgt⌝%I.

  Theorem correct: IModPair.sim HCannon0.Cannon (HCannon1.Cannon GlobalStb o) Ist RR.
  Proof.
    econs; et. i. red.
    econs; ss.
    {
      econs.
      {
        econs; ss. red. ii. iIntros. s.
        unfold cfunU, cfunN, fire_body.
        unfold HCannon0.fire_body at 2.
        unfold sGet, sPut.
        steps. ired_. steps. subst. unfold HCannon0.div in G1. 
        ired_. unfold sGet. steps. grind.
        assert ((1 `div` y2)%Z = 1). 
         

        
      } 
    }
    { unfold Ist.  }

  Theorem correct: refines2 [Cannon0.Cannon] [Cannon1.Cannon GlobalStb].
  Proof.
    (* proof using local simulation *)
    eapply adequacy_local2. econs; ss. i. red.
    econstructor 1 with (le:=le) (wf:=mk_wf wf); et; ss; cycle 1.

    (* initial state *)
    { exists tt. econs. eapply to_semantic.
      iIntros "H". iLeft. iSplitR; ss. }

    (* function "fire" *)
    econs; ss. econs; ss. red.
    (* use IPM *)
    apply isim_fun_to_tgt; auto. i; ss.
    (* state relation * precondition ⊢ isim (state relation* postcondition) p_src p_tgt *)
    unfold Cannon0.fire_body, Cannon1.fire_body.
    iIntros "[INV PRE]".
    iDestruct "PRE" as "[[% BALL] %]". subst.
    iEval (unfold inv_with, wf) in "INV".
    iDestruct "INV" as (w1) "[[[% READY] | FIRED] _]".
    { des; subst. hred_l. hred_r.
      iApply isim_pget_tgt. hred_r.
      iApply isim_syscall. iIntros (_).
      hred_l. hred_r.
      iApply isim_pput_tgt. hred_r.
      iApply isim_ret. iSplit.
      { iApply inv_with_current. iEval (unfold wf).
        iRight. iCombine "READY" "BALL" as "FIRED".
        iEval (rewrite <- ReadyBall). iApply "FIRED".
      }
      { iPureIntro. auto. }
    }
    { iCombine "FIRED" "BALL" as "FALSE".
      iPoseProof (OwnM_valid with "FALSE") as "%".
      exfalso. eapply FiredBall; auto.
    }
  Qed.

  (* isim *)
  (*   (* state relation *) *)
  (*   le (* world future *) wf (* state relation *) w (* current world *) *)
  (*   (* conditions for functions *) *)
  (*   mn (* current module name *) conds (* conditions *) o (* maximal call depth (for termination) *) *)
  (*   (* for coinduction *) *)
  (*   (r, g, f_src, f_tgt) *)
  (*   (* post condition : state_src -> state_tgt -> R_src -> R_tgt -> iProp *) *)
  (*   Q *)
  (*   (* source program : state_src * itree E R_src *) *)
  (*   (st_src, prog_src) *)
  (*   (* target program : state_tgt * itree E R_tgt*) *)
  (*   (st_tgt, prog_tgt) *)

End SIMMODSEM.
