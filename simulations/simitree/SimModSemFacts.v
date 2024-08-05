Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
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
Require Import Any.

Require Import BasicEvents ModuleInternal Mod.
Require Import SimGlobal SimGlobalFacts.
Require Import Red IRed.
Require Import SimModSem SimModSemFacts0.
Require Import ModSemFacts.
Import TAC.

Section ADEQUACY.
  (* Context {CONF: EMSConfig}. *)

  Lemma sim_ctx_mod
    ctx md1 md2
    (SIM: ModPair.sim md1 md2)
  :
    ModPair.sim (Mod.add md1 ctx) (Mod.add md2 ctx).
  Proof.
    inv SIM.
    econs; et.
    - i. ss. hexploit (sim_modsem sk); et.
      2: { ii. des. apply sim_ctx; et. }
      unfold Sk.incl, Sk.add in *. i. ss.
      apply SKINCL.
      rewrite in_app_iff. et.
    - r. ss. unfold Sk.add. ss.
      rewrite sim_sk. et.
  Qed.

  Lemma adequacy_mod
          md_src md_tgt
          (CONF: EMSConfig)
          (SIM: ModPair.sim md_src md_tgt)
    :
    <<REF: Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src) >>
    .
  Proof.
    ii. unfold Mod.compile in *.
    destruct (classic (ModSem.wf (Mod.enclose (md_src)) /\ Sk.wf (Mod.sk md_src))).
    2: { eapply ModSem.initial_itr_not_wf. ss. }
    ss. des. 
    pose (sk_tgt := (Mod.sk (md_tgt))).
    pose (sk_src := (Mod.sk (md_src))).
    assert (SKEQ: sk_src = sk_tgt).
    { unfold sk_tgt, sk_src. inv SIM. et. }
    unfold Mod.enclose in *. fold sk_src in H. inv H.
    inv SIM. hexploit (sim_modsem (Sk.canon sk_tgt)).
    { etrans; [|eapply Sk.sort_incl]. ss. }
    { ss. rewrite sim_sk in H0.
      clear - H0.
      unfold Sk.wf in *. ss.
      eapply Permutation.Permutation_NoDup; [|et].
      eapply Permutation.Permutation_map.
      eapply Sk.SkSort.sort_permutation. }
    i. des.
    inv H. ss.

    assert (WFTGT: Mod.wf md_tgt).
    { rr. unfold Mod.enclose. ss. fold sk_tgt. 
      rewrite SKEQ in *. split; auto.
      2: { rewrite <-SKEQ. unfold sk_src. et. }
      econs.
      match goal with
        | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0
      end; auto.
      eapply Forall2_eq. eapply Forall2_apply_Forall2; et.
      i. destruct a, b. inv H. ss.
    }

    des.

    eapply adequacy_local_aux in PR; et.
    - i. esplits.
      pose (ms_src := Mod.get_modsem md_src (Sk.sort (Mod.sk md_src))).
      pose (ms_tgt := Mod.get_modsem md_tgt (Sk.sort (Mod.sk md_tgt))).
      fold ms_src ms_tgt.
      rewrite <- SKEQ in sim_fnsems at 1.
      unfold sk_src, sk_tgt in sim_fnsems.
      fold ms_src ms_tgt in sim_fnsems.
      hexploit sim_fnsems. i.

      destruct (alist_find fn (ModSem.fnsems ms_src)) eqn:SRC; destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn:TGT; et.
      2: {
        right.
        eapply alist_find_some in SRC.
        rewrite <- sim_sk in sim_fnsems.
        (* eapply alist_find_none in TGT. *)
        eapply Forall2_In_l with (a:= (fn, i)) in sim_fnsems; et.
        inv sim_fnsems. inv H1.
        inv H3. inv H1.
        destruct x. ss. clarify.
        apply alist_find_none with (v:=i0) in TGT. clarify. 
      }
      right. esplits; et.

      hexploit SRC. hexploit TGT. i.
      apply alist_find_some in H1, H2.

      rewrite <- sim_sk in sim_fnsems.

      eapply Forall2_In_l with (a:=(fn, i)) in sim_fnsems; et.
      eapply Forall2_In_r with (b:=(fn, i0)) in H; et.
      inv sim_fnsems. inv H.
      destruct x, x1.
      inv H3. inv H5. inv H3. ss.
      inv H4. inv H7. inv H4. ss. clarify.
      unfold "@@2" in H5, H6. ss.
      (* apply NoDup_map_inv in wf_fnsems. *)
      unfold sk_src in wf_fnsems.
      fold ms_src in wf_fnsems.
      rewrite <- sim_sk in H3.
      eapply alist_find_some_iff  with (k:=s) (v:=i2) in wf_fnsems; et.
      rewrite SRC in wf_fnsems. clarify. apply H5.
    (* - inv sim_initial. econs. econs.
      2: { fold sk_src sk_tgt. rewrite SKEQ. apply H. }
      instantiate (1:= x). refl. *)
    - unfold sk_src, sk_tgt in *. rewrite sim_sk. eapply sim_initial.
    Qed.


  Theorem adequacy_local_strong md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
    <<CR: (refines_strong md_tgt md_src)>>.
  Proof.
    ii. apply sim_ctx_mod with (ctx:=ctx) in SIM.
    pose (Mod.add md_src ctx) as mds.
    pose (Mod.add md_tgt ctx) as mdt.
    fold mds. fold mdt in PR.
    apply adequacy_mod with (md_src := mds) in PR; et.
  Qed.

  Context {CONF: EMSConfig}.

  Theorem adequacy_local md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines md_tgt md_src)>>
  .
  Proof.
    eapply refines_strong_refines.
    eapply adequacy_local_strong; et.
  Qed.

  Corollary adequacy_local_list_strong
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    (* apply adequacy_local_strong. *)

  (* Admitted. *)


    r. induction FORALL; ss.
    { ii. auto. }

      destruct l eqn: L, l' eqn: L'.
      - apply adequacy_local_strong; et.
      - etrans.
        + instantiate (1:= Mod.add x (Mod.add_list [])). apply refines_strong_add.
          * apply adequacy_local_strong. apply H.
          * apply IHFORALL.
        + s. ii.
          pose proof ModFacts.add_comm as COMM. 
          pose proof ModFacts.add_assoc_rev as ASSOC'.
          apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR. et.
      - etrans.
        + apply adequacy_local_strong. apply H.
        + etrans.
          * instantiate (1:= Mod.add x (Mod.add_list [])). s. ii.
            pose proof ModFacts.add_comm as COMM. 
            pose proof ModFacts.add_assoc as ASSOC.
            apply COMM. apply COMM in PR. apply ASSOC. apply ModFacts.add_empty_rev_r. apply PR.
          * apply refines_strong_add; et. apply adequacy_local_strong.
            econs; et. ii. rr. apply ModSemPair.self_sim.
      - apply refines_strong_add; et. apply adequacy_local_strong. apply H.
    Qed.             
          

  Theorem adequacy_local2 md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines2 [md_tgt] [md_src])>>
  .
  Proof.
    eapply refines_strong_refines.
    eapply adequacy_local_list_strong. econs; ss.
  Qed.

  Corollary adequacy_local_list
            mds_src mds_tgt
            (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt)
    :
      <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>>
  .
  Proof.
    eapply refines_strong_refines.
    eapply adequacy_local_list_strong; et.
  Qed.

End ADEQUACY.