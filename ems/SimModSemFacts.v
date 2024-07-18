Require Import Coqlib.
Require Import ITreelib.
Require Import Skeleton.
Require Import ModSem.
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

Require Import SimGlobal.
Require Import Red IRed.
Require Import SimModSem.
Require Import ModSemFacts.
Import TAC.

Section ADEQUACY.
  (* Context {CONF: EMSConfig}. *)

  Lemma adequacy_modsem
          ms_src ms_tgt (P Q : Prop)
          (CONF: EMSConfig)
          (WF: Q -> P)
          (SIM: ModSemPair.sim ms_src ms_tgt)
    :
    <<REF: Beh.of_program (@ModSem.compile ms_tgt CONF (Some P)) <1= Beh.of_program (@ModSem.compile ms_src CONF (Some Q)) >>.
  Proof.
    red. inv SIM. eapply adequacy_local_aux with (wf:=wf) (le:=le); et.
    i. destruct (alist_find fn (ModSem.fnsems ms_src)) eqn:SRC; destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn:TGT; et; cycle 1.
    - eapply alist_find_some in SRC.
      eapply Forall2_In_l with (a:= (fn, i)) in sim_fnsems; et.
      inv sim_fnsems. des.
      destruct x. inv H0. unfold "@@1" in H1. ss. clarify.
      apply alist_find_none with (v:=i0) in TGT. clarify. 
    - right. esplits; et. clear -sim_fnsems SRC TGT.
      revert fn i i0 SRC TGT.
      induction sim_fnsems; i; ss.
      des_ifs_safe. inv H. unfold "@@1" in H0. ss. clarify.
      des_ifs. eapply IHsim_fnsems; et.
  Qed.

  Context `{Sk.ld}.

  Theorem adequacy_local_strong_l mds_src mds_tgt
          (SIM: forall sk, ModLPair.sim mds_src mds_tgt sk)
    :
      <<CR: (refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src))>>
  .
  Proof.
  (*   ii. unfold Mod.compile, Mod.enclose in *. *)
  (*   set (Mod.wf _) as wf_src. set (Mod.wf _) as wf_tgt in PR. *)
  (*   set (Mod.sk _) as sk_src. set (Mod.sk _) as sk_tgt in PR. *)
  (*   specialize (SIM (Sk.canon sk_tgt)). inv SIM. *)
  (*   destruct (classic wf_src); cycle 1. *)
  (*   { eapply ModSem.compile_not_wf; et. } *)
  (*   ss. rename H0 into SKWF. *)
  (*   assert (SKEQ: sk_src = sk_tgt). *)
  (*   { unfold sk_src, sk_tgt. ss. f_equal. clear -sim_sk. *)
  (*     ginduction mds_src; i. *)
  (*     - inv sim_sk. destruct mds_tgt; clarify. *)
  (*     - destruct mds_tgt; inv sim_sk. ss. destruct mds_src; ss. *)
  (*       + destruct mds_tgt; inv H5. et. *)
  (*       + destruct mds_tgt; inv H5. ss. f_equal; et. specialize (IHmds_src (t1 :: mds_tgt)). *)
  (*         ss. apply IHmds_src. econs; et. } *)
  (*   hexploit sim_modsem; et. *)
  (*   { clear. unfold sk_tgt. clear sk_tgt. *)
  (*     ss. set (Mod.sk ctx) as sk_ctx. *)
  (*     clearbody sk_ctx. clear ctx. *)
  (*     ginduction mds_tgt; i; ss. *)
  (*     econs; cycle 1. *)
  (*     { destruct mds_tgt; ss. specialize (IHmds_tgt (Sk.add (Mod.sk a) sk_ctx)). *)
  (*       eapply Forall_impl; [|et]. unfold flip. i. etrans; et. *)
  (*       etrans. apply Sk.le_canon_rev. etrans; [|apply Sk.le_canon]. *)
  (*       rewrite Sk.add_assoc. Print Sk.ld. apply IHmds_tgt. } *)
  (*     ss. etrans; [|apply Sk.le_canon]. etrans; [|apply Sk.le_add_l]. *)
  (*     apply Sk.le_add_r. } *)
  (*   { inv SKWF. rewrite <- SKEQ. apply Sk.wf_canon; et. } *)
  (*   intro SIM. *)
  (*   destruct wf_tgt; cycle 1. *)
  (*   { exfalso. apply n. unfold Mod.wf in *. ss. *)
  (*     fold sk_tgt. rewrite <- SKEQ. des. split; et. ss. *)
  (*     inv WF. econs; ss; unfold ModSem.add_fnsems in *; rewrite map_app in *. *)
  (*     i. set (List.map fst _) as ndom_src at 2. *)
  (*     set (List.map fst _) as ndom_tgt in wf_fnsems at 2. *)
  (*     replace ndom_src with ndom_tgt; et. *)
  (*     unfold ndom_src, ndom_tgt. fold sk_src. rewrite SKEQ. clear -SIM. clearbody sk_tgt. *)
  (*     rewrite !List.map_map. rewrite !ModSemFacts.fun_fst_trans_r. *)
  (*     revert mds_tgt SIM. induction mds_src; i.  *)
  (*     { inv SIM. destruct mds_tgt; clarify. } *)
  (*     destruct mds_tgt; inv SIM. ss. unfold ModSem.add_fnsems. rewrite !map_app. *)
  (*     rewrite !List.map_map.  *)
  (*     rewrite !ModSemFacts.fun_fst_trans_l. *)
  (*     rewrite !ModSemFacts.fun_fst_trans_r. f_equal; et. *)
  (*     inv H3. clear -sim_fnsems. *)
  (*     set (ModSem.fnsems _) as fl1. set (ModSem.fnsems _) as fl2.  *)
  (*     fold fl1 in sim_fnsems. fold fl2 in sim_fnsems. *)
  (*     clearbody fl1 fl2. revert fl2 sim_fnsems. *)
  (*     induction fl1; i; destruct fl2; inv sim_fnsems; ss. *)
  (*     f_equal; et. inv H3. destruct a0, p. ss. } *)
  (*   ss. rewrite SKEQ. *)
  (*   red in SIM. inv w. rename H0 into MSWFTGT. red in MSWFTGT. ss. fold sk_tgt in MSWFTGT.  *)
  (*   clearbody sk_tgt. clear -SIM PR MSWFTGT. *)
  (*   revert mds_tgt SIM ctx MSWFTGT x0 PR. *)
  (*   induction mds_src; i. *)
  (*   { destruct mds_tgt; inv SIM. ss. } *)
  (*   destruct mds_tgt; inv SIM. ss. *)
  (*   eapply ModSemFacts.add_assoc. { instantiate (1:= true). et. } *)
  (*   eapply ModSemFacts.add_assoc_rev in PR. 2:{ instantiate (1:= true). et. } *)
  (*   change (ModSem.add (Mod.get_modsem ctx (Sk.canon sk_tgt)) (Mod.get_modsem a (Sk.canon sk_tgt))) *)
  (*     with (Mod.get_modsem (Mod.add ctx a) (Sk.canon sk_tgt)). *)
  (*   eapply IHmds_src. { et. } *)
  (*   { clear -MSWFTGT H3. inv MSWFTGT. econs; ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. rewrite app_assoc in wf_fnsems. *)
  (*     rewrite !List.map_map in *. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l_l. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l_r. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l in wf_fnsems. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r_l in wf_fnsems. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r_r in wf_fnsems. *)
  (*     set (List.map _ (ModSem.fnsems (Mod.get_modsem a _))) as anamedom. *)
  (*     set (List.map _ (ModSem.fnsems (Mod.get_modsem t _))) as tnamedom in wf_fnsems. *)
  (*     replace anamedom with tnamedom; et. *)
  (*     unfold tnamedom, anamedom. inv H3. clear -sim_fnsems. *)
  (*     induction sim_fnsems; auto. *)
  (*     ss. f_equal; ss. inv H0. destruct x, y. ss. } *)
  (*   ss.  *)
  (*   eapply ModSemFacts.add_comm. { instantiate (1:= true). et. } *)
  (*   { clear -MSWFTGT H3. inv MSWFTGT. econs; ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. rewrite app_assoc in wf_fnsems. *)
  (*     rewrite !List.map_map in *. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l_l. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l_r. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r. *)
  (*     rewrite ModSemFacts.fun_fst_trans_l in wf_fnsems. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r_l in wf_fnsems. *)
  (*     rewrite ModSemFacts.fun_fst_trans_r_r in wf_fnsems. *)
  (*     set (List.map _ (ModSem.fnsems (Mod.get_modsem a _))) as anamedom. *)
  (*     set (List.map _ (ModSem.fnsems (Mod.get_modsem t _))) as tnamedom in wf_fnsems. *)
  (*     replace anamedom with tnamedom; et. *)
  (*     unfold tnamedom, anamedom. inv H3. clear -sim_fnsems. *)
  (*     induction sim_fnsems; auto. *)
  (*     ss. f_equal; ss. inv H0. destruct x, y. ss. } *)
  (*   eapply ModSemFacts.add_comm in PR; cycle 1. { instantiate (1:= true). et. } *)
  (*   { clear -MSWFTGT H3. inv MSWFTGT. econs; ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. ss. *)
  (*     unfold ModSem.add_fnsems in *; rewrite ! map_app in *. rewrite app_assoc in wf_fnsems. *)
  (*     rewrite !List.map_map in *. *)
  (*     rewrite !ModSemFacts.fun_fst_trans_l in *. *)
  (*     rewrite !ModSemFacts.fun_fst_trans_r_l in *. *)
  (*     rewrite !ModSemFacts.fun_fst_trans_r_r in *. *)
  (*     apply nodup_comm. et. } *)
  (*   eapply ModSemFacts.add_assoc. { instantiate (1:= true). et. } *)
  (*   eapply ModSemFacts.add_assoc_rev in PR. 2:{ instantiate (1:= true). et. } *)
  (*   eapply adequacy_modsem; cycle 1; et. apply sim_ctx. et. *)
  (* Qed. *)
  Admitted.

  Corollary adequacy_local_strong md_src md_tgt
      (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines_strong md_tgt md_src)>>
  .
  Proof.
    red. red. red. i.
    replace md_src with (Mod.add_list [md_src]) by et.
    replace md_tgt with (Mod.add_list [md_tgt]) in PR by et.
    eapply adequacy_local_strong_l; et. i. inv SIM. econs; ss; et.
    i. econs; et. eapply sim_modsem; et. inv SKINCL. ss.
  Qed.

  (* Lemma sim_ctx_mod *)
  (*   ctx md1 md2 *)
  (*   (SIM: ModPair.sim md1 md2) *)

  (* : *)
  (*   ModPair.sim (Mod.add md1 ctx) (Mod.add md2 ctx) *)
  (* . *)
  (* Proof. *)
  (*   inv SIM. *)
  (*   econs; et. *)
  (*   (* - i. ss. hexploit (sim_modsem sk); et. *) *)
  (*   - i. ss. hexploit (sim_modsem sk); et. *)

  (*     2: { ii. des. apply sim_ctx; et. } *)
  (*     unfold Sk.incl, Sk.add in *. i. ss. *)
  (*     apply SKINCL. *)
  (*     rewrite in_app_iff. et. *)
  (*   - r. ss. unfold Sk.add. ss. *)
  (*     rewrite sim_sk. et. *)
  (* Qed. *)

  (* Lemma adequacy_mod *)
  (*         md_src md_tgt *)
  (*         (CONF: EMSConfig) *)
  (*         (SIM: ModPair.sim md_src md_tgt) *)
  (*   : *)
  (*   <<REF: Beh.of_program (Mod.compile md_tgt) <1= Beh.of_program (Mod.compile md_src) >> *)
  (*   . *)
  (* Proof. *)
  (*   ii. unfold Mod.compile in *. *)
  (*   destruct (classic (ModSem.wf (Mod.enclose (md_src)) /\ Sk.wf (Mod.sk md_src))). *)
  (*   2: { eapply ModSem.initial_itr_not_wf. ss. } *)
  (*   ss. des.  *)
  (*   pose (sk_tgt := (Mod.sk (md_tgt))). *)
  (*   pose (sk_src := (Mod.sk (md_src))). *)
  (*   assert (SKEQ: sk_src = sk_tgt). *)
  (*   { unfold sk_tgt, sk_src. inv SIM. et. } *)
  (*   unfold Mod.enclose in *. fold sk_src in H. inv H. *)
  (*   inv SIM. hexploit (sim_modsem (Sk.canon sk_tgt)). *)
  (*   { etrans; [|eapply Sk.sort_incl]. ss. } *)
  (*   { ss. rewrite sim_sk in H0. *)
  (*     clear - H0. *)
  (*     unfold Sk.wf in *. ss. *)
  (*     eapply Permutation.Permutation_NoDup; [|et]. *)
  (*     eapply Permutation.Permutation_map. *)
  (*     eapply Sk.SkSort.sort_permutation. } *)
  (*   i. des. *)
  (*   inv H. ss. *)

  (*   assert (WFTGT: Mod.wf md_tgt). *)
  (*   { rr. unfold Mod.enclose. ss. fold sk_tgt.  *)
  (*     rewrite SKEQ in *. split; auto. *)
  (*     2: { rewrite <-SKEQ. unfold sk_src. et. } *)
  (*     econs. *)
  (*     match goal with *)
  (*       | H: NoDup ?l0 |- NoDup ?l1 => replace l1 with l0 *)
  (*     end; auto. *)
  (*     eapply Forall2_eq. eapply Forall2_apply_Forall2; et. *)
  (*     i. destruct a, b. inv H. ss. *)
  (*   } *)

  (*   eapply adequacy_local_aux in PR; et. *)
  (*   - i. esplits. *)
  (*     pose (ms_src := Mod.get_modsem md_src (Sk.sort (Mod.sk md_src))). *)
  (*     pose (ms_tgt := Mod.get_modsem md_tgt (Sk.sort (Mod.sk md_tgt))). *)
  (*     fold ms_src ms_tgt. *)
  (*     rewrite <- SKEQ in sim_fnsems at 1. *)
  (*     unfold sk_src, sk_tgt in sim_fnsems. *)
  (*     fold ms_src ms_tgt in sim_fnsems. *)
  (*     hexploit sim_fnsems. i. *)

  (*     destruct (alist_find fn (ModSem.fnsems ms_src)) eqn:SRC; destruct (alist_find fn (ModSem.fnsems ms_tgt)) eqn:TGT; et. *)
  (*     2: { *)
  (*       right. *)
  (*       eapply alist_find_some in SRC. *)
  (*       rewrite <- sim_sk in sim_fnsems. *)
  (*       (* eapply alist_find_none in TGT. *) *)
  (*       eapply Forall2_In_l with (a:= (fn, i)) in sim_fnsems; et. *)
  (*       inv sim_fnsems. inv H1. *)
  (*       inv H3. inv H1. *)
  (*       destruct x. ss. clarify. *)
  (*       apply alist_find_none with (v:=i0) in TGT. clarify.  *)
  (*     } *)
  (*     right. esplits; et. *)

  (*     hexploit SRC. hexploit TGT. i. *)
  (*     apply alist_find_some in H1, H2. *)

  (*     rewrite <- sim_sk in sim_fnsems. *)

  (*     eapply Forall2_In_l with (a:=(fn, i)) in sim_fnsems; et. *)
  (*     eapply Forall2_In_r with (b:=(fn, i0)) in H; et. *)
  (*     inv sim_fnsems. inv H. *)
  (*     destruct x, x1. *)
  (*     inv H3. inv H5. inv H3. ss. *)
  (*     inv H4. inv H7. inv H4. ss. clarify. *)
  (*     unfold "@@2" in H5, H6. ss. *)
  (*     (* apply NoDup_map_inv in wf_fnsems. *) *)
  (*     unfold sk_src in wf_fnsems. *)
  (*     fold ms_src in wf_fnsems. *)
  (*     rewrite <- sim_sk in H3. *)
  (*     eapply alist_find_some_iff  with (k:=s) (v:=i2) in wf_fnsems; et. *)
  (*     rewrite SRC in wf_fnsems. clarify. apply H5. *)
  (*   (* - inv sim_initial. econs. econs. *)
  (*     2: { fold sk_src sk_tgt. rewrite SKEQ. apply H. } *)
  (*     instantiate (1:= x). refl. *) *)

  (*   Qed. *)


  (* Theorem adequacy_local_strong md_src md_tgt *)
  (*         (SIM: ModPair.sim md_src md_tgt) *)
  (*   : *)
  (*   <<CR: (refines_strong md_tgt md_src)>> *)
  (* . *)
  (* Proof. *)

  (*   ii. *)
  (*   apply sim_ctx_mod with (ctx:=ctx) in SIM. *)

  (*   pose (Mod.add md_src ctx) as mds. *)
  (*   pose (Mod.add md_tgt ctx) as mdt. *)
  (*   fold mds. fold mdt in PR. *)
  (*   apply adequacy_mod with (md_src := mds) in PR; et. *)
  (* Qed. *)

  Context {CONF: EMSConfig}.

  Corollary adequacy_local md_src md_tgt
          (SIM: ModPair.sim md_src md_tgt)
    :
      <<CR: (refines md_tgt md_src)>>
  .
  Proof.
    eapply refines_strong_refines.
    eapply adequacy_local_strong; et.
  Qed.

  (* Corollary adequacy_local_list_strong *)
  (*           mds_src mds_tgt *)
  (*           (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt) *)
  (*   : *)
  (*     <<CR: refines_strong (Mod.add_list mds_tgt) (Mod.add_list mds_src)>> *)
  (* . *)
  (* Proof. *)
  (*   (* apply adequacy_local_strong. *) *)

  (* (* Admitted. *) *)


  (*   r. induction FORALL; ss. *)
  (*   { ii. auto. } *)

  (*     destruct l eqn: L, l' eqn: L'. *)
  (*     - apply adequacy_local_strong; et. *)
  (*     - etrans. *)
  (*       + instantiate (1:= Mod.add x (Mod.add_list [])). apply refines_strong_add. *)
  (*         * apply adequacy_local_strong. apply H. *)
  (*         * apply IHFORALL. *)
  (*       + s. ii. *)
  (*         pose proof ModFacts.add_comm as COMM.  *)
  (*         pose proof ModFacts.add_assoc_rev as ASSOC'. *)
  (*         apply COMM. apply COMM in PR. apply ASSOC' in PR. apply ModFacts.add_empty_r in PR. et. *)
  (*     - etrans. *)
  (*       + apply adequacy_local_strong. apply H. *)
  (*       + etrans. *)
  (*         * instantiate (1:= Mod.add x (Mod.add_list [])). s. ii. *)
  (*           pose proof ModFacts.add_comm as COMM.  *)
  (*           pose proof ModFacts.add_assoc as ASSOC. *)
  (*           apply COMM. apply COMM in PR. apply ASSOC. apply ModFacts.add_empty_rev_r. apply PR. *)
  (*         * apply refines_strong_add; et. apply adequacy_local_strong. *)
  (*           econs; et. ii. rr. apply ModSemPair.self_sim. *)
  (*     - apply refines_strong_add; et. apply adequacy_local_strong. apply H. *)
  (*   Qed.              *)
          

  (* Theorem adequacy_local2 md_src md_tgt *)
  (*         (SIM: ModPair.sim md_src md_tgt) *)
  (*   : *)
  (*     <<CR: (refines2 [md_tgt] [md_src])>> *)
  (* . *)
  (* Proof. *)
  (*   eapply refines_strong_refines. *)
  (*   eapply adequacy_local_list_strong. econs; ss. *)
  (* Qed. *)

  (* Corollary adequacy_local_list *)
  (*           mds_src mds_tgt *)
  (*           (FORALL: List.Forall2 ModPair.sim mds_src mds_tgt) *)
  (*   : *)
  (*     <<CR: refines (Mod.add_list mds_tgt) (Mod.add_list mds_src)>> *)
  (* . *)
  (* Proof. *)
  (*   eapply refines_strong_refines. *)
  (*   eapply adequacy_local_list_strong; et. *)
  (* Qed. *)

End ADEQUACY.
