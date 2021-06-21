From compcert Require Import Globalenvs Smallstep AST Integers Events Behaviors Errors Memory Csharpminor Linking.
Require Import Coqlib.
Require Import ITreelib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import STS Behavior.
Require Import Any.
Require Import ModSem.
Require Import Imp.
Require Import Imp2Csharpminor.
Require Import ImpProofs.
Require Import SimSTS2.
Require Import Mem0.
Require Import IRed.
From Ordinal Require Import Ordinal Arithmetic.

Require Import Imp2CsharpminorMatch.
Require Import Imp2CsharpminorArith.
Require Import Imp2CsharpminorGenv.
Require Import Imp2CsharpminorMem.
Require Import Imp2CsharpminorLink.
Require Import Imp2CsharpminorSim.

Set Implicit Arguments.

Section PROOFSINGLE.

  Context `{Σ: GRA.t}.

  Create HintDb ord_step2.
  Hint Resolve Nat.lt_succ_diag_r OrdArith.lt_from_nat OrdArith.lt_add_r: ord_step2.
  Hint Extern 1000 => lia: ord_step2.
  Ltac ord_step2 := eauto with ord_step2.

  (* Import ModSemL. *)

  (* Let _sim_mon := Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @sim_mon (ModL.compile src) (semantics tgt)). *)
  (* Hint Resolve _sim_mon: paco. *)

  (* Let _ordC_spec := *)
  (*   Eval simpl in (fun (src: ModL.t) (tgt: Csharpminor.program) => @ordC_spec (ModL.compile src) (Csharpminor.semantics tgt)). *)

  Ltac sim_red := try red; Red.prw ltac:(_red_gen) 2 0.
  Ltac sim_tau := (try sim_red); econs 3; ss; clarify; eexists; exists (ModSemL.step_tau _); eexists; split; [ord_step2|auto].
  (* Ltac sim_ord := guclo _ordC_spec; econs. *)

  Ltac sim_triggerUB := unfold triggerUB; (try sim_red); econs 5; i; ss; auto;
                        dependent destruction STEP; try (irw in x; clarify; fail).

  Definition imp_initial_state (src : Imp.programL) :=
    (ModL.compile (ModL.add (Mod.lift Mem) (ImpMod.get_modL src))).(initial_state).

  Lemma single_compile_behavior_improves
        (src: Imp.programL) (tgt: Csharpminor.program) srcst tgtst
        (WFPROG: Permutation.Permutation
                   ((List.map fst src.(prog_varsL)) ++ (List.map (compose fst snd) src.(prog_funsL)))
                   (List.map fst src.(defsL)))
        (WFPROG2 : forall gn gv, In (gn, Sk.Gvar gv) (Sk.sort (defsL src)) -> In (gn, gv) (prog_varsL src))
        (COMP: Imp2Csharpminor.compile src = OK tgt)
        (SINIT: srcst = imp_initial_state src)
        (TINIT: Csharpminor.initial_state tgt tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgt) srcst tgtst>>.
  Proof.
    eapply adequacy; eauto.
    { apply Ordinal.Ord.lt_well_founded. }
    { apply Csharpminor_wf_semantics. }
    { admit "ez? wf imp". }
    instantiate (1:= ((100 + max_fuel) + 120)%ord). red. unfold imp_initial_state in *. ss; clarify. inv TINIT.
    rename m0 into tm, ge into tge, H into TMINIT, H0 into TMAIN1, H1 into TMAIN2, H2 into TSIGMAIN, b into tb, f into tmain.
    assert (COMP0: Imp2Csharpminor.compile src = OK tgt); auto. move COMP0 before tgt.
    unfold compile in COMP. des_ifs. rename g into gm, Heq into GMAP.
    unfold _compile in COMP. des_ifs. rename Heq into COMPGDEFS, l0 into NOREPET. ss; clarify.
    match goal with | [ COMP0 : compile _ = OK ?_tgt |- _ ] => set (tgt:=_tgt) in * end.
    unfold ModSemL.initial_itr. unfold ModSemL.initial_itr_arg.
    pfold. econs 5; eauto. unfold assume. ss. grind. eapply angelic_step in STEP. des; clarify. eexists; split; [ord_step2|auto].
    left. unfold ITree.map. sim_red. set (sge:=Sk.load_skenv (Sk.sort (defsL src))) in *.
    destruct (alist_find "main" (List.map (fun '(mn, (fn, f)) => (fn, transl_all mn ∘ cfun (eval_imp sge f))) (prog_funsL src)))
             eqn:FOUNDMAIN; ss; grind.
    2:{ pfold. sim_triggerUB. }
    rewrite alist_find_find_some in FOUNDMAIN. rewrite find_map in FOUNDMAIN. uo; des_ifs; ss.
    rename s into mn, f into smain, Heq into SFOUND. apply find_some in SFOUND. des. ss. clear SFOUND0.
    assert (COMPGDEFS0 : compile_gdefs gm src = Some l); auto.
    unfold compile_gdefs in COMPGDEFS. uo; des_ifs. ss. rename l0 into cfs.
    match goal with | [ H: Coqlib.list_norepet (List.map fst ?_l) |- _ ] => set (tgds:=_l) in * end.
    hexploit exists_compiled_function; eauto. i; des. rename H into PCMAIN, H0 into INPMAIN, H1 into CFMAIN, H2 into INFMAIN.
    hexploit in_tgt_prog_defs_ifuns; eauto. i. rename H into INFMAINTGT.
    hexploit tgt_genv_find_def_by_blk; eauto. i. rename H into TGTMAIN. ss; clarify. uo; des_ifs; ss; clarify.
    2:{ rewrite eq_rel_dec_correct in Heq; des_ifs. }
    match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
    unfold Genv.find_funct_ptr in TMAIN2. des_ifs. rename Heq2 into TMAIN2.
    hexploit tgt_genv_match_symb_def.
    1,2,4: eauto.
    1: eapply TMAIN2.
    i; clarify. clear Heq. unfold pre_compile_function in PCMAIN. des_ifs; ss. clear INPMAIN.
    rename Heq1 into CMAINstmt, l into WF_MAIN, s into mstmt.
    unfold cfun. rewrite Any.upcast_downcast. grind. rewrite unfold_eval_imp_only. des_ifs; grind; sim_red.
    2:{ pfold. sim_triggerUB. }
    assert (MAINPARAM: fn_params smain = []).
    { depgen Heq. clear. i. remember (fn_params smain) as m. clear Heqm. depgen l. induction m; i; ss; clarify. }
    clear Heq. rewrite interp_imp_tau. sim_red.

    pfold. econs 4; ss. eexists. eexists.
    { apply Coqlib.list_norepet_app in WF_MAIN; des. subst tmainf.
      eapply step_internal_function; ss; eauto; try econs;
        match goal with [H: Genv.find_def _ _ = Some (Gfun (Internal ?tf)) |- _ ] => set (tmainf:=tf) in * end.
      rewrite MAINPARAM. ss. }
    eexists; split; [ord_step2|auto]. left. ss.

    pfold. econs 6; ss; eauto. eexists. eexists.
    { eapply step_seq. }
    eexists. exists (ModSemL.step_tau _). exists ((100 + max_fuel) + 100)%ord. left.
    rewrite interp_imp_bind. grind. sim_red. rename l into sle.
    assert (MATCHGE: match_ge src (Sk.sort (ModL.sk (ModL.add Mem (ImpMod.get_modL src)))) (Genv.globalenv tgt)).
    { econs. i. unfold map_blk. rewrite COMP0. hexploit Sk.env_found_range; eauto. i. unfold src_init_nb, int_len.
      rewrite <- sksort_same_len in H0. ss. des_ifs; unfold NW in *; try lia.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify.
        hexploit found_in_src_in_tgt; eauto. i. des. rewrite Heq1 in H2. clarify.
      - unfold get_sge in *. ss. apply Sk.sort_wf in SK.
        hexploit Sk.load_skenv_wf; eauto. i. apply H1 in H. rewrite H in Heq. clarify. }

    eapply match_states_sim; eauto.
    { apply map_blk_after_init. }
    { apply map_blk_inj. }
    match goal with
    | [ |- match_states _ ?_ge ?_ms _ _ _ ] => replace _ge with sge; auto; set (ms:=_ms) in *
    end.
    econs; eauto.
    { ss. }
    { admit "ez?: match initial le". }
    { clarify. }
    { econs; ss.
      { unfold src_init_nb, int_len. rewrite <- sksort_same_len. lia. }
      { apply Genv.init_mem_genv_next in TMINIT. rewrite <- TMINIT. unfold Genv.globalenv. ss.
        rewrite Genv.genv_next_add_globals. ss. rewrite Genv_advance_next_length. ss.
        rewrite length_elements_PTree_norepet; eauto. rewrite map_blk_after_init; eauto.
        2:{ unfold src_init_nb, int_len. rewrite <- sksort_same_len. lia. }
        unfold ext_len. subst tgds. repeat rewrite app_length. ss.
        rewrite <- sksort_same_len. rewrite wfprog_defsL_length; eauto.
        rewrite app_length. repeat rewrite map_length. apply get_iFuns_length in Heq0. rewrite <- Heq0.
        apply gmap_preserves_length in GMAP. des. rewrite EVL; rewrite EFL; rewrite IVL; rewrite IFL. lia. }
      i. uo; des_ifs. unfold NW in H. clarify. rename s into gn, Heq1 into SGENV.
      set (tblk:=map_blk src blk) in *. unfold map_ofs in *. rewrite! Z.mul_0_r.
      hexploit found_gvar_in_src_then_tgt; eauto. i. des. rename H into FOUNDTGV.
      hexploit Genv.init_mem_characterization; eauto.
      { unfold Genv.find_var_info. rewrite FOUNDTGV. clarify. }
      i. des. rename H into TMPERM, H0 into TMPERM0, H1 into TMLSID, H2 into TMLB.
      subst tblk. inv MATCHGE.
      assert (SKFOUND: SkEnv.blk2id sge blk = Some gn).
      { subst sge. Local Transparent Sk.load_skenv. unfold Sk.load_skenv. ss. rewrite SGENV. uo; ss. Local Opaque Sk.load_skenv. }
      assert (WFSKENV: Sk.wf (defsL src)); auto.
      apply Sk.sort_wf in WFSKENV. apply Sk.load_skenv_wf in WFSKENV. apply WFSKENV in SKFOUND. clear WFSKENV.
      apply MG in SKFOUND. apply nth_error_In in SGENV. apply WFPROG2 in SGENV.
      hexploit compiled_gvar_props; eauto. i. des. clarify.
      assert (TMLSID0: false = false); auto. apply TMLSID in TMLSID0; clear TMLSID.
      assert (TMLB0: false = false); auto. apply TMLB in TMLB0; clear TMLB.
      rewrite H0 in *. ss. des. clear TMLSID1. split; auto.
      unfold Genv.perm_globvar in TMPERM. des_ifs. split.
      2:{ unfold NW. lia. }
      split; eauto. ss. apply Z.divide_0_r. }
    { ss. }
    { ss.
      match goal with
      | [ |- match_code _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((fun '(r, p, (le, _)) => itree_of_imp_ret sge le ms mn (r, p)) : (_ * _ * (lenv * val)) -> _);
          replace s0 with [exit_stmt]; eauto
      end.
      { econs 1. }
      extensionality x. unfold itree_of_imp_ret, itree_of_imp_cont. grind. destruct p0. rewrite interp_imp_expr_Var. grind. }
    { ss.
      match goal with
      | [ |- match_stack _ _ _ _ _ _ ?i0 ?s0 ] =>
        replace i0 with ((itree_of_imp_pop_bottom ms mn) : (_ * _ * (lenv * val)) -> _);
          replace s0 with (Some ret_call_main); eauto
      end.
      { econs 1. ss. } }
  Qed.

End PROOFSINGLE.





Section PROOFLEFT.

  Context `{Σ: GRA.t}.

  (* Proving the left arrow of the diagram *)
  Lemma _comm_link_imp_link_mod
        src1 src2 srcl tgt1 tgt2 tgtl (ctx : ModL.t)
        (MOD1: ImpMod.get_modL src1 = tgt1)
        (MOD2: ImpMod.get_modL src2 = tgt2)
        (LINKIMP: link_imp src1 src2 = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: ModL.add ctx (ModL.add tgt1 tgt2) = ModL.add ctx tgtl>>.
  Proof.
    unfold link_imp in LINKIMP. des_ifs; ss. unfold ImpMod.get_modL; ss. unfold ModL.add. ss. red. f_equal.
    extensionality sk. unfold ModSemL.add; ss. f_equal.
    - f_equal. rewrite <- map_app. ss.
    - f_equal. rewrite <- map_app. ss.
  Qed.

  Lemma comm_link_imp_link_mod
        src_list srcl tgt_list tgtl ctx
        (MODLIST: List.map ImpMod.get_modL src_list = tgt_list)
        (LINKIMP: link_imp_list src_list = Some srcl)
        (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: fold_right ModL.add ModL.empty (ctx :: tgt_list) = ModL.add ctx tgtl>>.
  Proof.
    destruct src_list as [ | src0 src_liat ]; ss; clarify. des_ifs; ss; clarify.
    { rewrite ModL.add_empty_r. ss. }
    rename p into src1, p0 into srct, l into src_list, Heq into LINK. move src_list before Σ.
    revert_until Σ. induction src_list; i; ss; clarify.
    { rewrite ModL.add_empty_r. eapply _comm_link_imp_link_mod; eauto. }
    red. des_ifs; ss; clarify.
    { rewrite ModL.add_empty_r. eapply _comm_link_imp_link_mod; eauto.
      specialize IHsrc_list with (ctx:=ModL.empty). rewrite <- ModL.add_empty_l. sym; rewrite <- ModL.add_empty_l.
      replace (ImpMod.get_modL p) with (ModL.add (ImpMod.get_modL p) ModL.empty).
      2:{ apply ModL.add_empty_r. }
      eapply IHsrc_list; eauto. }
    hexploit _comm_link_imp_link_mod.
    5:{ i. eapply H. }
    4:{ clarify. }
    3:{ eapply LINKIMP. }
    all: eauto.
    specialize IHsrc_list with (ctx:=ModL.empty). rewrite <- ModL.add_empty_l. sym; rewrite <- ModL.add_empty_l.
    eapply IHsrc_list; eauto.
  Qed.

  Theorem left_arrow
          (src_list: list Imp.program) srcl (tgt_list: list Mod.t) tgtl (ctx: Mod.t)
          (MODLIST: List.map ImpMod.get_mod src_list = tgt_list)
          (LINKIMP: link_imps src_list = Some srcl)
          (MODL: ImpMod.get_modL srcl = tgtl)
    :
      <<LINKMOD: Mod.add_list (ctx :: tgt_list) = ModL.add (Mod.lift ctx) tgtl>>.
  Proof.
    red. unfold Mod.add_list. ss. eapply comm_link_imp_link_mod; eauto. rewrite List.map_map.
    pose ImpMod.comm_imp_mod_lift. unfold compose in e. rewrite e; clear e. rewrite <- List.map_map.
    rewrite MODLIST. ss.
  Qed.

End PROOFLEFT.





Section PROOFRIGHT.

  Import Maps.
  Import Permutation.

  Context `{Σ: GRA.t}.

  (* Proving the right arrow of the diagram *)

  Lemma pre_comp_link_two
        src1 src2 pcs1 pcs2
        (PCS1: pre_compile_iFuns (List.map snd (prog_funsL src1)) = Some pcs1)
        (PCS2: pre_compile_iFuns (List.map snd (prog_funsL src2)) = Some pcs2)
    :
      <<PCS12: pre_compile_iFuns (List.map snd (l_prog_funsLM src1 src2)) = Some (pcs1 ++ pcs2)>>.
  Proof.
    unfold l_prog_funsLM. rewrite map_app. red.
    match goal with
    | [ |- pre_compile_iFuns (?_fs1 ++ ?_fs2) = _ ] => set (fs1:=_fs1) in *; set (fs2:=_fs2) in *
    end.
    unfold pre_compile_iFuns in *. des_ifs; ss; clarify.
    { repeat f_equal. rewrite map_app. rewrite map_app. ss. }
    exfalso. apply n. clear n. rewrite map_app. apply Forall_app; eauto.
  Qed.

  Lemma link_then_some_gmap
        src1 pcs1 gm1 src2 pcs2 gm2 srcl
        (PCS1: pre_compile_iFuns (List.map snd (prog_funsL src1)) = Some pcs1)
        (GMAP1 : get_gmap src1 = Some gm1)
        (PCS2: pre_compile_iFuns (List.map snd (prog_funsL src2)) = Some pcs2)
        (GMAP2 : get_gmap src2 = Some gm2)
        (LINK : link_imp src1 src2 = Some srcl)
    :
      <<GMAPL: get_gmap srcl =
               Some (mk_gmap (compile_eVars (l_ext_vars src1 src2))
                             (compile_eFuns (l_ext_funs src1 src2))
                             (compile_iVars (l_prog_varsL src1 src2))
                             (pcs1 ++ pcs2))>>.
  Proof.
    unfold link_imp in LINK. des_ifs. unfold get_gmap; ss. erewrite pre_comp_link_two; eauto.
    uo; ss. unfold get_gmap in *. des_ifs; ss. uo; des_ifs; ss; clarify. exfalso. apply n; clear n.
    rename l into NOREPET1, l0 into NOREPET2, Heq2 into PCS1, Heq1 into PCS2.
    bsimpl; des. rename Heq into LC1, Heq1 into LC2, Heq0 into LC3. unfold link_imp_cond2 in LC2. bsimpl; des.
    repeat match goal with | [ H: _ = true |- _ ] => apply sumbool_to_bool_true in H end.
  Admitted.

  Lemma ext_vars_names :
    forall src, <<EVN: List.map fst (compile_eVars (ext_varsL src)) = List.map s2p (ext_varsL src)>>.
  Proof.
    i. unfold compile_eVars. rewrite List.map_map. apply List.map_ext. i. ss.
  Qed.

  Lemma ext_funs_names :
    forall src, <<EFN: List.map fst (compile_eFuns (ext_funsL src)) = List.map (compose s2p fst) (ext_funsL src)>>.
  Proof.
    i. unfold compile_eFuns. rewrite List.map_map. apply List.map_ext. i. destruct a. ss.
  Qed.

  Lemma int_vars_names :
    forall src, <<IVN: List.map fst (compile_iVars (prog_varsL src)) = List.map (compose s2p fst) (prog_varsL src)>>.
  Proof.
    i. unfold compile_iVars. rewrite List.map_map. apply List.map_ext. i. destruct a; ss.
  Qed.

  Lemma int_funs_names :
    forall src pcs
      (PCS : pre_compile_iFuns (List.map snd (prog_funsL src)) = Some pcs),
      <<IFN: List.map fst pcs = List.map (compose s2p (compose fst snd)) (prog_funsL src)>>.
  Proof.
    i. unfold pre_compile_iFuns in PCS. des_ifs. rewrite List.map_map in f. do 3 rewrite List.map_map. red.
    apply map_ext_strong. i. apply List.Forall_map in f. rewrite Forall_forall in f. apply f in IN.
    des_ifs. ss. destruct x. ss. destruct p. clarify.
  Qed.








  (* Maps.PTree.elements_extensional 
     we will rely on above theorem for commutation lemmas *)
  Variable P: Imp2Csharpminor.gmap -> Imp2Csharpminor.gmap -> Imp2Csharpminor.gmap -> Prop.
  Variable Q: list (ident * globdef fundef ()) -> list (ident * globdef fundef ()) -> list (ident * globdef fundef ()) -> Prop.
  Lemma _comm_link_imp_compile
        src1 src2 srcl tgt1 tgt2 tgtl
        (COMP1: compile src1 = OK tgt1)
        (COMP2: compile src2 = OK tgt2)
        (LINKSRC: link_imp src1 src2 = Some srcl)
        (LINKTGT: link_prog tgt1 tgt2 = Some tgtl)
    :
      <<COMPL: compile srcl = OK tgtl>>.
  Proof.
    unfold compile, _compile in *. des_ifs_safe.
    rename l1 into pa. rename l into pb.
    rename g0 into ga. rename g into gb.
    assert(exists gml, get_gmap srcl = Some gml /\ <<PROP: P ga gb gml>>).
    { admit "". }
    des. des_ifs_safe.
    assert(exists pl, compile_gdefs gml srcl = Some pl /\ Q pa pb pl).
    { unfold compile_gdefs in *. uo. des_ifs_safe.
      admit "somehow". }
    des. des_ifs_safe.
    assert(forall k, get k (combine link_prog_merge (Maps.PTree_Properties.of_list pa)
                                    (Maps.PTree_Properties.of_list pb)) =
                     get k (Maps.PTree_Properties.of_list pl)).
    { i. erewrite gcombine; ss.
      erewrite ! Maps.PTree_Properties.of_list_norepet; ss; et. admit "". }
  Admitted.










  Fixpoint compile_imps (src_list : list Imp.programL) :=
    match src_list with
    | [] => Some []
    | src :: srcs =>
      match compile src with
      | OK tgt =>
        match compile_imps srcs with
        | Some tgts => Some (tgt :: tgts)
        | _ => None
        end
      | _ => None
      end
    end.

  (* Inductive compile_list : *)
  (*   list programL -> list (Csharpminor.program) -> Prop := *)
  (* | compile_nil : *)
  (*     compile_list [] [] *)
  (* | compile_head *)
  (*     src_h src_t tgt_h tgt_t *)
  (*     (COMPH: compile src_h = OK tgt_h) *)
  (*     (COMPT: compile_list src_t tgt_t) *)
  (*   : *)
  (*     <<COMPLIST: compile_list (src_h :: src_t) (tgt_h :: tgt_t)>>. *)
  Definition link_csm_list (tgt_list : list (Csharpminor.program)) :=
    match tgt_list with
    | [] => None
    | tgt_h :: tgt_t =>
      fold_left_option link_prog tgt_t (Some tgt_h)
    end.

  Lemma comm_link_imp_compile
        src_list srcl tgt_list tgtl
        (COMPL: compile_list src_list tgt_list)
        (LINKSRC: link_imp_list src_list = Some srcl)
        (LINKTGT: link_csm_list tgt_list = Some tgtl)
    :
      compile srcl = OK tgtl.
  Proof.
    i. destruct src_list; destruct tgt_list; ss; clarify.
    inv COMPL; clarify.
    generalize dependent srcl. generalize dependent tgtl.
    generalize dependent p. generalize dependent p0.
    induction COMPT; i; ss; clarify.
    destruct (link_prog p0 tgt_h) eqn:LPt; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKTGT; clarify. }
    destruct (link_imp p src_h) eqn:LPs; ss; clarify.
    2:{ rewrite fold_left_option_None in LINKSRC; clarify. }
    eapply IHCOMPT.
    2: apply LINKTGT.
    2: apply LINKSRC.
    eapply _comm_link_imp_compile.
    3: apply LPs.
    3: apply LPt.
    auto. auto.
  Qed.

End PROOFRIGHT.




Section PROOFLINK.

  (* Definition src_initial_state (src : ModL.t) := *)
  (*   (ModL.compile src).(initial_state). *)

  Theorem compile_behavior_improves
          (src_list : list Imp.program) srcl tgt_list tgtl srcst tgtst
          (COMP: let src_list_lift := List.map Imp.lift src_list in
                 compile_list src_list_lift tgt_list)
          (LINKSRC: let src_list_mod := List.map ImpMod.get_mod src_list in
                    Mod.add_list (Mem :: src_list_mod) = srcl)
          (LINKTGT: link_csm_list tgt_list = Some tgtl)
          (SINIT: srcst = src_initial_state srcl)
          (TINIT: Csharpminor.initial_state tgtl tgtst)
    :
      <<IMPROVES: @improves2 _ (Csharpminor.semantics tgtl) srcst tgtst>>.
  Proof.
  Admitted.

End PROOFLINK.
