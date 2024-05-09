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

Require Import HTactics.

Require Import SimStrict HPSim.

 (****************************************)

Section HPSIM. 
  Context `{Σ: GRA.t}.

  Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
  Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
  Variable I: Any.t -> Any.t -> iProp.


  Definition hp_reconf_eq cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      <<RELr: Own fr ⊢ #=> Own (fr' ⋅ cr)>> /\      
      <<STR: str' = str>>.
  
  Definition hp_reconf_equiv cr : relation (Any.t * Σ) :=
    fun '(str,fr) '(str',fr') =>
      hp_reconf_eq cr (str,fr) (str',fr')
      \/
      (exists st (mr mr': Σ),
       <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
       <<STR: str = Any.pair st mr↑>> /\
       <<STR': str' = Any.pair st mr'↑>>).

  Definition hp_reconf_rel R (eqv: Σ -> _) cr : relation (Any.t * (Σ * R)) :=
    fun '(str,(fr,x)) '(str',(fr',x')) =>
      eqv cr (str,fr) (str',fr') /\ x = x'.

  Lemma hp_reconf_equiv_strong
    cr str str' (fr fr': Σ)
    (EQV: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    (hp_reconf_eq cr (str,fr) (str',fr') /\
     <<FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑>>)
    \/
    (exists st (mr mr': Σ),
     <<RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr' ⋅ cr)>> /\
     <<STR: str = Any.pair st mr↑>> /\
     <<STR': str' = Any.pair st mr'↑>>).
  Proof.
    ss. des; subst; [|right]; esplits; eauto.
    destruct (classic (exists stx (mrx:Σ), str = Any.pair stx mrx↑)); eauto.
    des. subst. right. esplits; eauto.
    eapply own_ctx with (ctx := mrx) in RELr. revert RELr. r_solve. i.
    rewrite-> URA.add_comm, (URA.add_comm fr' mrx). eauto.
  Qed.
  
  Lemma hp_reconf_fail
    r R RR str i i'
    (FAIL: ~ exists st (mr:Σ), str = Any.pair st mr↑)
    :
    paco4 _sim_strict r R RR
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i mr)
      (str, p <- unwrapU (Any.split str);;
            mr <- (let '(st,_mr) := p in unwrapU (@Any.downcast Σ _mr));; i' mr).
  Proof.
    destruct (Any.split str) eqn:STR; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn:T0; cycle 1.
    { ss. unfold triggerUB. grind. pstep. econs. i. inv x. }
    apply Any.split_pair in STR. apply Any.downcast_upcast in T0.
    exfalso. eapply FAIL. des; subst. eauto.
  Qed.

(*  
  Lemma handle_Guarantee_reconf
    P str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_equiv cr)
      (str, handle_Guarantee P fr)
      (str', handle_Guarantee P fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget, mput.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1, c2⋅cr).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]". iSplitL "X"; eauto.
      iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. right. esplits; eauto.
    r_solve. eauto.
  Qed.

  Lemma handle_Guarantee_reconf_true
    str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel _ hp_reconf_eq cr)
      (str, handle_Guarantee True fr)
      (str', handle_Guarantee True fr').
  Proof.
    ginit. unfold handle_Guarantee, guarantee, mget, mput.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, c1⋅cr, c2).
    grind; gstep; econs; i.
    grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
    { gfinal. right. apply hp_reconf_fail. eauto. }
    rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
    grind; gstep; econs; i. eexists.
    { r_solve. iIntros "H". iPoseProof (RELr0 with "H") as "H". iMod "H".
      iDestruct "H" as "[X Y]".
      rewrite -URA.add_assoc (URA.add_comm cr c2) URA.add_assoc.
      iSplitL "X"; eauto. iPoseProof (x' with "X") as "X". eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    grind; gstep; econs; i. grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    split; eauto. split; eauto.
  Qed.
 *)
  
  Lemma trigger_hAGE_simpl R (P: iProp) (e : hAGE R):
    (trigger (e|)%sum : itree hAGEs R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma trigger_callE_simpl R (P: iProp) (e : callE R):
    (trigger (|e|)%sum : itree hAGEs R) = trigger e.
  Proof. reflexivity. Qed.

  Lemma trigger_sE_simpl R (P: iProp) (e : sE R):
    (trigger (|e|)%sum : itree hAGEs R) = trigger e.
  Proof. reflexivity. Qed.

(*  
  Lemma interp_hp_reconf
    R itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ (hp_reconf_rel R hp_reconf_equiv cr)
      (str, interp_hp itrH fr)
      (str', interp_hp itrH fr').

      Proof.
    revert_until I. ginit. gcofix CIH; i.
    assert (CASE := case_itrH _ itrH). des; subst.
    - rewrite !interp_hp_ret.
      gstep. econs. rr. esplits; eauto.
    - rewrite-> !interp_hp_tau.
      grind; gstep; econs; i. eauto 10 with paco.
    - rewrite-> !interp_hp_bind, !interp_hp_Assume.
      unfold handle_Assume, assume, mget, mput.
      grind; gstep; econs; i. exists x.
      grind; gstep; econs; i.
      grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst).
      { gfinal. right. apply hp_reconf_fail. eauto. }
      rewrite !Any.pair_split. grind. rewrite !Any.upcast_downcast.
      grind; gstep; econs; i. eexists.
      { eapply own_ctx with (ctx := x) in RELr0. rewrite !URA.add_assoc in RELr0.
        eapply own_wf in RELr0; eauto. eapply URA.wf_mon; eauto. }
      grind; gstep; econs; i. eexists. { eauto. }
      grind; gstep; econs; i.
      gfinal. left. eapply CIH. right. esplits; eauto.
      { eapply own_ctx with (ctx := x) in RELr0.
        rewrite !URA.add_assoc in RELr0. eauto using own_wf. }
    - rewrite-> !interp_hp_bind, !interp_hp_Guarantee. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf. eauto. }
      i. grind; gstep; econs; i.
      gfinal. left. eapply CIH. destruct v0, v0'. rr in REL. des; subst. ss.
    - rewrite-> !interp_hp_bind, !interp_hp_call. grind.
      guclo sim_strict_bindC_spec. econs.
      { gfinal. right. eapply paco4_mon_bot; eauto.
        eapply handle_Guarantee_reconf_true. eauto. }
      i. destruct v0, v0', c. repeat (rr in REL; des; subst).
      repeat (grind; gstep; econs; i).
      gfinal. left. eapply CIH. left. s. eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggerp.
      destruct s. unfold handle_sE_tgt, pupdate.
      repeat (grind; gstep; econs; i).
      grind; apply hp_reconf_equiv_strong in RELr; repeat (rr in RELr; des; subst); cycle 1.
      { rewrite !Any.pair_split. grind.
        gfinal. left. eapply CIH. right. esplits; eauto. }
      gfinal. left. eapply CIH.
      destruct (Any.split str) as [[]|] eqn: STR.
      { left. s. esplits; eauto. }
      left. s. esplits; eauto.
    - rewrite-> !interp_hp_bind, !interp_hp_triggere.
      destruct e.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + grind; gstep; econs; i. eexists.
        repeat (grind; gstep; econs; i). eauto 10 with paco.
      + repeat (grind; gstep; econs; i). eauto 10 with paco.
  Qed.
  
  Lemma hp_fun_tail_reconf
    str str' (fr fr' cr: Σ) x
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
      (str, hp_fun_tail (fr,x))
      (str', hp_fun_tail (fr',x)).
  Proof.
    ginit. unfold hp_fun_tail. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst).
    eauto with paco.
  Qed.

  Lemma interp_hp_body_reconf
    itrH str str' (fr fr' cr: Σ)
    (RELr: hp_reconf_equiv cr (str,fr) (str',fr'))
    :
    sim_strict _ eq
      (str, interp_hp_body itrH fr)
      (str', interp_hp_body itrH fr').
  Proof.
    ginit. unfold interp_hp_body.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf. eauto. }
    i. destruct v0, v0'. repeat (rr in REL; des; subst); cycle 1.
    - gfinal. right. eapply hp_fun_tail_reconf. right. esplits; eauto.
    - gfinal. right. eapply hp_fun_tail_reconf. left. esplits; eauto.
      rr. esplits; eauto.
  Qed.

  Lemma interp_strict_inline_src
    itrH ktrH st (fr mr: Σ)
    :
    sim_strict Any.t eq
      (Any.pair st (fr ⋅ mr)↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (ε,x));; interp_hp_body (ktrH rv) rr)
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr).
  Proof.
    ginit. guclo sim_strict_transC_spec. econs; cycle 1.
    { gfinal. right. eapply interp_hp_body_reconf with (fr := (ε:Σ)) (cr:=(ε:Σ)).
      right. esplits; eauto. instantiate (1:= fr ⋅ mr). r_solve. eauto. }
    { i. destruct PR. subst. eauto. }
    unfold interp_hp_body. rewrite !interp_hp_bind.
    grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. apply sim_strict_refl. }
    i. depdes REL. rewrite-> interp_hp_bind, interp_hp_Guarantee.
    destruct v0' as [fr' st']. unfold hp_fun_tail at 1. grind.
    unfold handle_Guarantee, mget, mput, guarantee, sGet, sPut.
    grind; gstep; econs; i. destruct x' as [[c0 c1] c2]. exists (c0, ε, c1 ⋅ c2).
    grind; gstep; econs; i.
    ss. destruct (Any.split st0') eqn: ST0'; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    grind. destruct (Any.downcast t0) eqn: T0; ss; cycle 1.
    { unfold triggerUB. grind; gstep; econs. i. inv x. }
    apply Any.split_pair in ST0'. rr in ST0'. subst.
    apply Any.downcast_upcast in T0. rr in T0. subst.
    grind; gstep; econs; i. eexists. { r_solve. eauto. }
    grind; gstep; econs; i. eexists. { eauto. }
    repeat (grind; gstep; econs; i).
    grind. rewrite !Any.pair_split.
    repeat (grind; gstep; econs; i).
    gfinal. right. eapply interp_hp_body_reconf with (cr:=(ε:Σ)).
    right. esplits; eauto. r_solve. eauto.
  Qed.

  Lemma interp_strict_inline_tgt
    itrH ktrH st (fr mr fr' mr': Σ)
    (RELr: Own (fr ⋅ mr) ⊢ #=> Own (fr' ⋅ mr'))
    :
    sim_strict Any.t eq
      (Any.pair st mr↑, interp_hp_body (x <- itrH;; trigger (Guarantee True) ;;; ktrH x) fr)
      (Any.pair st mr'↑, x <- interp_hp_body itrH ε;; '(rr,rv) <- (tau;; Ret (fr',x));; interp_hp_body (ktrH rv) rr).
  Proof.
    ginit. unfold interp_hp_body. rewrite-> !interp_hp_bind. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply interp_hp_reconf with (cr:=fr').
      right. esplits; eauto. r_solve.
      rewrite (URA.add_comm mr' fr'). eauto. }
    i. rewrite-> !interp_hp_bind, interp_hp_Guarantee. unfold hp_fun_tail. grind.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      destruct v0. ss. des; subst; eauto.
      right. esplits; eauto. }
    i. grind; gstep; econs; i.
    destruct v0. rr in REL; des; subst. simpl. destruct v1, v0'.
    guclo sim_strict_bindC_spec. econs.
    { gfinal. right.  eapply interp_hp_reconf with (cr:=c2).
      s in REL0; des; subst. left. s. esplits; eauto.
      rewrite URA.add_comm. eauto. }
    i. grind. guclo sim_strict_bindC_spec. econs.
    { gfinal. right. eapply handle_Guarantee_reconf_true.
      r in REL1. des; subst. eauto. }
    i. gstep; econs. rr in REL1. des; subst.
    destruct v0, v0'. s in REL2; des; subst. eauto. 
  Qed.
 *)


  (*** ****)
  

  (*** ****)

  
Variant interp_inv: Σ -> Any.t * Any.t -> Prop :=
| interp_inv_intro
     st_src st_tgt (ctxi mr mr_src mr_tgt: Σ)
    (* (WF: URA.wf mr_src) *)
    (MRS: mr_src = ctxi ⋅ mr ⋅ mr_tgt)
    (MR: Own mr ⊢ I st_src st_tgt)
  :
  interp_inv ctxi (Any.pair st_src mr_src↑, Any.pair st_tgt mr_tgt↑)
.

Lemma hpsim_adequacy:
  forall
    (fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) 
    (FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
    (FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
    p_src p_tgt st_src st_tgt itr_src itr_tgt
    (ctx mr_src mr_tgt fr_src fr_tgt ctxi_src ctxi_tgt ctxe fmr: Σ)
    (SIM: hpsim_body fl_src fl_tgt I p_src p_tgt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
    (WF: URA.wf (fr_src ⋅ mr_src ⋅ ctxi_src ⋅ ctxe))
    (FMR: fr_src ⋅ mr_src = fmr ⋅ fr_tgt ⋅ mr_tgt)
    (CTXR: ctxi_tgt = ctxi_src ⋅ fmr),
  @sim_itree Σ interp_inv eq fl_src0 fl_tgt0 p_src p_tgt ctx
    (Any.pair st_src mr_src↑, interp_hp_body itr_src (fr_src, ctxi_src, ctxe))
    (Any.pair st_tgt mr_tgt↑, interp_hp_body itr_tgt (fr_tgt, ctxi_tgt, ctxe)).
Proof.
  (* i. apply hpsim_add_dummy in SIM. *)
  i. revert_until I. ginit. gcofix CIH. i.
  remember (st_src, itr_src). remember (st_tgt, itr_tgt).
  move SIM before FLT. revert_until SIM.
  punfold SIM. induction SIM; i; clarify; cycle 1.


  - (* "Call Case" DONE!  *)

    move INV at bottom. unfold interp_hp_body.
    steps. unfold handle_callE, handle_Guarantee, give_iprop, take_iprop, guarantee, assume, mget, mput.
    steps.
    i. hexploit iProp_sepconj; [eauto|refl| |].
    { instantiate (1:= c0 ⋅ c1 ⋅ c ⋅ ctxi_src ⋅ ctxe).
      eapply eq_ind; eauto. r_solve.
    }
    i. des.
    force_l. instantiate (1:= (ε, ε, c0 ⋅ c1 ⋅ c ⋅ a ⋅ b)).
    steps_safe. force_l.
    { eapply eq_ind; eauto. r_solve. }
    force_l; eauto.
    steps_safe. force_r. instantiate (1:= (ε, c2 ⋅ c0 ⋅ a ⋅ b ⋅ c3)).
    steps_safe. force_r.
    { eapply eq_ind; eauto. r_solve. }
    steps_safe. force_r; eauto.
    grind. eapply safe_sim_sim; econs.
    esplits; i.
    { econs; cycle 1.
      { instantiate (1:= a).
        uiprop. i. eapply iProp_mono; eauto. }
      instantiate (1:= b ⋅ c0 ⋅ c1). r_solve.
    }
    inv WF0.
    unfold handle_Assume, give_iprop, take_iprop, guarantee, assume, mget, mput.
    steps. force_r. instantiate (1:= x3).
    steps. force_r. instantiate (1:= (ε, c4 ⋅ c2 ⋅ b ⋅ c0 ⋅ mr ⋅ c5)).
    steps. force_r.
    { eapply eq_ind; eauto. r_solve. }
    steps. force_r; eauto.
    steps. force_l. instantiate (1:= (c7, b ⋅ c0 ⋅ c2 ⋅ c4 ⋅ c6 ⋅ c8, mr)).
    steps. force_l.
    { eapply eq_ind; eauto. r_solve. }
    steps. force_l; eauto.
    steps. eapply H; cycle 5.
    { instantiate (1:= b ⋅ c0 ⋅ c2 ⋅ c4 ⋅ mr).
      eapply eq_ind; eauto. r_solve. }
    { eapply eq_ind; eauto. r_solve. }
    { eapply URA.wf_mon in x6. rewrite (URA.add_comm (c7 ⋅ c8 ⋅ c6)) in x6.
      do 2 eapply URA.wf_mon in x6. eapply eq_ind; eauto. r_solve. }
    { eapply from_semantic. rewrite (URA.add_comm _ mr).
      uiprop. esplits; eauto.
      - uiprop in MR. eapply MR; try refl.
        revert x6. r_solve. i. do 2 eapply URA.wf_mon in x6.
        rewrite (URA.add_comm _ mr) in x6. repeat eapply URA.wf_mon in x6. eauto.
      - eapply iProp_mono; eauto.
        + eapply URA.wf_mon in x6. rewrite (URA.add_comm (c7 ⋅ c8 ⋅ c6)) in x6.
          do 3 eapply URA.wf_mon in x6. eapply eq_ind; eauto. r_solve.
        + rewrite <-!URA.add_assoc. rr; esplits; eauto.
    }
    { eauto. }
    { eauto. }
    { rewrite -!URA.add_assoc -URA.add_comm in x6. eapply URA.wf_mon in x6.
      eapply eq_ind; eauto. r_solve. }

(*    
  - unfold interp_hp_body, hp_fun_tail, handle_Guarantee, guarantee, mget, mput.
  steps. force_l. instantiate (1 := (c0, c1, ctx ⋅ fmr ⋅ c)). steps.
  force_l.
  {
    eapply own_trans; et. rewrite <- URA.add_assoc.
    replace (c0 ⋅ c1 ⋅ (ctx ⋅ fmr ⋅ c)) with (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)); [|r_solve].
    eapply own_ctx; et.  
  } 
  steps. force_l; et. 
  steps. econs.
  unfold hpsim_end in RET.
  esplits; et.
  { 
    econs; et.
    {
      eapply own_wf in FMR; et. rewrite <- URA.add_assoc in FMR. 
      eapply own_ctx in x. eapply own_wf in x; et.
      replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
      eapply URA.wf_mon; et.
    }
    { iIntros "H". iPoseProof (RET with "H") as "H". iMod "H". iDestruct "H" as "[H H0]". et. }
  }
  {
    eapply own_wf in FMR; et. do 2 eapply URA.wf_mon in FMR. eapply URA.wf_split in FMR. des.
    rr in RET. uipropall. hexploit RET; [et|refl|instantiate (1:= ε); r_solve; et|].
    i. des. rr in H2. uipropall.
  }
- unfold interp_hp_body. hexploit INV. i.
  assert (FMRWF: URA.wf (fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt))). 
  { eapply own_wf in FMR; et. replace (fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt); r_solve. et. }
  eapply iProp_sepconj in H0; [|refl|et]. des. rename a into fr. rename b into mr.
  steps. unfold handle_Guarantee, guarantee, mget, mput. steps_safe.
  force_l. instantiate (1:= (c0, ε, ctx ⋅ fr ⋅ c1 ⋅ mr ⋅ c)). steps_safe.
  rename c1 into frt. rename c into mrt.
  force_l.
  { 
    replace (c0 ⋅ ε ⋅ (ctx ⋅ fr ⋅ frt ⋅ mr ⋅ mrt)) with (ctx ⋅ (mr ⋅ fr) ⋅ (c0 ⋅ frt ⋅ mrt)); [|r_solve].
    eapply own_trans; et.     
    rewrite <- (URA.add_assoc (ctx ⋅ fmr) fr_tgt mr_tgt).
    iIntros "[[H H0] X]". iSplitL "H H0".
    { iSplitL "H"; et. iPoseProof (H0 with "H0") as "H"; et. }
    { iPoseProof (x with "X") as "H"; et. }
  }
  steps_safe. 
  force_l; et.
  steps_safe. eapply safe_sim_sim; econs. esplits; i.
  { 
    instantiate (1:= ctx ⋅ fr ⋅ frt). econs; [ |et|eapply own_mod; et].
    eapply own_wf in FMR; et. 
    eapply own_ctx in x. rewrite <- URA.add_assoc in FMR. eapply own_wf in x; et.
    replace (ctx ⋅ fmr ⋅ (c0 ⋅ frt ⋅ mrt)) with (c0 ⋅ ctx ⋅ frt ⋅ mrt ⋅ fmr) in x; r_solve.
    eapply own_ctx in H0. eapply own_wf in H0; et.
    rewrite <- !URA.add_assoc in H0. rewrite URA.add_comm in H0.
    eapply URA.wf_mon in H0.
    replace (ctx ⋅ (frt ⋅ (mrt ⋅ (mr ⋅ fr)))) with (ctx ⋅ fr ⋅ frt ⋅ mr ⋅ mrt) in H0; r_solve; et.          
  }
  steps.
  inv WF0. eapply H with (fmr0 := fr ⋅ mr0); [| |et|et|r_solve; et|].
  {  
    eapply own_wf in MRS; et.
    replace (ctx ⋅ fr ⋅ frt ⋅ mr0 ⋅ mr_tgt0) with (fr ⋅ mr0 ⋅ (ctx ⋅ frt ⋅ mr_tgt0)) in MRS; r_solve.
    eapply URA.wf_mon; et.
  }
  {
    iIntros "[H H0]". 
    iPoseProof (H2 with "H") as "FR". iPoseProof (MR with "H0") as "INV". iMod "INV".  
    iFrame. et.
  }
  { r_solve. replace (ctx ⋅ fr ⋅ mr0 ⋅ frt ⋅ mr_tgt0) with (ctx ⋅ fr ⋅ frt ⋅ mr0 ⋅ mr_tgt0); et. r_solve. }
- unfold interp_hp_body. steps. eapply H; et.
- exploit IHSIM; eauto. i.
  rewrite-> interp_hp_body_bind, interp_hp_call.
  unfold handle_Guarantee, mget, mput, guarantee. 
  steps. force_l. instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
  steps. force_l. { r_solve; et. }
  steps. force_l; et. steps.
  {	instantiate (1:= interp_hp_fun f).
  rewrite alist_find_map. rewrite FUN. et. }
  guclo sim_strictC_spec. econs; eauto.
  + apply interp_strict_inline_src.
  + apply sim_strict_refl.
- exploit IHSIM; eauto. i.
  rewrite-> interp_hp_body_bind, interp_hp_call.
  unfold handle_Guarantee, mget, mput, guarantee.
  steps.
  {	instantiate (1:= interp_hp_fun f).
  rewrite alist_find_map. rewrite FUN. et. }
  guclo sim_strictC_spec. econs; eauto.
  + apply sim_strict_refl.      
  + apply interp_strict_inline_tgt.
    { iIntros "H". iPoseProof (x with "H") as "H". iMod "H".
      iDestruct "H" as "[[X Y] Z]". iModIntro. iSplitL "Y"; eauto. }
- unfold interp_hp_body. steps. eapply IHSIM; et.
- unfold interp_hp_body. steps. eapply IHSIM; et.
- unfold interp_hp_body. steps. force_l. steps. eapply IHSIM; et.
- unfold interp_hp_body. steps. eapply H; et.
- unfold interp_hp_body. steps. eapply H; et.
- unfold interp_hp_body. steps. force_r. steps. eapply IHSIM; et.
- unfold interp_hp_body. steps. rewrite Any.pair_split. steps. rewrite RUN. eapply IHSIM; et.
- unfold interp_hp_body. steps. rewrite Any.pair_split. steps. rewrite RUN. eapply IHSIM; et.
- unfold interp_hp_body. steps. rewrite interp_hp_Assume. unfold handle_Assume, mget, mput.
  steps. eapply H with (fmr0 := x ⋅ fmr); et.
  { 
    eapply own_ctx with (ctx := x) in FMR0. revert FMR0; r_solve; i.
    eapply own_wf in FMR0; et. replace (x ⋅ ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with (x ⋅ fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) in FMR0; r_solve.
    eapply URA.wf_mon. et.
  }
  { 
    iIntros "[H H0]".
    iPoseProof (_ASSUME0 with "H") as "H". iPoseProof (CUR with "H0") as "H0". iMod "H0".
    iFrame; et.
  }  
  {
    eapply own_ctx with (ctx := x) in FMR0; et. rewrite URA.add_assoc in FMR0.
    replace (x ⋅ (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ x ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) in FMR0; r_solve.
    et.
  }
- unfold interp_hp_body. steps.
  rewrite interp_hp_Assume.
  hexploit CUR. i. eapply iProp_sepconj in H0. des. rename rq into fmr0.
  unfold handle_Assume, assume, mget, mput. 
  steps. force_r. instantiate (1:= rp).
  steps. force_r.
  {
    eapply own_wf in FMR0; et.
    rewrite <- URA.add_assoc in FMR0. rewrite URA.add_comm in FMR0. rewrite URA.add_assoc in FMR0.
    eapply own_ctx in H0. eapply own_wf in H0; et.
    replace (fr_tgt ⋅ mr_tgt ⋅ ctx ⋅ (rp ⋅ fmr0)) with (rp ⋅ fr_tgt ⋅ mr_tgt ⋅ (ctx ⋅ fmr0)) in H0; r_solve.
    eapply URA.wf_mon; et.
  }
  steps. force_r; et.
  steps. eapply H with (fmr0 := fmr0); et.
  {
    eapply own_wf in FMR0; et. rewrite <- URA.add_assoc in FMR0. eapply URA.wf_mon in FMR0.
    eapply URA.wf_split in FMR0. des.
    eapply own_wf in H0; et. eapply URA.wf_mon. rewrite URA.add_comm. et.
  }
  { eapply own_mod; et. }
  {
    replace (fmr0 ⋅ (rp ⋅ fr_tgt) ⋅ mr_tgt) with (rp ⋅ fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve. 
    iIntros "H". iPoseProof (FMR0 with "H") as "H". iMod "H".
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    rewrite <- URA.add_assoc.
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    iPoseProof (H0 with "H0") as "H"; et. iMod "H".
    iDestruct "H" as "[H H0]". iSplitL "H0"; et.
  }
- unfold interp_hp_body. steps.
  rewrite interp_hp_Guarantee.
  hexploit CUR. i. eapply iProp_sepconj in H0. des. rename rq into fmr0.
  unfold handle_Guarantee, guarantee, mget, mput.
  steps. force_l. instantiate (1:= (rp, fmr0 ⋅ fr_tgt, ctx ⋅ mr_tgt)).
  steps. force_l. 
  {
    replace (rp ⋅ (fmr0 ⋅ fr_tgt) ⋅ (ctx ⋅ mr_tgt)) with (ctx ⋅ rp ⋅ fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve. 
    iIntros "H". iPoseProof (FMR0 with "H") as "H". iMod "H".
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    rewrite <- URA.add_assoc. 
    iDestruct "H" as "[H H0]". iSplitL "H"; et.
    iPoseProof (H0 with "H0") as "H"; et.
  }
  steps. force_l; et.
  steps. eapply H with (fmr0 := fmr0); et.
  {
    eapply own_wf in FMR0; et. do 2 eapply URA.wf_mon in FMR0. eapply URA.wf_split in FMR0. des.
    eapply own_wf in H0; et. eapply URA.wf_split in H0. des. et.
  }
  { eapply own_mod; et. }
  {
    eapply own_wf in FMR0; et.
    replace (ctx ⋅ fmr ⋅ fr_tgt ⋅ mr_tgt) with (fr_tgt ⋅ mr_tgt ⋅ ctx ⋅ fmr) in FMR0; r_solve.
    eapply own_ctx in H0. eapply own_wf in H0; et.
    replace (fr_tgt ⋅ mr_tgt ⋅ ctx ⋅ (rp ⋅ fmr0)) with (fmr0 ⋅ fr_tgt ⋅ ctx ⋅ mr_tgt ⋅ rp) in H0; r_solve.
    eapply URA.wf_mon; et.
  }
  { replace (fmr0 ⋅ fr_tgt ⋅ (ctx ⋅ mr_tgt)) with (ctx ⋅ fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve; et. }
- unfold interp_hp_body. steps.
  rewrite interp_hp_Guarantee. unfold handle_Guarantee, guarantee, mget, mput.
  steps. eapply H with (fmr0 := c0 ⋅ fmr); et.
  {
    eapply own_wf in FMR0; et. rewrite <- URA.add_assoc in FMR0.
    eapply own_ctx in x. eapply own_wf in x; et.
    replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (c0 ⋅ fmr ⋅ (ctx ⋅ c1 ⋅ c)) in x; r_solve.
    eapply URA.wf_mon; et. 
  }
  {
    iIntros "[P FMR]". iPoseProof (x0 with "P") as "P". iPoseProof (CUR with "FMR") as "FMR".
    iSplitL "P"; et.  
  }
  {
    eapply own_trans; et.
    replace (ctx ⋅ (c0 ⋅ fmr) ⋅ c1 ⋅ c) with (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)); [|r_solve].
    rewrite <- URA.add_assoc. eapply own_ctx. et.
  }
- pclearbot. gstep. econs. gfinal. left. eapply CIH; et.
Qed.
 *)
Admitted.    

End HPSIM.
