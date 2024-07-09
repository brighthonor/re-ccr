From stdpp Require Import coPset gmap namespaces.
Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Require Import Coqlib PCM PCMAux IProp IPM SRF sProp.
Require Import Coq.Logic.ClassicalEpsilon.

Local Notation univ_id := positive.
Local Notation level := nat.

Section INDEXED_INVARIANT_SET.

  Context `{_W: CtxSL.t}.
  
  Definition InvSetRA (n : level) : URA.t :=
    (Auth.t (positive ==> URA.agree (SRFSyn.t n)))%ra.

  Definition OwnIRA : URA.t :=
    URA.pointwise univ_id (@URA.pointwise_dep level InvSetRA).

  Definition OwnERA : URA.t :=
    URA.pointwise univ_id (CoPset.t).
  
  Definition OwnDRA : URA.t :=
    URA.pointwise univ_id (Auth.t Gset.t).

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{_W: CtxSL.t}.
  Context `{@GRA.inG OwnIRA Σ}.
  
  Definition OwnIR (u: univ_id) (n : level) (i : positive) (p : SRFSyn.t n) : OwnIRA :=
    maps_to_res u (@maps_to_res_dep level InvSetRA
      n (Auth.white (@maps_to_res positive (URA.agree (SRFSyn.t n)) i (Some (Some p))))).
  
  Definition OwnI (u: univ_id) (n : level) (i : positive) (p : SRFSyn.t n) :=
    OwnM (OwnIR u n i p).

  Definition OwnI_authR (u: univ_id) (n : level) (I : gmap positive (SRFSyn.t n)) : OwnIRA :=
    maps_to_res u (@maps_to_res_dep level _
      n (@Auth.black (positive ==> URA.agree (SRFSyn.t n))%ra (fun i => Some <$> (I !! i)))).

  Definition OwnI_auth (u: univ_id) (n: level) (I : gmap positive (SRFSyn.t n)) :=
    OwnM (OwnI_authR u n I).

  Context `{@GRA.inG OwnERA Γ}.
   
  Definition OwnER (u: univ_id) (E: coPset) : OwnERA :=
    @maps_to_res _ CoPset.t u (Some E).
  
  Definition OwnE (u: univ_id) (E: coPset) : iProp :=
    OwnM (OwnER u E).

  Context `{@GRA.inG OwnDRA Γ}.
   
  Definition OwnDR (u: univ_id) (D: gset positive) : OwnDRA :=
    maps_to_res u (Auth.white (Some D: Gset.t)).
  
  Definition OwnD (u: univ_id) (D: gset positive) :=
    OwnM (OwnDR u D).

  Definition OwnD_authR  (u: univ_id) (D: gset positive) : OwnDRA :=
    maps_to_res u (Auth.black (Some D : Gset.t)).

  Definition OwnD_auth (u: univ_id) : iProp :=
    (∃ D, OwnM (OwnD_authR u D))%I.

  Lemma OwnE_exploit u (E1 E2 : coPset) :
    OwnE u E1 ∗ OwnE u E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro.
    rewrite /URA.wf /URA.add /OwnER /maps_to_res in WF. unseal "ra". ss. specialize (WF u).
    des_ifs. rewrite /URA.wf /URA.add in WF. unseal "ra". ss; des_ifs.
  Qed.

  Lemma OwnE_union u (E1 E2 : coPset) :
    OwnE u E1 ∗ OwnE u E2 ⊢ OwnE u (E1 ∪ E2).
  Proof.
    iIntros "H". iPoseProof (OwnE_exploit with "H") as "%D".
    iRevert "H". iApply from_sep. eapply from_sep_ownM.
    unfold IsOp, OwnER, maps_to_res, URA.add. ss. unseal "ra".
    extensionalities u'. des_ifs; ss; r_solve.
    repeat (unfold URA.add; unseal "ra"; ss; des_ifs).
  Qed.

  Lemma OwnE_disjoint u (E1 E2 : coPset) :
    E1 ## E2 -> OwnE u (E1 ∪ E2) ⊢ OwnE u E1 ∗ OwnE u E2.
  Proof.
    i. unfold OwnE.
    iApply into_sep. eapply into_sep_ownM.
    unfold IsOp, OwnER, maps_to_res, URA.add. ss. unseal "ra".
    extensionalities u'. des_ifs; r_solve.
    repeat (unfold URA.add; unseal "ra"; ss; des_ifs).
  Qed.

  Lemma OwnE_subset u (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE u E2 ⊢ OwnE u E1 ∗ (OwnE u E1 -∗ OwnE u E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply leibniz_equiv. eapply union_difference. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent 
    u n i p : Persistent (OwnI u n i p).
  Proof.
    unfold OwnI, OwnIR.
    remember (@maps_to_res_dep level InvSetRA n (Auth.white (@maps_to_res positive (URA.agree (SRFSyn.t n)) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ _ _ with "H") as "#HP". iModIntro.
    replace (maps_to_res u r) with (URA.core (maps_to_res u r)) at 2. auto.
    subst. unfold maps_to_res_dep, maps_to_res. ss. extensionalities u' n'. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{_W: CtxSL.t}.
  Context `{_W0: @GRA.inG OwnIRA Σ}.
  Context `{_W1: @GRA.inG OwnERA Γ}.
  Context `{_W2: @GRA.inG OwnDRA Γ}.

  Variable u : univ_id.
  Variable n : level.
  

  Definition inv_satall (I : gmap positive (SRFSyn.t n)) :=
    ([∗ map] i ↦ p ∈ I, ((@SRFSem.t (@SL.domain Σ) α β n p) ∗ OwnD u {[i]}) ∨ OwnE u {[i]})%I.

  Definition wsat : iProp := (∃ I, OwnI_auth u n I ∗ inv_satall I)%I.

  Lemma alloc_name φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u ⊢ |==>  OwnD_auth u ∗ ∃ i, ⌜φ i⌝ ∧ OwnD u {[i]}.
  Proof.
    iIntros "[% DA]". specialize (INF (fun _ => Some D) n). ss. des.
    assert (@URA.updatable
              OwnDRA
              (maps_to_res u (Auth.black (Some D : Gset.t)))
              ((maps_to_res u (Auth.black (Some (D ∪ {[i]}) : Gset.t)))
               ⋅
               (maps_to_res u (Auth.white (Some {[i]} : Gset.t))))) as UPD.
    { rewrite !maps_to_res_add. apply maps_to_res_updatable.
      ii. ur in H. des_ifs. des. rewrite URA.unit_idl in H.
      unfold URA.extends in H. des. ur in H.
      ur. rewrite URA.unit_idl. split.
      { exists ctx. ur. des_ifs; ss.
        2:{ des_ifs. set_solver. }
        des_ifs.
        2:{ set_solver. }
        f_equal. set_solver.
      }
      { ur. ss. }
    }
    iMod (OwnM_Upd UPD with "DA") as "[DA D]".
    iModIntro. iSplitL "DA".
    { iExists _. iFrame. }
    { iExists i. iFrame. auto. }
  Qed.

  Lemma wsat_OwnI_alloc_gen p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u ∗ wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ OwnD_auth u ∗ ((@SRFSem.t (@SL.domain Σ) α β n p) -∗ wsat).
  Proof.
    iIntros "[DA [% [AUTH SAT]]]".
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i) with "DA") as "[DA [% [[%iI %iφ] D]]]".
    { i.
      set (uni := fun n => match E n with
                        | None => None
                        | Some G => Some (G ∪ dom I)
                        end).
      specialize (INF uni n0). subst uni. ss. des_ifs.
      des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    pose (<[i:=p]> I) as I'.

    assert (URA.updatable
              (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (SRFSyn.t n))%ra (fun i => Some <$> (I !! i)))): OwnIRA)
              ((maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (SRFSyn.t n))%ra (fun i => Some <$> (I' !! i)))): OwnIRA)
               ⋅
               (maps_to_res u (maps_to_res_dep n (Auth.white (@maps_to_res _ (URA.agree (SRFSyn.t n)) i (Some (Some p))))): OwnIRA))).
    { setoid_rewrite maps_to_res_add. setoid_rewrite maps_to_res_dep_add.
      apply maps_to_res_updatable. apply maps_to_res_dep_updatable.
      apply Auth.auth_alloc. ii. des. rewrite URA.unit_idl in FRAME. subst. split.
      { rr; unseal "ra". ss. intro. rr; unseal "ra". destruct (I' !! k); ss. }
      rr. subst I'.
      unfold URA.add. unseal "ra". ss.
      extensionalities j. unfold maps_to_res. des_ifs.
      - rewrite lookup_insert. rewrite not_elem_of_dom_1; ss.
        unfold URA.add. unseal "ra". ss.
      - rewrite URA.unit_idl. rewrite lookup_insert_ne; eauto.
    }
    unfold OwnI_auth, inv_satall.
    iMod (OwnM_Upd H with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iFrame. iIntros "P". unfold wsat. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u ∗ wsat ∗ ⟦p⟧ ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ OwnD_auth u ∗ wsat.
  Proof.
    iIntros "(D & W & P)".
    iMod (wsat_OwnI_alloc_gen with "[D W]") as "(I & D & W)". eauto. iFrame.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI u n i p ∗ wsat ∗ OwnE u {[i]} ⊢ |==> (@SRFSem.t (@SL.domain Σ) α β n p) ∗ wsat ∗ OwnD u {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & EN)". iModIntro.
    unfold OwnI, OwnI_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold OwnI_authR in WF.
      setoid_rewrite maps_to_res_add in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF.
      apply (pw_lookup_wf _ u) in WF. apply (pwd_lookup_wf _ n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
         exfalso. unfold OwnER, maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
         specialize (WF u). unfold URA.wf, URA.add in WF. unseal "ra". ss.
         des_ifs. unfold URA.wf, URA.add in WF. unseal "ra".
         ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI u n i p ∗ wsat ∗ ⟦p⟧ ∗ OwnD u {[i]} ⊢ |==> wsat ∗ OwnE u {[i]}.
  Proof.
    iIntros "(I & [% [AUTH SAT]] & P & DIS)". iModIntro.
    unfold OwnI, OwnI_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold OwnI_authR in WF.
      setoid_rewrite maps_to_res_add in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF.
      apply (pw_lookup_wf _ u) in WF. apply (pwd_lookup_wf _ n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0.
      rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
      exfalso. unfold OwnDR, maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
      specialize (WF u). unfold URA.wf, URA.add in WF. unseal "ra".
      des_ifs. ur in WF. ur in WF. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnI_auth u n ∅ ⊢ wsat.
  Proof.
    iIntros "H".
    iExists ∅. iFrame. unfold inv_satall. iApply big_sepM_empty. ss.
  Qed.

End WORLD_SATISFACTION.

Section UNIVERSE.

  Fixpoint pos_sup (p i: positive) : bool :=
    match p, i with
    | 1, _ => true
    | p'~0, i'~0 => pos_sup p' i'
    | p'~1, i'~1 => pos_sup p' i'
    | _, _ => false
    end%positive.

  Fixpoint pos_ext_0 (p: positive) : positive :=
    match p with
    | 1 => 1~0
    | p'~0 => (pos_ext_0 p')~0
    | p'~1 => (pos_ext_0 p')~1
    end%positive.

  Fixpoint pos_ext_1 (p: positive) : positive :=
    match p with
    | 1 => 1~1
    | p'~0 => (pos_ext_1 p')~0
    | p'~1 => (pos_ext_1 p')~1
    end%positive.

  Lemma pos_sup_refl p:
    pos_sup p p = true.
  Proof. induction p; s; eauto. Qed.
  
  Lemma pos_sup_trans p0 p1 p2
    (EXT1: pos_sup p0 p1 = true)
    (EXT2: pos_sup p1 p2 = true)
    :
    pos_sup p0 p2 = true.
  Proof.
    revert_until p0. induction p0; i; destruct p1, p2; ss; eauto.
  Qed.
  
  Lemma pos_ext_0_sup_true p:
    pos_sup p (pos_ext_0 p) = true.
  Proof. induction p; s; eauto. Qed.

  Lemma pos_ext_1_sup_true p:
    pos_sup p (pos_ext_1 p) = true.
  Proof. induction p; s; eauto. Qed.

  Lemma pos_ext_0_sup_false p:
    pos_sup (pos_ext_0 p) p = false.
  Proof. induction p; s; eauto. Qed.

  Lemma pos_ext_1_sup_false p:
    pos_sup (pos_ext_1 p) p = false.
  Proof. induction p; s; eauto. Qed.
  
  Lemma pos_ext_0_neq p:
    p ≠ pos_ext_0 p.
  Proof. induction p; eauto; ii; depdes H; eauto. Qed.

  Lemma pos_ext_1_neq p:
    p ≠ pos_ext_1 p.
  Proof. induction p; eauto; ii; depdes H; eauto. Qed.

  Lemma pos_ext_0_disj p p'
    (SUP: pos_sup (pos_ext_1 p) p' = true)
    :
    pos_sup (pos_ext_0 p) p' = false.
  Proof. revert p' SUP. induction p; i; destruct p'; ss; eauto. Qed.
  
  Lemma pos_ext_1_disj p p'
    (SUP: pos_sup (pos_ext_0 p) p' = true)
    :
    pos_sup (pos_ext_1 p) p' = false.
  Proof. revert p' SUP. induction p; i; destruct p'; ss; eauto. Qed.

  Lemma pos_sup_cases u k
    (EQ : (k =? u)%positive = false)
    (SUP0 : pos_sup (pos_ext_0 u) k = false)
    (SUP1 : pos_sup (pos_ext_1 u) k = false)
    :
    pos_sup u k = false.
  Proof.
    revert_until u. induction u; i; destruct k; ss; eauto.
  Qed.

End UNIVERSE.

Section WSATS.

  Context `{_W: CtxSL.t}.
  Context `{_W0: @GRA.inG OwnIRA Σ}.
  Context `{_W1: @GRA.inG OwnERA Γ}.
  Context `{_W2: @GRA.inG OwnDRA Γ}.

  Definition OwnI_restR u b : OwnIRA :=
    fun u' n =>
      if (u' =? u)%positive
      then
        (if (lt_dec n b)
         then ε
         else @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None))
      else
        ε.

  Definition OwnI_rest u b := OwnM (OwnI_restR u b)%I.

  Definition empty_worldsR {R: univ_id -> URA.t} eu (r: forall u, R u) :=
    fun u =>
      if (pos_sup eu u)
      then r u
      else ε.

  Definition empty_worlds (eu: univ_id) : iProp :=
    OwnM (empty_worldsR eu (fun _ => Some ⊤ : CoPset.t) : OwnERA)
    ∗
    OwnM (empty_worldsR eu (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA)
    ∗
    OwnM (empty_worldsR eu (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : OwnIRA)
    .

  Definition free_universes := (∃ eu, empty_worlds eu)%I.

  Fixpoint countdown (n: nat) : list nat :=
      match n with 0 => [] | S n' => n' :: countdown n' end.

  Definition wsats u b : iProp := ([∗ list] n ∈ (countdown b), wsat u n)%I.

  Definition free_worlds u b : iProp := OwnI_rest u b.

  Definition world u b E : iProp :=
    wsats u b ∗ OwnE u E ∗ OwnD_auth u ∗ free_universes.
  
  Definition closed_world u b E : iProp :=
    free_worlds u b ∗ world u b E.

  Lemma unfold_wsats u b :
    wsats u (S b) ⊢ (wsat u b ∗ wsats u b)%I.
  Proof. ss. Qed.

  Lemma fold_wsats u b :
    (wsat u b ∗ wsats u b)%I ⊢ wsats u (S b).
  Proof. ss. Qed.

  Lemma free_worlds_nin_ u (b b' : level) (NIN : b < b')
    : free_worlds u b ⊢ free_worlds u b' ∗
                      ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    induction NIN.
    - iIntros "AUTH".
      assert ((OwnI_restR u b) =
              ((OwnI_restR u (S b))
              ⋅
              (maps_to_res u (maps_to_res_dep b (@Auth.black (positive ==> URA.agree (SRFSyn.t b))%ra (fun (i : positive) => None)))))).
      { i. subst. extensionalities u' n. unfold OwnI_restR, maps_to_res, maps_to_res_dep.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (u' =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (u' = u)); ss.
          setoid_rewrite URA.unit_id. eauto.
        }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative (u=u)); ss.
        destruct (excluded_middle_informative (n = b)).
        - subst. des_ifs; try lia.
          unfold eq_rect_r. ss. r_solve.
        - destruct (le_dec n (S b)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      unfold free_worlds, OwnI_rest.
      rewrite H. iDestruct "AUTH" as "[AUTH NEW]".
      iPoseProof (wsat_init with "NEW") as "NEW". iFrame.
      replace (S b - b) with 1 by lia. ss. iFrame.
    - unfold free_worlds in *.
      iIntros "AUTH". iPoseProof (IHNIN with "AUTH") as "[AUTH SAT]". iFrame.
      clear IHNIN.
      assert ((OwnI_restR u m) =
                ((OwnI_restR u (S m))
                   ⋅
                   (maps_to_res u (maps_to_res_dep m (@Auth.black (positive ==> URA.agree (SRFSyn.t m))%ra (fun (i : positive) => None)))))).
      { i. extensionalities u' m'. unfold OwnI_restR, maps_to_res, maps_to_res_dep.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (u' =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (u' = u)); ss.
          setoid_rewrite URA.unit_id. eauto.
        }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative (u=u)); ss.
        destruct (excluded_middle_informative (m' = m)).
        - subst. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec m' (S m)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      unfold OwnI_rest.
      rewrite H. iDestruct "AUTH" as "[AUTH NEW]".
      iPoseProof (wsat_init with "NEW") as "NEW". iFrame.
      replace (S m - b) with ((m - b) + 1) by lia. rewrite seq_app.
      iApply big_sepL_app. iFrame.
      replace (b + (m - b)) with m by lia. ss. iFrame.
  Qed.

  Lemma free_worlds_nin u (b b' : level) (LE : b <= b')
    : free_worlds u b ⊢ free_worlds u b' ∗
                      ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    iIntros "R".
    destruct (le_lt_or_eq _ _ LE); subst; cycle 1.
    - replace (b'-b') with 0 by nia. s. iFrame.
    - iApply free_worlds_nin_; eauto.
  Qed.

  Lemma wsats_unfold u b :
    wsats u b ⊢ ([∗ list] n ∈ (seq 0 b), wsat u n).
  Proof.
    unfold wsats. induction b; ss.
    rewrite IHb. destruct b; eauto.
    replace (S b) with (1 + b) at 2 by nia.
    replace (S b) with (b + 1) at 2 by nia.
    rewrite !seq_app. s.
    iIntros "(W1 & (W2 & W3))". iFrame. ss.
  Qed.

  Lemma wsats_fold u b :
    ([∗ list] n ∈ (seq 0 b), wsat u n) ⊢ wsats u b.
  Proof.
    unfold wsats. induction b; ss.
    rewrite <-IHb. destruct b; eauto.
    replace (S b) with (b + 1) at 1 by nia.
    replace (S b) with (1 + b) at 2 by nia.
    rewrite !seq_app. s.
    iIntros "(W1 & (W2 & W3 & W4))". iFrame.
  Qed.
  
  Lemma wsats_nin u (b b' : level):
    b <= b' -> wsats u b ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n) ⊢ wsats u b'.
  Proof.
    iIntros (LE) "[SALL WSAT]". rewrite ->wsats_unfold, <-wsats_fold.
    replace b' with (b + (b' - b)) at 2 by lia.
    rewrite seq_app. iFrame.
  Qed.

  Lemma wsats_in u (b b' : level):
    b <= b' -> wsats u b' ⊢ wsats u b ∗ ([∗ list] n ∈ (seq b (b' - b)), wsat u n).
  Proof.
    iIntros (LE) "SAT". rewrite ->wsats_unfold, <-wsats_fold.
    replace b' with (b + (b' - b)) at 1 by lia. rewrite (seq_app _ _ 0).
    iDestruct "SAT" as "[SAT K]". iFrame.
  Qed.

  Lemma wsats_allocs u b b':
    b <= b' -> free_worlds u b ∗ wsats u b ⊢ free_worlds u b' ∗ wsats u b'.
  Proof.
    iIntros (LE) "(AUTH & SAT)".
    iPoseProof ((free_worlds_nin _ _ _ LE) with "AUTH") as "(AUTH & NEW)". iFrame.
    iPoseProof ((wsats_nin _ _ _ LE) with "[SAT NEW]") as "SAT". iFrame. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt_gen u n b (IN : n < b) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u ∗ wsats u b ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ OwnD_auth u ∗ ((@SRFSem.t (@SL.domain Σ) α β n p) -∗ wsats u b).
  Proof.
    iIntros "[DA SALL]". iPoseProof (wsats_unfold with "SALL") as "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iPoseProof (wsat_OwnI_alloc_gen with "[DA WSAT]") as ">(RES & DA & WSAT)".
    { apply INF. } { iFrame. }
    iFrame. iModIntro. iIntros "P".
    iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL".
    iApply wsats_fold. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt u n b (IN : n < b) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u ∗ wsats u b ∗ ⟦p⟧ ⊢
        |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ OwnD_auth u ∗ wsats u b.
  Proof.
    iIntros "(D & W & P)".
    iMod (wsats_OwnI_alloc_lt_gen with "[D W]") as "(I & D & W)"; eauto. iFrame.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen u b n (GE : b <= n) p φ  
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : free_worlds u b ∗ OwnD_auth u ∗ wsats u b ⊢ 
        |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
              ∗ free_worlds u (S n) ∗ OwnD_auth u ∗ ((@SRFSem.t (@SL.domain Σ) α β n p) -∗ wsats u (S n))).
  Proof.
    iIntros "(AUTH & D & WSAT)".
    iPoseProof ((wsats_allocs u b (S n)) with "[AUTH WSAT]") as "[AUTH WSAT]". lia. iFrame.
    iMod ((wsats_OwnI_alloc_lt_gen u n (S n)) with "[D WSAT]") as "[RES WSAT]". auto. eauto. iFrame.
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge u b n (GE : b <= n) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : free_worlds u b ∗ OwnD_auth u ∗ wsats u b ∗ ⟦p⟧ ⊢
        |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
                ∗ free_worlds u (S n) ∗ OwnD_auth u ∗ wsats u (S n)).
  Proof.
    iIntros "(A & D & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[A D W]") as "(I & A & D & W)".
    1,2: eauto. iFrame.
    iFrame. iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma free_worlds_OwnI_le u b n i p :
    OwnI u n i p ∗ free_worlds u b ⊢ ⌜n < b⌝.
  Proof.
    iIntros "(I & AUTH)".
    unfold OwnI, free_worlds, OwnI_rest.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    unfold OwnI_restR, OwnIR, maps_to_res, maps_to_res_dep in WF.
    unfold URA.add in WF. unseal "ra". ss.
    apply (pw_lookup_wf _ u) in WF. ss.
    unfold URA.add in WF. unseal "ra". ss.
    apply (pwd_lookup_wf _ n) in WF. ss.
    destruct (u =? u)%positive eqn:EQ; cycle 1.
    { apply Pos.eqb_neq in EQ. ss. }
    des_ifs.
    exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
    unfold maps_to_res in WF. apply Auth.auth_included in WF. rename WF into EXTENDS.
    apply pw_extends in EXTENDS. specialize (EXTENDS i). des_ifs.
    clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
    ss. des_ifs.
  Qed.

  Lemma wsats_OwnI_open u b n i p:
    n < b -> OwnI u n i p ∗ wsats u b ∗ OwnE u {[i]} ⊢ |==> (@SRFSem.t (@SL.domain Σ) α β n p) ∗ wsats u b ∗ OwnD u {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & EN)".
    unfold OwnI. iPoseProof (wsats_unfold with "SAT") as "SAT".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    ss. iMod (wsat_OwnI_open with "[I WSAT EN]") as "[P [WSAT DN]]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame. iApply wsats_fold. eauto.
  Qed.

  Lemma wsats_OwnI_close u b n i p:
    n < b -> OwnI u n i p ∗ wsats u b ∗ ⟦p⟧ ∗ OwnD u {[i]} ⊢ |==> wsats u b ∗ OwnE u {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & P & DIS)".
    iPoseProof (wsats_unfold with "SAT") as "SAT".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iMod (wsat_OwnI_close with "[I WSAT P DIS]") as "[WSAT EN]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame. iApply wsats_fold. eauto.
  Qed.

  Lemma empty_worlds_split eu:
    empty_worlds eu ⊢ free_worlds eu 0 ∗ wsats eu 0 ∗ OwnE eu ⊤ ∗ OwnD_auth eu ∗ empty_worlds (pos_ext_0 eu) ∗ empty_worlds (pos_ext_1 eu).
  Proof.
    assert (ERA: URA.extends
              ((OwnER eu ⊤) ⋅
               (empty_worldsR (pos_ext_0 eu) (fun _ => Some ⊤ : CoPset.t)) ⋅
               (empty_worldsR (pos_ext_1 eu) (fun _ => Some ⊤ : CoPset.t)))
              (empty_worldsR eu (fun _ => Some ⊤ : CoPset.t) : OwnERA)).
    { unfold empty_worldsR, OwnER, maps_to_res.
      exists ε. ur. extensionalities k.
      destruct (excluded_middle_informative _).
      { subst. 
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto; r_solve.
      eapply Pos.eqb_neq; eauto.
    }

    assert (DRA: URA.extends
              ((OwnD_authR eu ∅) ⋅
               (empty_worldsR (pos_ext_0 eu) (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA) ⋅
               (empty_worldsR (pos_ext_1 eu) (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA))
              (empty_worldsR eu (fun _ => Auth.black (Some ∅ : Gset.t)) : OwnDRA)).
    { unfold empty_worldsR, OwnD_authR, maps_to_res.
      exists ε. ur. extensionalities k.
      destruct (excluded_middle_informative _).
      { subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto; r_solve.
      eapply Pos.eqb_neq; eauto.
    }

    assert (IRA: URA.extends
              ((OwnI_restR eu 0) ⋅
               (empty_worldsR (pos_ext_0 eu) (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : OwnIRA) ⋅
               (empty_worldsR (pos_ext_1 eu) (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : OwnIRA))
              (empty_worldsR eu (fun _ => (fun n => @Auth.black (_ ==> URA.agree (SRFSyn.t n))%ra (fun _ => None)) : URA.pointwise_dep _) : OwnIRA)).
    { unfold empty_worldsR, OwnI_restR.
      exists ε. ur. ur. extensionalities k n.
      destruct (k =? eu)%positive eqn: EQ.
      { apply Pos.eqb_eq in EQ. subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        repeat setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. repeat setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. repeat setoid_rewrite URA.unit_id. rewrite URA.add_comm.
        setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto.
      repeat setoid_rewrite URA.unit_id. r_solve.
    }

    iIntros "(ERA & DRA & IRA)".
    iPoseProof ((OwnM_extends ERA) with "ERA") as "[[NE E1] E2]".
    iPoseProof ((OwnM_extends DRA) with "DRA") as "[[ND D1] D2]".
    iPoseProof ((OwnM_extends IRA) with "IRA") as "[[NI I1] I2]".
    unfold wsats. s. iFrame.
    iExists ∅. eauto.
  Qed.
  
  Lemma closed_world_init:
    empty_worlds 1 ⊢ closed_world 1 0 ⊤.
  Proof.
    iIntros "E".
    iPoseProof (empty_worlds_split with "E") as "(F & S & E & D & L & _)".
    iFrame. iExists (pos_ext_0 1). iFrame.
  Qed.

  Lemma closed_world_mon {u} b b' (LE: b <= b') E:
    closed_world u b E ⊢ closed_world u b' E.
  Proof.
    unfold closed_world, world. iIntros "(F & W & E & R)". iFrame.
    rewrite ->wsats_unfold, <-wsats_fold.
    replace b' with (b + (b'-b)) by nia.
    rewrite ->seq_app, big_sepL_app. iFrame.
    iPoseProof (free_worlds_nin with "F") as "(FI & W)"; eauto.
    replace (b+(b'-b)) with b' by nia. iFrame.
  Qed.

End WSATS.

Section FANCY_UPDATE.

  Context `{_W: CtxSL.t}.
  Context `{_W0: @GRA.inG OwnIRA Σ}.
  Context `{_W1: @GRA.inG OwnERA Γ}.
  Context `{_W2: @GRA.inG OwnDRA Γ}.

  Definition inv u (n : level) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI u n i p)%I.

  Definition FUpd u b (A : iProp) (E1 E2 : coPset) (P : iProp) : iProp :=
    A ∗ world u b E1 -∗ |==> (A ∗ world u b E2 ∗ P).

  Lemma FUpd_mono u b b' A E1 E2 P :
    (b <= b') -> FUpd u b A E1 E2 P ⊢ FUpd u b' A E1 E2 P.
  Proof.
    unfold FUpd, world.
    iIntros (LE) "FUPD (A & SAT & EN & R)".
    iPoseProof ((wsats_in _ _ _ LE) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[A SAT EN R]") as "(A & (SAT & EN & R) & P)"; iFrame.
    iApply wsats_nin. apply LE. iFrame. eauto.
  Qed.

  Lemma wsats_inv_gen u b E N n p :
    n < b ->
    wsats u b ∗ OwnE u E ∗ OwnD_auth u -∗ |==> inv u n N p ∗ (⟦p⟧ -∗ wsats u b) ∗ OwnE u E ∗ OwnD_auth u.
  Proof.
    iIntros (LT) "(WSAT & EN & DA)".
    iMod (wsats_OwnI_alloc_lt_gen _ _ _ LT p (fun i => i ∈ ↑N) with "[WSAT DA]") as "(I & D & WSAT)".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame.
    - iModIntro. iFrame.
  Qed.

  Lemma FUpd_alloc_gen u b A E N n p :
    n < b -> (inv u n N p -∗ ⟦p⟧) ⊢ FUpd u b A E E (inv u n N p).
  Proof.
    iIntros (LT) "P (A & W & E & D & U)".
    iMod (wsats_inv_gen with "[W E D]") as "(#INV & W & E)"; eauto. iFrame.
    iPoseProof ("P" with "INV") as "P". iPoseProof ("W" with "P") as "W".
    iModIntro. iFrame. eauto.
  Qed.

  Lemma FUpd_alloc u b A E N n p :
    n < b -> ⟦p⟧ ⊢ FUpd u b A E E (inv u n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen. auto. iIntros. iFrame.
  Qed.

  Lemma FUpd_open u b A n N E (LT : n < b) (IN : ↑N ⊆ E) p :
    inv u n N p ⊢
        FUpd u b A E (E∖↑N)
        (⟦p⟧ ∗ ((⟦p⟧) -∗ FUpd u b A (E∖↑N) E emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & EN & D & R)".
    iAssert (OwnE u (E ∖ ↑N) ∗ OwnE u (↑N ∖ {[i]}) ∗ OwnE u {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r.
      { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint.
      { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - iFrame.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsats_OwnI_open _ _ _ i p LT with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame.
    iIntros "P (A & WSAT & EN1 & D1 & R1)".
    iMod (wsats_OwnI_close _ _ _ i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnE_union with "[EN2 EN1]") as "EN". iFrame.
    rewrite difference_union_L. replace (E ∪ ↑N) with E by set_solver. eauto.
  Qed.

  Lemma FUpd_intro u b A E P :
    (|==> P) ⊢ FUpd u b A E E P.
  Proof.
    iIntros ">P H". iModIntro. iFrame. iFrame.
  Qed.

  Lemma FUpd_mask_frame u b A E1 E2 E P :
    E1 ## E ->
    FUpd u b A E1 E2 P ⊢ FUpd u b A (E1 ∪ E) (E2 ∪ E) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & EN & D & R)".
    iPoseProof (OwnE_disjoint _ _ _ D with "EN") as "(EN1 & EN)".
    iPoseProof ("H" with "[A WSAT EN1 D R]") as ">(A & (WSAT & EN1 & D & R) & P)". iFrame.
    iPoseProof (OwnE_union with "[EN EN1]") as "EN". iFrame.
    iModIntro. iFrame.
  Qed.

  Lemma FUpd_intro_mask u b A E1 E2 P :
    E2 ⊆ E1 ->
    FUpd u b A E1 E1 P ⊢ FUpd u b A E1 E2 (FUpd u b A E2 E1 P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & ENS & D & R)".
    iPoseProof ("H" with "[A WSAT ENS D R]") as ">(A & (WSAT & ENS & D & R) & P)". iFrame.
    iModIntro. rewrite (union_difference_L _ _ HE).
    iPoseProof (OwnE_disjoint with "ENS") as "(ENS & EN)".
    { set_solver. }    
    iFrame. iIntros "(A & WSAT & ENS & D & R)". iModIntro. iFrame.
    iApply OwnE_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono u b A E1 E2 P :
    E1 ⊆ E2 ->
    FUpd u b A E1 E1 P ⊢ FUpd u b A E2 E2 P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame. set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  (* Multiverse operations *)
  
  Theorem FUpd_spawn_world u b A E:
    ⊢ FUpd u b A E E (∃ v, closed_world v 0 ⊤).
  Proof.
    unfold FUpd, closed_world, world, free_universes, wsats. s.
    iIntros "(A & S & E & D & R)". iDestruct "R" as (eu) "EW".
    iPoseProof (empty_worlds_split with "EW") as "(EW & FA & E' & D' & L' & R')".
    iFrame. iSplitL "L'"; eauto.
    iExists eu. iFrame. eauto.
  Qed.

  Lemma FUpd_send_iprop u b A E u0 b0 E0 N n p
    (LT: n < b0)
    :
    ⟦p⟧ ∗ closed_world u0 b0 E0
    ⊢
    FUpd u b A E E (inv u0 n N p ∗ closed_world u0 b0 E0).
  Proof.
    iIntros "(P & F0 & S0 & E0 & D0 & R0) (A & S & E & D & R)".
    iPoseProof (FUpd_alloc with "P") as "Upd"; eauto.
    iMod ("Upd" with "[A S0 E0 D0 R0]") as "(A & (S0 & E0 & D9 & R0) & I0)".
    - iFrame; iAssumption.
    - iFrame; eauto.
  Qed.

  Lemma FUpd_receive_iprop u b A E u0 b0 E0 N n p
    (LT: n < b0)
    (IN: ↑N ⊆ E0)
    :
    inv u0 n N p ∗ closed_world u0 b0 E0
    ⊢
    FUpd u b A E E (⟦p⟧ ∗ closed_world u0 b0 (E0 ∖↑N)).
  Proof.
    iIntros "(I & F0 & S0 & E0 & D0 & R0) (A & S & E & D & R)".
    iPoseProof (FUpd_open with "I") as "Upd"; eauto.
    iMod ("Upd" with "[A S0 E0 D0 R0]") as "(A & (S0 & E0 & D0 & R0) & P & _)".
    - iFrame; iAssumption.
    - iFrame; eauto.
  Qed.
  
  Global Instance from_modal_FUpd u b A E P :
    FromModal True modality_id (FUpd u b A E E P) (FUpd u b A E E P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general u b A E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd u b A E1 E2 P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN & D & R)". iModIntro. iFrame.
    iPoseProof ((OwnE_subset _ _ _ HE) with "EN") as "(EN1 & _)". eauto.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask u b A E1 E2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd u b A E1 E2 P) (FUpd u b A E1 E2 P) P | 100.
  Proof.
    intros [].
  Qed.

  Global Instance elim_modal_bupd_FUpd p u b A E1 E2 P Q :
    ElimModal True p false (|==> P) P (FUpd u b A E1 E2 Q) (FUpd u b A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "(>P & K) I". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd u p b b' A E1 E2 E3 P Q :
    ElimModal (b <= b') p false (FUpd u b A E1 E2 P) P (FUpd u b' A E1 E3 Q) (FUpd u b' A E2 E3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LT) "(P & K) I". inv LT.
    - rewrite /FUpd.
      iMod ("P" with "I") as "(A & (WSAT & EN & R) & P)". iApply ("K" with "P"). iFrame.
    - iPoseProof (FUpd_mono _ b (S m) with "P") as "P". lia.
      rewrite /FUpd.
      iMod ("P" with "I") as "(A & (WSAT & EN & R) & P)". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p u b A E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (FUpd u b A E0 E1 P)
              P
              (FUpd u b A E2 E3 Q)
              (FUpd u b A (E1 ∪ (E2 ∖ E0)) (E3) Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iPoseProof (FUpd_mask_frame _ _ _ _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iPoseProof ("K" with "M") as "M". iFrame.
  Qed.

  Global Instance elim_acc_FUpd
         {X : Type} u b A E1 E2 E (γ δ : X -> iProp) (mγ : X -> option iProp) (Q : iProp) :
    ElimAcc True (FUpd u b A E1 E2) (FUpd u b A E2 E1) γ δ mγ (FUpd u b A E1 E Q)
      (fun x : X => ((FUpd u b A E2 E2 (δ x)) ∗ (mγ x -∗? FUpd u b A E1 E Q))%I).
  Proof.
    iIntros (_) "Hinner >[% [Hα Hclose]]".
    iPoseProof ("Hinner" with "Hα") as "[>Hβ Hfin]".
    iPoseProof ("Hclose" with "Hβ") as ">Hγ".
    iApply "Hfin". iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv u b A E n N p :
    IntoAcc (inv u n N p) (n < b /\ (↑N) ⊆ E) True
            (FUpd u b A E (E ∖ ↑N))
            (FUpd u b A (E ∖ ↑N) E)
            (fun _ : () => ⟦p⟧) (fun _ : () => ⟦p⟧) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  Global Instance elim_modal_iupd_FUpd p u b A E1 E2 P Q :
    ElimModal True p false (#=(A)=> P) P (FUpd u b A E1 E2 Q) (FUpd u b A E1 E2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] [A I]".
    iMod ("P" with "A") as "[A P]". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance into_acc_FUpd_world u b A E n N p :
    IntoAcc (inv u n N p) (n < b /\ (↑N) ⊆ E) True
            (FUpd u b A E (E ∖ ↑N))
            (FUpd u b A (E ∖ ↑N) E)
            (fun _ : () => ⟦p⟧) (fun _ : () => ⟦p⟧) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  (* TODO:
     Needs to register the fancy update rules for multivere operations.
  *)
  
End FANCY_UPDATE.

Global Opaque FUpd.

(* Goal (nroot .@ "gil") ## (nroot .@ "hur"). *)
(* eauto with solve_ndisj. *)
