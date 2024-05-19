From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Require Import Coqlib PCM PCMAux IProp IPM.
Require Import Coq.Logic.ClassicalEpsilon.

Local Notation universe := positive.
Local Notation level := nat.
  
Section INDEXED_INVARIANT_SET.

  Context `{Σ : GRA.t}.

  Class IInvSet (Vars : level -> Type) :=
    { prop : forall (i : level), (Vars i) -> iProp }.

  Definition InvSetRA (Vars : level -> Type) (n : level) : URA.t :=
    (Auth.t (positive ==> URA.agree (Vars n)))%ra.

  Definition OwnIsRA (Vars : level -> Type) : URA.t :=
    URA.pointwise universe (@URA.pointwise_dep level (InvSetRA Vars)).

  Definition OwnEsRA : URA.t :=
    URA.pointwise universe (URA.pointwise level CoPset.t).
  
  Definition OwnDsRA : URA.t :=
    URA.pointwise universe (URA.pointwise level (Auth.t Gset.t)).

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnI {Vars} `{@GRA.inG (OwnIsRA Vars) Σ} (u: universe) (n : level) (i : positive) (p : Vars n) :=
    OwnM (maps_to_res u (@maps_to_res_dep level (@InvSetRA Vars)
          n (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p))))) : OwnIsRA Vars).

  Definition OwnE `{@GRA.inG OwnEsRA Σ} (u: universe) (n : level) (E : coPset) :=
    OwnM (maps_to_res u (@maps_to_res level CoPset.t n (Some E)) : OwnEsRA).

  Definition OwnD `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level) (D: gset positive) :=
    OwnM (maps_to_res u (@maps_to_res level (Auth.t Gset.t) n (Auth.white (Some D: Gset.t))) : OwnDsRA).

  Definition OwnD_auth_black `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level) (D: gset positive) : OwnDsRA :=
    maps_to_res u (@maps_to_res level (Auth.t Gset.t) n (Auth.black (Some D : Gset.t))).

  Definition OwnD_auth `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level): iProp :=
    (∃ D, OwnM (OwnD_auth_black u n D))%I.

  Lemma OwnE_level_diff `{@GRA.inG OwnEsRA Σ} u n1 n2 (E : coPset) :
    (E <> ∅) -> OwnE u n1 E ∗ OwnE u n2 E ⊢ ⌜n1 <> n2⌝.
  Proof.
    intros NEMP.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. intros EQ. subst n2.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. specialize (WF u).
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. specialize (WF n1).
    unfold maps_to_res in WF. des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
  Qed.

  Lemma OwnE_exploit `{@GRA.inG OwnEsRA Σ} u n (E1 E2 : coPset) :
    OwnE u n E1 ∗ OwnE u n E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. specialize (WF u).
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. specialize (WF n).
    unfold maps_to_res in WF. des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss; des_ifs.
  Qed.

  Lemma OwnE_union `{@GRA.inG OwnEsRA Σ} u n (E1 E2 : coPset) :
    OwnE u n E1 ∗ OwnE u n E2 ⊢ OwnE u n (E1 ∪ E2).
  Proof.
    iIntros "H". iPoseProof (OwnE_exploit with "H") as "%D".
    iRevert "H". iApply from_sep. eapply from_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. ss. unseal "ra".
    extensionalities u' n'. des_ifs; ss.
    - repeat (unfold URA.add; unseal "ra"; ss; des_ifs).
    - unfold URA.add. unseal "ra". ss. des_ifs. r_solve.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG OwnEsRA Σ} u n (E1 E2 : coPset) :
    E1 ## E2 -> OwnE u n (E1 ∪ E2) ⊢ OwnE u n E1 ∗ OwnE u n E2.
  Proof.
    i. unfold OwnE.
    iApply into_sep. eapply into_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. ss. unseal "ra".
    extensionalities u' n'. des_ifs.
    - repeat (unfold URA.add; unseal "ra"; ss; des_ifs).
    - unfold URA.add. unseal "ra". ss. des_ifs. r_solve.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_subset `{@GRA.inG OwnEsRA Σ} u n (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE u n E2 ⊢ OwnE u n E1 ∗ (OwnE u n E1 -∗ OwnE u n E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply leibniz_equiv. eapply union_difference. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent {Vars} `{@GRA.inG (OwnIsRA Vars) Σ}
    u n i p : Persistent (OwnI u n i p).
  Proof.
    unfold OwnI.
    remember (@maps_to_res_dep level (InvSetRA Vars) n (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H _ with "H") as "#HP". iModIntro.
    replace (maps_to_res u r) with (URA.core (maps_to_res u r)) at 2. auto.
    subst. unfold maps_to_res_dep, maps_to_res. ss. extensionalities u' n'. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{Vars : level -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA Vars) Σ}.

  Variable u : universe.
  Variable n : level.
  Local Notation Var := (Vars n).

  Definition inv_auth_black (I : gmap positive Var) : OwnIsRA Vars :=
    maps_to_res u (
    @maps_to_res_dep level _
                     n (@Auth.black (positive ==> URA.agree Var)%ra
                                    (fun (i : positive) => Some <$> (I !! i)))).

  Definition inv_auth (I : gmap positive Var) := OwnM (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD u n {[i]} ∨ OwnE u n {[i]})%I.

  Definition wsat : iProp := (OwnD_auth u n ∗ ∃ I, inv_auth I ∗ inv_satall I)%I.

  Lemma alloc_name φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u n ⊢ |==> OwnD_auth u n ∗ ∃ i, ⌜φ i⌝ ∧ OwnD u n {[i]}.
  Proof.
    iIntros "[% DA]". specialize (INF (fun _ => Some D) n). ss. des.
    assert (@URA.updatable
              OwnDsRA
              (maps_to_res u (maps_to_res n (Auth.black (Some D : Gset.t))))
              ((maps_to_res u (maps_to_res n (Auth.black (Some (D ∪ {[i]}) : Gset.t))))
                 ⋅
                 (maps_to_res u (maps_to_res n (Auth.white (Some {[i]} : Gset.t)))))) as UPD.
    { rewrite !maps_to_res_add. do 2 apply maps_to_res_updatable.
      ii. ur in H3. des_ifs. des. rewrite URA.unit_idl in H3.
      unfold URA.extends in H3. des. ur in H3.
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
    : wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ (prop n p -∗ wsat).
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
              (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I !! i)))): OwnIsRA Vars)
              ((maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I' !! i)))): OwnIsRA Vars)
               ⋅
               (maps_to_res u (maps_to_res_dep n (Auth.white (@maps_to_res _ (URA.agree Var) i (Some (Some p))))): OwnIsRA Vars))).
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
    unfold inv_auth, inv_satall.
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iIntros "P". unfold wsat. iFrame. iExists I'. iFrame.
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
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ wsat.
  Proof.
    iIntros "[W P]".
    iMod (wsat_OwnI_alloc_gen with "W") as "[I W]". eauto.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI u n i p ∗ wsat ∗ OwnE u n {[i]} ⊢ |==> prop n p ∗ wsat ∗ OwnD u n {[i]}.
  Proof.
    iIntros "(I & [DA [% [AUTH SAT]]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black in WF.
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
         exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
         specialize (WF u). unfold URA.wf, URA.add in WF. unseal "ra". ss.
         specialize (WF n). des_ifs. unfold URA.wf, URA.add in WF. unseal "ra".
         ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI u n i p ∗ wsat ∗ prop n p ∗ OwnD u n {[i]} ⊢ |==> wsat ∗ OwnE u n {[i]}.
  Proof.
    iIntros "(I & [DA [% [AUTH SAT]]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black in WF.
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
      exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
      specialize (WF u). unfold URA.wf, URA.add in WF. unseal "ra". ss.
      specialize (WF n). des_ifs.
      unfold URA.wf, URA.add in WF. unseal "ra". ss.
      ur in WF. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (maps_to_res u (maps_to_res n (Auth.black (Some ∅ : Gset.t))) : OwnDsRA)
    ∗
    OwnM (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun (i : positive) => None))) : OwnIsRA _)
    ⊢ wsat.
  Proof.
    iIntros "[H1 H2]". iSplitL "H1".
    { iExists ∅. iFrame. }
    { iExists ∅. iFrame. unfold inv_satall. iApply big_sepM_empty. ss. }
  Qed.

End WORLD_SATISFACTION.

Section POSITIVE_AUX.

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
  
End POSITIVE_AUX.

Section WSATS.

  Context `{Σ : GRA.t}.
  Context `{Vars : level -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA Vars) Σ}.

  Definition OwnDs_auth_black (u: universe) (n : level) : OwnDsRA :=
    (fun u' n' =>
       if (u' =? u)%positive
       then
         (if (lt_dec n' n)
          then ε
          else Auth.black (Some ∅ : Gset.t))
       else
         (if (pos_sup u u')
          then Auth.black (Some ∅ : Gset.t)
          else ε)).

  Definition OwnIs_auth_black u n : OwnIsRA Vars :=
    (fun u' n' =>
       if (u' =? u)%positive
       then
         (if (lt_dec n' n)
          then ε
          else @Auth.black (positive ==> URA.agree (Vars n'))%ra (fun _ => None))
       else
         (if (pos_sup u u')
          then @Auth.black (positive ==> URA.agree (Vars n'))%ra (fun _ => None)
          else ε)).

  Definition wsats_auth u n :=
    OwnM (OwnDs_auth_black u n) ** OwnM (OwnIs_auth_black u n).

  Definition wsats u n : iProp :=
    ([∗ list] n' ∈ (seq 0 n), wsat u n')%I.

  Lemma unfold_wsats u n :
    wsats u (S n) ⊢ (wsats u n ∗ wsat u n)%I.
  Proof.
    iIntros "A". unfold wsats. replace (seq 0 (S n)) with (seq 0 n ++ [n]).
    2:{ rewrite seq_S. ss. }
    iPoseProof (big_sepL_app with "A") as "[A [B C]]". ss. iFrame.
  Qed.

  Lemma fold_wsats u n :
    (wsats u n ∗ wsat u n)%I ⊢ wsats u (S n).
  Proof.
    iIntros "A". unfold wsats. replace (seq 0 (S n)) with (seq 0 n ++ [n]).
    2:{ rewrite seq_S. ss. }
    iApply big_sepL_app. ss. iDestruct "A" as "[A B]". iFrame.
  Qed.

  Lemma wsats_init_zero :
    OwnM ((fun u n => Auth.black (Some ∅ : Gset.t)) : OwnDsRA)
    **
    OwnM ((fun u n => @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)) : OwnIsRA Vars)
    ⊢ wsats_auth 1 0 ∗ wsats 1 0.
  Proof.
    iIntros "H". unfold wsats_auth, wsats. ss.
    iSplitL; eauto. eapply eq_ind; [iApply "H"|].
    f_equal; f_equal; extensionalities u n;
      unfold OwnDs_auth_black, OwnIs_auth_black; destruct (u =? 1)%positive; ss.
  Qed.

  Lemma wsats_auth_nin u (n n' : level) (NIN : n < n')
    : wsats_auth u n ⊢ wsats_auth u n' ∗
                       ([∗ list] m ∈ (seq n (n' - n)), wsat u m).
  Proof.
    induction NIN.
    - iIntros "[DA AUTH]".
      assert ((OwnIs_auth_black u n) =
              ((OwnIs_auth_black u (S n))
              ⋅
              (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (Vars n))%ra (fun (i : positive) => None)))))).
      { subst. extensionalities u' n'. unfold OwnIs_auth_black, maps_to_res, maps_to_res_dep.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (u' =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (u' = u)); ss.
          setoid_rewrite URA.unit_id. eauto.
        }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative (u=u)); ss.
        destruct (excluded_middle_informative (n' = n)).
        - subst. des_ifs; try lia.
          unfold eq_rect_r. ss. r_solve.
        - destruct (le_dec n' (S n)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      assert ((OwnDs_auth_black u n) =
              ((OwnDs_auth_black u (S n))
              ⋅
              (maps_to_res u (maps_to_res n (Auth.black (Some ∅ : Gset.t)))))).
      { subst. extensionalities u' n'. unfold OwnDs_auth_black, maps_to_res.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (u' =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (u' = u)); ss.
          setoid_rewrite URA.unit_id. eauto.
        }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative (u=u)); ss.
        destruct (excluded_middle_informative (n' = n)).
        - subst n'. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec n' (S n)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      unfold wsats_auth. rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW". iFrame.
      replace (S n - n) with 1 by lia. ss. iFrame.
    - unfold wsats_auth in *.
      iIntros "[DA AUTH]". iPoseProof (IHNIN with "[DA AUTH]") as "[[DA AUTH] SAT]". iFrame.
      clear IHNIN.
      assert ((OwnIs_auth_black u m) =
                ((OwnIs_auth_black u (S m))
                   ⋅
                   (maps_to_res u (maps_to_res_dep m (@Auth.black (positive ==> URA.agree (Vars m))%ra (fun (i : positive) => None)))))).
      { extensionalities u' m'. unfold OwnIs_auth_black, maps_to_res, maps_to_res_dep.
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
      assert ((OwnDs_auth_black u m) =
              ((OwnDs_auth_black u (S m))
              ⋅
              (maps_to_res u (maps_to_res m (Auth.black (Some ∅ : Gset.t)))))).
      { extensionalities u' m'. unfold OwnDs_auth_black, maps_to_res.
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
      rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW". iFrame.
      iFrame. replace (S m - n) with ((m - n) + 1) by lia. rewrite seq_app.
      iApply big_sepL_app. iFrame.
      replace (n + (m - n)) with m by lia. ss. iFrame.
  Qed.

  Lemma wsats_nin u (n n' : level):
    n < n' -> wsats u n ∗ ([∗ list] m ∈ (seq n (n' - n)), wsat u m) ⊢ wsats u n'.
  Proof.
    iIntros (LT) "[SALL WSAT]". unfold wsats.
    replace n' with (n + (n' - n)) at 2 by lia. rewrite seq_app. iFrame.
  Qed.

  Lemma wsats_in u (n n' : level):
    n < n' -> wsats u n' ⊢ wsats u n ∗ ([∗ list] m ∈ (seq n (n' - n)), wsat u m).
  Proof.
    iIntros (LT) "SAT". unfold wsats.
    replace n' with (n + (n' - n)) at 1 by lia. rewrite (seq_app _ _ 0).
    iPoseProof (big_sepL_app with "SAT") as "[SAT K]". iFrame.
  Qed.

  Lemma wsats_allocs u n n':
    n < n' -> wsats_auth u n ∗ wsats u n ⊢ wsats_auth u n' ∗ wsats u n'.
  Proof.
    iIntros (LT) "(AUTH & SAT)".
    iPoseProof ((wsats_auth_nin _ _ _ LT) with "AUTH") as "(AUTH & NEW)". iFrame.
    iPoseProof ((wsats_nin _ _ _ LT) with "[SAT NEW]") as "SAT". iFrame. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt_gen u n n' (LT : n < n') p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats u n' ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ (prop n p -∗ wsats u n').
  Proof.
    iIntros "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iPoseProof (wsat_OwnI_alloc_gen with "WSAT") as ">[RES WSAT]". apply INF. iFrame.
    iModIntro. iIntros "P". iFrame. iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt u n n' (LT : n < n') p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats u n' ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI u n i p) ∗ wsats u n'.
  Proof.
    iIntros "[W P]". iMod (wsats_OwnI_alloc_lt_gen with "W") as "[I W]". 1,2: eauto.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen u n' n (GE : n' <= n) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats_auth u n' ∗ wsats u n' ⊢
                 |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
                         ∗ wsats_auth u (S n) ∗ (prop n p -∗ wsats u (S n))).
  Proof.
    iIntros "(AUTH & WSAT)".
    iPoseProof ((wsats_allocs u n' (S n)) with "[AUTH WSAT]") as "[AUTH WSAT]". lia. iFrame.
    iMod ((wsats_OwnI_alloc_lt_gen u n (S n)) with "WSAT") as "[RES WSAT]". auto. eauto.
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge u n' n (GE : n' <= n) p φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats_auth u n' ∗ wsats u n' ∗ prop n p
                 ⊢ |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
                           ∗ wsats_auth u (S n) ∗ wsats u (S n)).
  Proof.
    iIntros "(A & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[A W]") as "(I & A & W)".
    1,2: eauto.
    iFrame. iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_auth_OwnI_le u n n' i p :
    OwnI u n i p ∗ wsats_auth u n' ⊢ ⌜n < n'⌝.
  Proof.
    iIntros "(I & (_ & AUTH))".
    unfold OwnI, wsats_auth.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    unfold OwnIs_auth_black, maps_to_res, maps_to_res_dep in WF.
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

  Lemma wsats_OwnI_open u n n' i p:
    n < n' -> OwnI u n i p ∗ wsats u n' ∗ OwnE u n {[i]} ⊢ |==> prop n p ∗ wsats u n' ∗ OwnD u n {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & EN)".
    unfold OwnI, wsats.
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    ss. iMod (wsat_OwnI_open with "[I WSAT EN]") as "[P [WSAT DN]]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_close u n n' i p:
    n < n' -> OwnI u n i p ∗ wsats u n' ∗ prop n p ∗ OwnD u n {[i]} ⊢ |==> wsats u n' ∗ OwnE u n {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & P & DIS)".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    apply lookup_seq_lt; eauto.
    iMod (wsat_OwnI_close with "[I WSAT P DIS]") as "[WSAT EN]". iFrame.
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

End WSATS.

Notation coPsets := (gmap level coPset).

Section OWNES.

  Context `{Σ : GRA.t}.
  Context `{@GRA.inG OwnEsRA Σ}.

  Definition OwnE_auth_black u (Es : coPsets) : (universe ==> (level ==> CoPset.t))%ra :=
    fun u' n =>
      if (u' =? u)%positive
      then
        match Es !! n with
        | Some _ => ε
        | None => Some ⊤
        end
      else
        (if (pos_sup u u')
         then Some ⊤
         else ε).

  Definition OwnE_auth u (Es : coPsets) := OwnM (OwnE_auth_black u Es).

  Definition OwnE_satall u (Es : coPsets) := ([∗ map] n ↦ E ∈ Es, OwnE u n E)%I.

  Definition OwnEs u (Es : coPsets) := (OwnE_auth u Es ∗ OwnE_satall u Es)%I.

  Definition OwnEs_top (Es : coPsets) : Prop := map_Forall (fun _ E => ⊤ ⊆ E) Es.

  Lemma OwnEs_init_wf u:
    URA.wf (OwnE_auth_black u ∅).
  Proof.
    unfold OwnE_auth_black. ur. i. ur. i. des_ifs; ur; des_ifs.
  Qed.

  Lemma OwnEs_init u:
    OwnM (OwnE_auth_black u ∅) ⊢ OwnEs u ∅.
  Proof.
    iIntros. unfold OwnEs. iFrame. unfold OwnE_satall. ss.
  Qed.

  Lemma OwnEs_has u Es n E :
    (Es !! n = Some E) -> OwnEs u Es ⊢ OwnEs u (<[n:=E]>Es).
  Proof.
    iIntros (IN) "ES". rewrite insert_id; auto.
  Qed.

  Lemma OwnEs_alloc u Es n:
    (Es !! n = None) -> OwnEs u Es ⊢ |==> OwnEs u (<[n := ⊤]>Es).
  Proof.
    iIntros (NIN) "[AUTH SAT]". unfold OwnE_auth, OwnE_satall.
    remember (<[n := ⊤]> Es) as Es'.
    assert (URA.updatable
              (OwnE_auth_black u Es)
              ((OwnE_auth_black u Es')
               ⋅
               (@maps_to_res _ (_==>_)%ra u (maps_to_res n (Some ⊤))))).
    { do 2 (apply pointwise_updatable; i).
      unfold OwnE_auth_black, maps_to_res.
      do 2 (unfold URA.add; unseal "ra"; ss).
      destruct (a =? u)%positive eqn: EQ; cycle 1.
      { apply Pos.eqb_neq in EQ.
        destruct (excluded_middle_informative (a = u)); ss.
        setoid_rewrite URA.unit_id. reflexivity. }
      apply Pos.eqb_eq in EQ. subst.
      destruct (excluded_middle_informative _); ss.
      destruct (excluded_middle_informative (a0 = n)).
      - subst. des_ifs.
        2:{ exfalso. setoid_rewrite lookup_insert in Heq0. inv Heq0. }
        rewrite URA.unit_idl. reflexivity.
      - rewrite lookup_insert_ne; auto. rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd H0 with "AUTH") as "[AUTH NEW]". clear H0.
    iModIntro. iFrame. unfold OwnE_satall. subst. iApply big_sepM_insert; auto. iFrame.
  Qed.

  Lemma OwnEs_acc_in u Es n E (IN : Es !! n = Some E) :
    OwnEs u Es ⊢ OwnE u n E ∗ OwnEs u (<[n := ∅]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnE_satall.
    iAssert (OwnE u n E ∗ ([∗ map] n0↦E0 ∈ delete n Es, OwnE u n0 E0))%I with "[SAT]" as "[EN SAT]".
    { iApply big_sepM_delete; auto. }
    iPoseProof (OwnM_persistently with "EN") as "#EN2". ss.
    iAssert ([∗ map] n0↦E0 ∈ <[n := ∅]>Es, OwnE u n0 E0)%I with "[SAT]" as "SAT".
    { iApply big_sepM_insert_delete. iFrame. iApply (OwnM_extends with "EN2").
      unfold maps_to_res. clear. exists ε. rewrite URA.unit_id.
      extensionalities u' n'. des_ifs.
    }
    iFrame. iClear "EN2".
    iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id.
    extensionalities u' n'.
    unfold OwnE_auth_black. destruct (Nat.eqb_spec n' n).
    - subst. rewrite lookup_insert. rewrite IN. auto.
    - rewrite lookup_insert_ne; auto.
  Qed.

  Lemma OwnEs_acc_new u Es n (NIN : Es !! n = None) :
    OwnEs u Es ⊢ |==> OwnE u n ⊤ ∗ OwnEs u (<[n := ∅]>Es).
  Proof.
    iIntros "ENS". iMod (OwnEs_alloc with "ENS") as "ENS". eauto.
    iModIntro.
    assert (<[n:=∅]> Es = <[n:=∅]> (<[n:=⊤]> Es)).
    { rewrite insert_insert. auto. }
    rewrite H0. iApply OwnEs_acc_in.
    - rewrite lookup_insert. auto.
    - iFrame.
  Qed.

  Lemma OwnEs_union u Es n E1 E2 :
    OwnEs u (<[n:=E1]> Es) ∗ OwnE u n E2 ⊢ OwnEs u (<[n:=E1 ∪ E2]> Es).
  Proof.
    iIntros "[[AUTH SAT] EN]". unfold OwnEs. iSplitL "AUTH".
    { iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id.
      extensionalities u' n'.
      unfold OwnE_auth_black. destruct (Nat.eqb_spec n' n).
      - subst. rewrite ! lookup_insert. auto.
      - rewrite ! lookup_insert_ne; auto.
    }
    iApply big_sepM_insert_delete.
    iAssert (OwnE u n E1 ∗ (OwnE_satall u (delete n (<[n:=E1]> Es))))%I with "[SAT]" as "[EN' SAT]".
    { iApply big_sepM_delete.
      - apply lookup_insert.
      - iFrame.
    }
    assert ((delete n (<[n:=E1]> Es)) = delete n Es).
    { rewrite delete_insert_delete. auto. }
    rewrite H0. iFrame. iApply OwnE_union. iFrame.
  Qed.

  Lemma OwnEs_free u Es n :
    Es !! n = None -> OwnEs u (<[n:=⊤]>Es) ⊢ |==> OwnEs u Es.
  Proof.
    iIntros (NIN) "ENS". iPoseProof (OwnEs_acc_in with "ENS") as "[EN ENS]". apply lookup_insert.
    rewrite insert_insert. unfold OwnEs. iDestruct "ENS" as "[AUTH SAT]".
    iSplitL "EN AUTH".
    - unfold OwnE_auth, OwnE. iCombine "EN AUTH" as "AUTH".
      assert (URA.updatable
                ((maps_to_res u (@maps_to_res level CoPset.t n (Some ⊤)))
                 ⋅
                 OwnE_auth_black u (<[n:=∅]> Es))
                (OwnE_auth_black u Es)).
      { do 2 (apply pointwise_updatable; i).
        unfold OwnE_auth_black, maps_to_res.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (a =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (a = u)); ss.
          setoid_rewrite URA.unit_idl. reflexivity. }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative _); ss.
        destruct (excluded_middle_informative (a0 = n)).
        - subst. rewrite lookup_insert. rewrite NIN.
          rewrite URA.unit_id. reflexivity.
        - rewrite lookup_insert_ne; auto. rewrite URA.unit_idl. reflexivity.
      }
      iMod (OwnM_Upd H0 with "AUTH") as "AUTH". iModIntro. iFrame.
    - unfold OwnE_satall. iModIntro.
      iPoseProof (big_sepM_insert with "SAT") as "[_ SAT]"; auto.
  Qed.

  Lemma OwnEs_update_one u Es n E1 E2 :
    OwnEs u (<[n:=E1]>Es) ⊢ (OwnE u n E1 -∗ OwnE u n E2) -∗ OwnEs u (<[n:=E2]>Es).
  Proof.
    iIntros "E IMPL". iPoseProof (OwnEs_acc_in with "E") as "[E K]".
    { apply lookup_insert. }
    iPoseProof ("IMPL" with "E") as "E".
    iEval (rewrite insert_insert) in "K".
    iPoseProof (OwnEs_union with "[E K]") as "E". iFrame.
    replace (∅ ∪ E2) with E2 by set_solver.
    iFrame.
  Qed.

  Lemma OwnEs_subset u Es n E1 E2 :
    (E1 ⊆ E2) -> OwnEs u (<[n:=E2]>Es) ⊢ OwnEs u (<[n:=E1]>Es).
  Proof.
    iIntros (SUB) "ES". iApply (OwnEs_update_one with "ES").
    iIntros "E". iPoseProof (OwnE_subset with "E") as "[E1 _]". eauto. iFrame.
  Qed.

  Lemma OwnEs_disjoint u Es n E1 E2 :
    E1 ## E2 -> OwnEs u (<[n:=E1 ∪ E2]>Es) ⊢ OwnEs u (<[n:=E1]>Es) ∗ OwnE u n E2.
  Proof.
    iIntros (HE) "ENS". iPoseProof (OwnEs_acc_in with "ENS") as "[EN ENS]".
    { apply lookup_insert. }
    iPoseProof ((OwnE_disjoint _ _ _ _ HE) with "EN") as "[EN1 EN2]".
    iFrame. rewrite insert_insert.
    iApply (OwnEs_update_one with "ENS"). iIntros. iFrame.
  Qed.

  Lemma OwnEs_free_all u Es :
    OwnEs_top Es -> OwnEs u Es ⊢ |==> OwnEs u ∅.
  Proof.
    pattern Es. revert Es. apply map_ind.
    { iIntros (TOP) "ES". ss. }
    iIntros (? ? ? NONE IND TOP) "ES".
    iMod (OwnEs_free with "[ES]") as "ES". eauto.
    { eapply map_Forall_lookup_1 in TOP. 2: apply lookup_insert. iApply OwnEs_subset; eauto. }
    iApply IND. 2: iFrame.
    eapply map_Forall_insert_1_2; eauto.
  Qed.


  Definition lookup_def (Es : coPsets) (n : nat) : coPset := default ⊤ (Es !! n).

  Definition subseteq_def (Es : coPsets) (n : nat) (E : coPset) : Prop :=
    match Es !! n with | Some E' => E ⊆ E' | None => True end.

  Definition insert_def (Es : coPsets) (n : nat) : coPsets :=
    match Es !! n with | Some E => Es | None => <[n:=⊤]> Es end.

  Lemma OwnEs_lookup_def u Es n :
    OwnEs u Es ⊢ |==> OwnEs u (<[n := lookup_def Es n]>Es).
  Proof.
    iIntros "ENS". unfold lookup_def, default. des_ifs; ss.
    - rewrite insert_id; auto.
    - iMod (OwnEs_alloc with "ENS") as "ENS"; eauto.
  Qed.

  Lemma lookup_subseteq_def Es n E :
    E ⊆ (lookup_def Es n) -> subseteq_def Es n E.
  Proof.
    unfold lookup_def,default, subseteq_def. i. des_ifs.
  Qed.

End OWNES.

Notation "M '!?' k" := (lookup_def M k) (at level 20).
Notation "E '⪿' '(' Es ',' n ')'" := (subseteq_def Es n E) (at level 70).

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : level -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA Vars) Σ}.

  Definition inv u (n : level) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI u n i p)%I.

  Definition FUpd u n (A : iProp) (Es1 Es2 : coPsets) (P : iProp) : iProp :=
    A ∗ wsats u n ∗ OwnEs u Es1 -∗ #=> (A ∗ wsats u n ∗ OwnEs u Es2 ∗ P).

  Lemma FUpd_mono u n n' A Es1 Es2 P :
    (n < n') -> FUpd u n A Es1 Es2 P ⊢ FUpd u n' A Es1 Es2 P.
  Proof.
    iIntros (LT) "FUPD (A & SAT & EN)".
    iPoseProof ((wsats_in _ _ _ LT) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[A SAT EN]") as "(A & SAT & EN & P)". iFrame.
    iModIntro. iFrame. iApply wsats_nin. apply LT. iFrame.
  Qed.

  Lemma wsats_inv_gen u n' A Es n N p :
    n < n' ->
    ⊢ A ∗ wsats u n' ∗ OwnEs u Es -∗ #=> (A ∗ (prop n p -∗ wsats u n') ∗ OwnEs u Es ∗ (inv u n N p)).
  Proof.
    iIntros (LT) "(A & WSAT & EN)".
    iMod (wsats_OwnI_alloc_lt_gen _ _ _ LT p (fun i => i ∈ ↑N) with "WSAT") as "[I WSAT]".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame. auto.
  Qed.

  Lemma FUpd_alloc_gen u n' A Es n N p :
    n < n' -> (inv u n N p -∗ prop n p) ⊢ FUpd u n' A Es Es (inv u n N p).
  Proof.
    iIntros (LT) "P (A & WSAT & EN)".
    iMod (wsats_inv_gen with "[A WSAT EN]") as "(A & W & EN & #INV)". eauto.
    iSplitL "A". iApply "A". iFrame.
    iPoseProof ("P" with "INV") as "P". iPoseProof ("W" with "P") as "W". iModIntro. iFrame. auto.
  Qed.

  Lemma FUpd_alloc u n' A Es n N p :
    n < n' -> prop n p ⊢ FUpd u n' A Es Es (inv u n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen. auto. iIntros. iFrame.
  Qed.

  Lemma FUpd_open_aux u n' A Es n N E (LT : n < n') (INE : Es !! n = Some E) (IN : ↑N ⊆ E) p :
    inv u n N p ⊢
        FUpd u n' A Es (<[n := E∖↑N]> Es)
        ((prop n p) ∗ ((prop n p) -∗ FUpd u n' A (<[n := E∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & ENS)".
    iPoseProof ((OwnEs_acc_in _ _ _ _ INE) with "ENS") as "[EN ENS]".
    iAssert (OwnE u n (E ∖ ↑N) ∗ OwnE u n (↑N ∖ {[i]}) ∗ OwnE u n {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
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
    iModIntro. iFrame. iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ E ∖ ↑N) with (E ∖ ↑N). 2: set_solver.
    iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close _ _ _ i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplit; auto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnEs_union with "[EN1 EN2]") as "ENS". iFrame.
    rewrite insert_id. iFrame. rewrite INE. f_equal.
    rewrite difference_union_L. set_solver.
  Qed.

  Lemma FUpd_open u n' A Es n N (LT : n < n') (IN : (↑N) ⪿ (Es, n)) p :
    inv u n N p ⊢
        FUpd u n' A Es
        (<[n := (Es !? n)∖↑N]> Es)
        ((prop n p) ∗ ((prop n p) -∗ FUpd u n' A (<[n := (Es !? n)∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & ENS)".
    unfold lookup_def, subseteq_def in *. destruct (Es !! n) eqn:CASES; ss.
    - iApply FUpd_open_aux; auto. unfold inv; auto. iFrame.
    - iAssert (
          (#=> (A ∗ (wsats u n' ∗ (OwnEs u (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd u n' A (<[n:=⊤ ∖ ↑N]> Es) (<[n:=⊤]>Es) emp))))))
            -∗
            #=> (A ∗ (wsats u n' ∗ (OwnEs u (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd u n' A (<[n:=⊤ ∖ ↑N]> Es) Es emp))))))%I as "K".
      { iIntros ">[A [SAT [ENS [P K]]]]". iModIntro. iFrame. iIntros "P".
        iPoseProof ("K" with "P") as "K". iIntros "[A [SAT ENS]]".
        iPoseProof ("K" with "[A SAT ENS]") as ">[A [SAT [ENS _]]]". iFrame.
        iMod (OwnEs_free with "ENS") as "ENS". auto.
        iModIntro. iFrame.
      }
      iApply "K". iClear "K".
      iMod (OwnEs_alloc _ _ _ CASES with "ENS") as "ENS". remember (<[n:=⊤]> Es) as Es'.
      replace (<[n:=⊤ ∖ ↑N]> Es) with (<[n:=⊤ ∖ ↑N]> Es').
      2:{ subst. rewrite insert_insert. auto. }
      iApply FUpd_open_aux; auto.
      { subst. apply lookup_insert. }
      unfold inv; auto. iFrame.
  Qed.

  Lemma FUpd_intro u n A Es P :
    #=> P ⊢ FUpd u n A Es Es P.
  Proof.
    iIntros "P H". iMod "P". iModIntro. iFrame. iFrame.
  Qed.

  Lemma FUpd_mask_frame_gen u n' A Es1 Es2 n E P :
    (Es1 !? n) ## E ->
    FUpd u n' A Es1 Es2 P ⊢
         FUpd u n' A (<[n := (Es1 !? n) ∪ E]>Es1) (<[n := (Es2 !? n) ∪ E]>Es2) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & ENS)".
    iPoseProof ((OwnEs_acc_in _ _ n) with "ENS") as "[EN ENS]". apply lookup_insert.
    iPoseProof (OwnE_disjoint _ _ _ _ D with "EN") as "[EN1 EN]".
    iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ lookup_def Es1 n) with (lookup_def Es1 n) by set_solver.
    destruct (coPset_equiv_dec E ∅); cycle 1.
    { unfold lookup_def, default in D. des_ifs; ss.
      2:{ exfalso. set_solver. }
      rewrite insert_insert. rewrite (insert_id Es1).
      2:{ unfold lookup_def, default. rewrite Heq. ss. }
      iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
      destruct (Es2 !! n) eqn:CASES.
      2:{ iMod ((OwnEs_acc_new _ _ _ CASES) with "ENS2") as "[EN2 _]".
          iPoseProof (OwnE_exploit with "[EN EN2]") as "%DIS". iFrame.
          set_solver.
      }
      unfold lookup_def. rewrite CASES. ss.
      iPoseProof ((OwnEs_acc_in _ _ _ _ CASES) with "ENS2") as "[EN2 ENS]".
      iPoseProof (OwnE_union with "[EN EN2]") as "EN". iFrame.
      iPoseProof (OwnEs_union with "[ENS EN]") as "ENS". iFrame.
      replace (∅ ∪ (c0 ∪ E)) with (c0 ∪ E) by set_solver.
      iModIntro. iFrame.
    }
    { replace (lookup_def Es1 n ∪ E) with (lookup_def Es1 n) by set_solver.
      replace (lookup_def Es2 n ∪ E) with (lookup_def Es2 n) by set_solver.
      rewrite insert_insert.
      destruct (Es1 !! n) eqn:CASES.
      - rewrite (insert_id Es1).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
      - replace (lookup_def Es1 n) with (⊤ : coPset).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iMod ((OwnEs_free _ _ _ CASES) with "ENS") as "ENS".
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
    }
  Qed.

  Lemma FUpd_mask_frame u n' A Es1 Es2 n E1 E2 E P :
    E1 ## E ->
    FUpd u n' A (<[n:=E1]>Es1) (<[n:=E2]>Es2) P ⊢
         FUpd u n' A (<[n :=E1 ∪ E]>Es1) (<[n :=E2 ∪ E]>Es2) P.
  Proof.
    iIntros (D) "FUPD".
    iPoseProof (FUpd_mask_frame_gen with "FUPD") as "FUPD".
    { unfold lookup_def. rewrite lookup_insert. ss. eauto. }
    unfold lookup_def. rewrite ! lookup_insert. ss. rewrite ! insert_insert. auto.
  Qed.

  Lemma FUpd_intro_mask u n' A Es1 Es2 Es3 n E1 E2 P :
    E2 ⊆ E1 ->
    FUpd u n' A (<[n:=E1]>Es1) (<[n:=E1]>Es2) P ⊢
         FUpd u n' A (<[n:=E1]>Es1) (<[n:=E2]>Es2) (FUpd u n' A (<[n:=E2]>Es3) (<[n:=E1]>Es3) P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & ENS)".
    iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS & P)". iFrame.
    iModIntro.
    rewrite (union_difference_L _ _ HE).
    iPoseProof (OwnEs_disjoint with "ENS") as "[ENS EN]".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & ENS)". iModIntro. iFrame.
    iApply OwnEs_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono u n' A Es1 Es2 n E1 E2 P :
    E1 ⊆ E2 ->
    FUpd u n' A (<[n:=E1]>Es1) (<[n:=E1]>Es2) P ⊢ FUpd u n' A (<[n:=E2]>Es1) (<[n:=E2]>Es2) P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame. set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  Global Instance from_modal_FUpd u n A Es P :
    FromModal True modality_id (FUpd u n A Es Es P) (FUpd u n A Es Es P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed.

  Global Instance from_modal_FUpd_alloc u n' A Es n P :
    FromModal (Es !! n = None) modality_id P (FUpd u n' A Es (<[n:=⊤]>Es) P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)".
    iMod (OwnEs_alloc with "EN") as "EN". eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_free u n' A Es n P :
    FromModal (Es !! n = None) modality_id P (FUpd u n' A (<[n:=⊤]>Es) Es P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)".
    iMod (OwnEs_free with "EN") as "EN". eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general u n' A Es n E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd u n' A (<[n:=E1]>Es) (<[n:=E2]>Es) P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    iPoseProof (OwnEs_acc_in with "EN") as "[EN ENS]". apply lookup_insert.
    iPoseProof ((OwnE_subset _ _ _ _ HE) with "EN") as "[EN1 _]".
    iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". iFrame. rewrite insert_insert.
    replace (∅ ∪ E2) with E2 by set_solver. iFrame.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask u n A Es1 Es2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd u n A Es1 Es2 P) (FUpd u n A Es1 Es2 P) P | 100.
  Proof.
    intros [].
  Qed.

  Global Instance elim_modal_bupd_FUpd p u n A Es1 Es2 P Q :
    ElimModal True p false (|==> P) P (FUpd u n A Es1 Es2 Q) (FUpd u n A Es1 Es2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod "P". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd u p n n' A Es1 Es2 Es3 P Q :
    ElimModal (n <= n') p false (FUpd u n A Es1 Es2 P) P (FUpd u n' A Es1 Es3 Q) (FUpd u n' A Es2 Es3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LT) "[P K] I". inv LT.
    - rewrite /FUpd.
      iMod ("P" with "I") as "(A & WSAT & EN & P)". iApply ("K" with "P"). iFrame.
    - iPoseProof (FUpd_mono _ n (S m) with "P") as "P". lia.
      rewrite /FUpd.
      iMod ("P" with "I") as "(A & WSAT & EN & P)". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p u n' A Es0 Es1 Es2 n E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (FUpd u n' A (<[n:=E0]>Es0) (<[n:=E1]>Es1) P)
              P
              (FUpd u n' A (<[n:=E2]>Es0) (<[n:=E3]>Es2) Q)
              (FUpd u n' A (<[n:=(E1 ∪ (E2 ∖ E0))]>Es1) (<[n:=E3]>Es2) Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iPoseProof (FUpd_mask_frame _ _ _ _ _ _ _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iPoseProof ("K" with "M") as "M". iFrame.
  Qed.

  Global Instance elim_acc_FUpd
         {X : Type} u i A Es1 Es2 Es (α β : X -> iProp) (mγ : X -> option iProp) (Q : iProp) :
    ElimAcc True (FUpd u i A Es1 Es2) (FUpd u i A Es2 Es1) α β mγ (FUpd u i A Es1 Es Q) (fun x : X => ((FUpd u i A Es2 Es2 (β x)) ∗ (mγ x -∗? FUpd u i A Es1 Es Q))%I).
  Proof.
    iIntros (_) "Hinner >[% [Hα Hclose]]".
    iPoseProof ("Hinner" with "Hα") as "[>Hβ Hfin]".
    iPoseProof ("Hclose" with "Hβ") as ">Hγ".
    iApply "Hfin". iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv u n' A Es n N p :
    IntoAcc (inv u n N p) (n < n' /\ (↑N) ⪿ (Es, n)) True
            (FUpd u n' A Es (<[n := Es !? n ∖ ↑N]>Es))
            (FUpd u n' A (<[n := Es !? n ∖ ↑N]>Es) Es)
            (fun _ : () => prop n p) (fun _ : () => prop n p) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  Global Instance elim_modal_iupd_FUpd p u n A Es1 Es2 P Q :
    ElimModal True p false (#=(A)=> P) P (FUpd u n A Es1 Es2 Q) (FUpd u n A Es1 Es2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] [A I]".
    iMod ("P" with "A") as "[A P]". iApply ("K" with "P"). iFrame.
  Qed.

End FANCY_UPDATE.

Global Opaque FUpd.

Section WORLD_SPLIT_MERGE.

  Context `{Σ : GRA.t}.
  Context `{Vars : level -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA Vars) Σ}.

  Definition wclosed u n :=
    wsats_auth u n ** wsats u n ** OwnEs u ∅.

  Definition invE := (namespace * { n & Vars n })%type.

  Definition invE_prop u (e: invE) : iProp :=
    inv u (projT1 (snd e)) (fst e) (projT2 (snd e)).

  Fixpoint inv_disj_from (N: namespace) (invs: list invE) : Prop :=
    match invs with
    | [] => True
    | (N',_)::invs' => N ## N' /\ inv_disj_from N invs'
    end.

  Fixpoint inv_disj (invs: list invE) : Prop :=
    match invs with
    | [] => True
    | (N,_)::invs' => inv_disj_from N invs' /\ inv_disj invs'
    end.

  Section TEST.
    Goal forall i,
      inv_disj [(nroot .@ "gil",i); (nroot .@ "hur", i); (nroot .@ "chung", i)].
    Proof. i. ss. eauto with solve_ndisj. Qed.
  End TEST.

  Definition update_dep {B} (bs: forall n, B n) (n: level) (b: B n): forall n, B n.
    i. destruct (Nat.eq_dec n0 n); subst.
    - exact b.
    - exact (bs n0).
  Defined.

  Lemma update_dep_eq {B} bs n b :
    @update_dep B bs n b n = b.
  Proof.
    unfold update_dep. des_ifs.
    rewrite (UIP _ _ _ e eq_refl). eauto.
  Qed.

  Lemma update_dep_neq {B} bs n b n'
    (NEQ: n <> n')
    :
    @update_dep B bs n b n' = bs n'.
  Proof.
    unfold update_dep. des_ifs.
  Qed.

  Search big_opL.
  
  Lemma big_sepL_seq_exist {B} (unit: forall a, B a) P n sz:
    ([∗ list] a ∈ seq n sz, ∃ b: B a, P a b)
    ⊢ ∃ bs, [∗ list] a ∈ seq n sz, P a (bs a).
  Proof.
    revert n. induction sz; ss; i.    
    { iIntros. iExists unit. eauto. }
    iIntros "[NEW SAT]".
    iDestruct "NEW" as (b) "NEW".
    iPoseProof (IHsz with "SAT") as (bs) "SAT".
    iExists (update_dep bs n b).
    iSplitL "NEW".
    { rewrite update_dep_eq. eauto. }
    erewrite big_opL_ext.
    { iApply "SAT". }
    i. s. rewrite update_dep_neq; eauto.
    eapply lookup_seq in H2. des. lia.
  Qed.
    
  Lemma big_sepL_seq_exist_rev {B} bs P n sz:
    ([∗ list] a ∈ seq n sz, P a (bs a))
    ⊢ [∗ list] a ∈ seq n sz, ∃ b: B a, P a b.
  Proof.
    revert n. induction sz; ss; i.
    iIntros "[NEW H]".
    iPoseProof (IHsz with "H") as "IH". iFrame.
    iExists (bs n). eauto.
  Qed.

  Lemma OwnEs_split u:
    OwnEs u ∅ ⊢ #=> (OwnEs (pos_ext_0 u) ∅ ** OwnEs (pos_ext_1 u) ∅).
  Proof.
    unfold OwnEs, OwnE_auth, OwnE_satall, OwnE.
    rewrite !big_sepM_empty.
    assert (URA.updatable (OwnE_auth_black u ∅)
              ((OwnE_auth_black (pos_ext_0 u) ∅) ⋅ (OwnE_auth_black (pos_ext_1 u) ∅))).
    { do 2 (apply pointwise_updatable; i).
      unfold OwnE_auth_black, maps_to_res.
      do 2 (unfold URA.add; unseal "ra"; ss).
      rewrite lookup_empty.
      destruct (pos_sup (pos_ext_0 u) a) eqn: SUP0.
      { erewrite (pos_sup_trans u _ a); eauto using pos_ext_0_sup_true.
        erewrite pos_ext_1_disj; eauto.
        destruct (a =? pos_ext_1 u)%positive eqn: EQ.
        { apply Pos.eqb_eq in EQ. subst.
          erewrite pos_ext_0_disj in SUP0; ss; eauto using pos_sup_refl. }
        r_solve. des_ifs.
      }
      destruct (pos_sup (pos_ext_1 u) a) eqn: SUP1.
      { erewrite (pos_sup_trans u _ a); eauto using pos_ext_1_sup_true.
        destruct (a =? pos_ext_0 u)%positive eqn: EQ.
        { apply Pos.eqb_eq in EQ. subst.
          erewrite pos_ext_1_disj in SUP1; ss; eauto using pos_sup_refl. }
        r_solve. des_ifs.
      }
      destruct (a =? pos_ext_0 u)%positive eqn: EQ0.
      { apply Pos.eqb_eq in EQ0. subst. rewrite pos_sup_refl in SUP0. ss. }
      destruct (a =? pos_ext_1 u)%positive eqn: EQ1.
      { apply Pos.eqb_eq in EQ1. subst. rewrite pos_sup_refl in SUP1. ss. }
      des_ifs; r_solve; ii; r_solve;
        rewrite URA.add_comm in H2; eapply URA.wf_mon; eauto.
    }
    eapply OwnM_Upd in H2.
    iIntros "[H _]". iPoseProof (H2 with "H") as "H". iMod "H" as "[H1 H2]".
    iFrame. eauto.
  Qed.

  
  Lemma OwnIs_split u n inve invs Is (DIS: inv_disj (inve::invs)):
    (OwnM (OwnIs_auth_black u n) **
     (([∗ list] x ∈ seq 0 n, OwnM (inv_auth_black u x (Is x))) **
      ([∗ list] e ∈ (inve :: invs), invE_prop u e)))
    ⊢ #=>
    ((OwnM (OwnIs_auth_black (pos_ext_0 u) n) **
      ([∗ list] x ∈ seq 0 n, OwnM (inv_auth_black (pos_ext_0 u) x (Is x))) **
      invE_prop (pos_ext_0 u) inve) **
     (OwnM (OwnIs_auth_black (pos_ext_1 u) n) **
      ([∗ list] x ∈ seq 0 n, OwnM (inv_auth_black (pos_ext_1 u) x (Is x))) **
      ([∗ list] e ∈ invs, invE_prop (pos_ext_1 u) e))).
  Proof.
  Admitted.

  Lemma OwnDs_split u n Ds:
    (OwnM (OwnDs_auth_black u n) **
     ([∗ list] a ∈ seq 0 n, OwnM (OwnD_auth_black u a (Ds a))))
    ⊢ #=>
    ((OwnM (OwnDs_auth_black (pos_ext_0 u) n) **
      ([∗ list] a ∈ seq 0 n, OwnM (OwnD_auth_black (pos_ext_0 u) a (Ds a)))) **
     (OwnM (OwnDs_auth_black (pos_ext_1 u) n) **
      ([∗ list] a ∈ seq 0 n, OwnM (OwnD_auth_black (pos_ext_1 u) a (Ds a))))).
  Proof.
    revert u. induction n; i; ss.
  Admitted.
  
  Lemma wclosed_split1 u n inve (invs: list invE):
    inv_disj (inve::invs) ->
    (wclosed u n ** [∗ list] e ∈ (inve::invs), invE_prop u e)
    ⊢ #=>
    ((wclosed (pos_ext_0 u) n ** invE_prop (pos_ext_0 u) inve) **
     (wclosed (pos_ext_1 u) n ** [∗ list] e ∈ invs, invE_prop (pos_ext_1 u) e)).
  Proof.
    unfold wclosed, wsats_auth, wsats, wsat, inv_auth, OwnD_auth.
    rewrite !big_sepL_sep.
    iIntros (DIS) "[[[[DSE ISE] [DS SAT]] ES] INV]".
    iPoseProof (big_sepL_seq_exist with "DS") as (Ds) "DS".
    { exact (fun _ => ∅). }
    iPoseProof (big_sepL_seq_exist with "SAT") as (Is) "SAT".
    { exact (fun _ => ∅). }
    rewrite !big_sepL_sep.
    iDestruct "SAT" as "[IS SAT]".
    iCombine "DSE DS" as "DS".
    iCombine "ISE IS INV" as "IS".
    iPoseProof (OwnEs_split with "ES") as "ES". iMod "ES" as "[ES1 ES2]". iFrame.
    iPoseProof (OwnIs_split with "IS") as "IS"; eauto.
    iMod "IS" as "[[[IX1 IY1] IZ1] [[IX2 IY2] IZ2]]". iFrame.
    
    


    
    iPoseProof ((big_sepL_seq_exist_rev Is (fun x I => OwnM (inv_auth_black (pos_ext_0 u) x I))) with "IY1") as "IY1".
    
    
    

    
    
    
    
    
    
    

    
  Qed.


  Lemma OwnDs_auth_black_split u n I:
    URA.updatable
      (OwnDs_auth_black u n
      [⋅ list] n' ∈ seq 0 n, OwnD_auth_black u n' 

      )
      ((OwnDs_auth_black (pos_ext_0 u) n)
       ⋅
       (OwnDs_auth_black (pos_ext_1 u) n)).
  Proof.
    do 2 (apply pointwise_updatable; i).
    
    
  Qed.




    
    iIntros (DIS) "[WC [INVE INVS]]".
    assert (URA.updatable
              (OwnDs_auth_black u n)
              ((OwnDs_auth_black (pos_ext_0 u) n)
               ⋅
               (OwnDs_auth_black (pos_ext_1 u) n))).
      { do 2 (apply pointwise_updatable; i).
        unfold OwnE_auth_black, maps_to_res.
        do 2 (unfold URA.add; unseal "ra"; ss).
        destruct (a =? u)%positive eqn: EQ; cycle 1.
        { apply Pos.eqb_neq in EQ.
          destruct (excluded_middle_informative (a = u)); ss.
          setoid_rewrite URA.unit_idl. reflexivity. }
        apply Pos.eqb_eq in EQ. subst.
        destruct (excluded_middle_informative _); ss.
        destruct (excluded_middle_informative (a0 = n)).
        - subst. rewrite lookup_insert. rewrite NIN.
          rewrite URA.unit_id. reflexivity.
        - rewrite lookup_insert_ne; auto. rewrite URA.unit_idl. reflexivity.
      }


    
    unfold OwnEs.
    
    Search (OwnM (_: (_ ==> _)%ra)).
    
    
    
    
  Qed.
    
  
  Lemma wclosed_split u n (invs1 invs2: list invE):
    inv_disj (invs1++invs2) ->
    (wclosed u n ** [∗ list] e ∈ (invs1++invs2), invE_prop u e)
    ⊢
    ∃ u1 u2,
    (wclosed u1 n ** [∗ list] e ∈ invs1, invE_prop u1 e) **
    (wclosed u2 n ** [∗ list] e ∈ invs, invE_prop u2 e).
  Proof.
    cut (inv_disj (invs1++invs2) ->
         (wclosed u n ** [∗ list] e ∈ (invs1++invs2), invE_prop u e)
           ⊢
           (wclosed (pos_ext_0 u) n ** [∗ list] e ∈ invs1, invE_prop (pos_ext_0 u) e) **
           (wclosed (pos_ext_1 u) n ** [∗ list] e ∈ invs1, invE_prop (pos_ext_0 u) e)).


    
  Qed.
    
    

  
  


End WORLD_SPLIT_MERGE.


(* Goal (nroot .@ "gil") ## (nroot .@ "hur"). *)
(* eauto with solve_ndisj. *)
