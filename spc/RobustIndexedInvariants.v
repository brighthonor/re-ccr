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

  Class IInvSet (sProp : level -> Type) :=
    { prop : forall (i : level), sProp i -> iProp }.

  Definition InvSetRA (sProp : level -> Type) (n : level) : URA.t :=
    (Auth.t (positive ==> URA.agree (sProp n)))%ra.

  Definition OwnIsRA (sProp : level -> Type) : URA.t :=
    URA.pointwise universe (@URA.pointwise_dep level (InvSetRA sProp)).

  Definition OwnEsRA : URA.t :=
    URA.pointwise universe (URA.pointwise level CoPset.t).
  
  Definition OwnDsRA : URA.t :=
    URA.pointwise universe (URA.pointwise level (Auth.t Gset.t)).

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnI {sProp} `{@GRA.inG (OwnIsRA sProp) Σ} (u: universe) (n : level) (i : positive) (p : sProp n) :=
    OwnM (maps_to_res u (@maps_to_res_dep level (@InvSetRA sProp)
          n (Auth.white (@maps_to_res positive (URA.agree (sProp n)) i (Some (Some p))))) : OwnIsRA sProp).

  Definition OwnI_authR {sProp} `{@GRA.inG (OwnIsRA sProp) Σ} (u: universe) (n : level) (I : gmap positive (sProp n)) : OwnIsRA sProp :=
    maps_to_res u (@maps_to_res_dep level _ n (@Auth.black (positive ==> URA.agree (sProp n))%ra
                                                 (fun i => Some <$> (I !! i)))).

  Definition OwnI_auth {sProp} `{@GRA.inG (OwnIsRA sProp) Σ} (u: universe) (n: level) (I : gmap positive (sProp n)) :=
    OwnM (OwnI_authR u n I).
  
  Definition OwnE `{@GRA.inG OwnEsRA Σ} (u: universe) (n : level) (E : coPset) :=
    OwnM (maps_to_res u (@maps_to_res level CoPset.t n (Some E)) : OwnEsRA).

  Definition OwnD `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level) (D: gset positive) :=
    OwnM (maps_to_res u (@maps_to_res level (Auth.t Gset.t) n (Auth.white (Some D: Gset.t))) : OwnDsRA).

  Definition OwnD_authR `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level) (D: gset positive) : OwnDsRA :=
    maps_to_res u (@maps_to_res level (Auth.t Gset.t) n (Auth.black (Some D : Gset.t))).

  Definition OwnD_auth `{@GRA.inG OwnDsRA Σ} (u: universe) (n : level): iProp :=
    (∃ D, OwnM (OwnD_authR u n D))%I.

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

  Global Instance OwnI_persistent {sProp} `{@GRA.inG (OwnIsRA sProp) Σ}
    u n i p : Persistent (OwnI u n i p).
  Proof.
    unfold OwnI.
    remember (@maps_to_res_dep level (InvSetRA sProp) n (Auth.white (@maps_to_res positive (URA.agree (sProp n)) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H _ with "H") as "#HP". iModIntro.
    replace (maps_to_res u r) with (URA.core (maps_to_res u r)) at 2. auto.
    subst. unfold maps_to_res_dep, maps_to_res. ss. extensionalities u' n'. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.

  Variable u : universe.
  Variable n : level.

  Definition inv_satall (I : gmap positive (sProp n)) :=
    ([∗ map] i ↦ p ∈ I, (prop n p ∗ OwnD u n {[i]}) ∨ OwnE u n {[i]})%I.

  Definition wsat : iProp := (OwnD_auth u n ∗ ∃ I, OwnI_auth u n I ∗ inv_satall I)%I.

  Lemma alloc_name φ
        (INF : forall (E : level -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth u n ⊢ |==>  OwnD_auth u n ∗ ∃ i, ⌜φ i⌝ ∧ OwnD u n {[i]}.
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
              (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (sProp n))%ra (fun i => Some <$> (I !! i)))): OwnIsRA sProp)
              ((maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (sProp n))%ra (fun i => Some <$> (I' !! i)))): OwnIsRA sProp)
               ⋅
               (maps_to_res u (maps_to_res_dep n (Auth.white (@maps_to_res _ (URA.agree (sProp n)) i (Some (Some p))))): OwnIsRA sProp))).
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
    OwnM (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (sProp n))%ra (fun (i : positive) => None))) : OwnIsRA _)
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

  Lemma pos_sup_cases u k
    (EQ : (k =? u)%positive = false)
    (SUP0 : pos_sup (pos_ext_0 u) k = false)
    (SUP1 : pos_sup (pos_ext_1 u) k = false)
    :
    pos_sup u k = false.
  Proof.
    revert_until u. induction u; i; destruct k; ss; eauto.
  Qed.

End POSITIVE_AUX.

Notation coPsets := (gmap level coPset).

Section WSATS.

  Context `{Σ : GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{@IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.

  Definition OwnD_restR (u: universe) (n : level) : OwnDsRA :=
    fun u' n' =>
      if (u' =? u)%positive
      then
        (if (lt_dec n' n)
         then ε
         else Auth.black (Some ∅ : Gset.t))
      else
        ε.

  Definition OwnD_rest u n := OwnM (OwnD_restR u n)%I.

  Definition OwnI_restR u n : OwnIsRA sProp :=
    fun u' n' =>
      if (u' =? u)%positive
      then
        (if (lt_dec n' n)
         then ε
         else @Auth.black (_ ==> URA.agree (sProp n'))%ra (fun _ => None))
      else
        ε.

  Definition OwnI_rest u n := OwnM (OwnI_restR u n)%I.
  
  Definition OwnE_restR u (Es : coPsets) : OwnEsRA :=
    fun u' n' =>
      if (u' =? u)%positive
      then
        match Es !! n' with
        | Some _ => ε
        | None => Some ⊤
        end
      else
        ε.

  Definition OwnE_rest u (Es : coPsets) := OwnM (OwnE_restR u Es)%I.

  Definition OwnEs u (Es : coPsets) := ([∗ map] n ↦ E ∈ Es, OwnE u n E)%I.

  Definition OwnE_all u (Es : coPsets) := (OwnE_rest u Es ∗ OwnEs u Es)%I.

  Definition OwnE_top (Es : coPsets) : Prop := map_Forall (fun _ E => ⊤ ⊆ E) Es.

  Definition empty_univR {R: universe -> level -> URA.t} eu (r: forall u n, R u n) :=
    fun u n =>
      if (pos_sup eu u)
      then r u n
      else ε.

  Definition empty_univ (eu: universe) :=
    OwnM (empty_univR eu (fun _ _ => Some ⊤ : CoPset.t) : OwnEsRA)
    **
    OwnM (empty_univR eu (fun _ _ => Auth.black (Some ∅ : Gset.t)) : OwnDsRA)
    **
    OwnM (empty_univR eu (fun _ n => @Auth.black (_ ==> URA.agree (sProp n))%ra (fun _ => None)) : OwnIsRA sProp)
    .

  Definition OwnDI_rest u n := OwnD_rest u n ** OwnI_rest u n.

  Definition univ_rest := (∃ eu, empty_univ eu)%I.

  Definition wsats u n : iProp := ([∗ list] n' ∈ (seq 0 n), wsat u n')%I.
  
  Definition world u n Es :=
    wsats u n ** OwnE_all u Es ** OwnDI_rest u n ** univ_rest.

  Definition lookup_def (Es : coPsets) (n : nat) : coPset := default ⊤ (Es !! n).

  Definition subseteq_def (Es : coPsets) (n : nat) (E : coPset) : Prop :=
    match Es !! n with | Some E' => E ⊆ E' | None => True end.

  Definition insert_def (Es : coPsets) (n : nat) : coPsets :=
    match Es !! n with | Some E => Es | None => <[n:=⊤]> Es end.

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

  Lemma OwnDI_rest_nin u (n n' : level) (NIN : n < n')
    : OwnDI_rest u n ⊢ OwnDI_rest u n' ∗
                       ([∗ list] m ∈ (seq n (n' - n)), wsat u m).
  Proof.
    induction NIN.
    - iIntros "[DA AUTH]".
      assert ((OwnI_restR u n) =
              ((OwnI_restR u (S n))
              ⋅
              (maps_to_res u (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (sProp n))%ra (fun (i : positive) => None)))))).
      { i. subst. extensionalities u' n'. unfold OwnI_restR, maps_to_res, maps_to_res_dep.
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
      assert ((OwnD_restR u n) =
              ((OwnD_restR u (S n))
              ⋅
              (maps_to_res u (maps_to_res n (Auth.black (Some ∅ : Gset.t)))))).
      { i. subst. extensionalities u' n'. unfold OwnD_restR, maps_to_res.
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
      unfold OwnDI_rest, OwnD_rest, OwnI_rest.
      rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW". iFrame.
      replace (S n - n) with 1 by lia. ss. iFrame.
    - unfold OwnDI_rest in *.
      iIntros "[DA AUTH]". iPoseProof (IHNIN with "[DA AUTH]") as "[[DA AUTH] SAT]". iFrame.
      clear IHNIN.
      assert ((OwnI_restR u m) =
                ((OwnI_restR u (S m))
                   ⋅
                   (maps_to_res u (maps_to_res_dep m (@Auth.black (positive ==> URA.agree (sProp m))%ra (fun (i : positive) => None)))))).
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
      assert ((OwnD_restR u m) =
              ((OwnD_restR u (S m))
              ⋅
              (maps_to_res u (maps_to_res m (Auth.black (Some ∅ : Gset.t)))))).
      { i. extensionalities u' m'. unfold OwnD_restR, maps_to_res.
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
      unfold OwnD_rest, OwnI_rest.
      rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW". iFrame.
      iSplitL "DA AUTH"; cycle 1. 
      { iFrame. replace (S m - n) with ((m - n) + 1) by lia. rewrite seq_app.
        iApply big_sepL_app. iFrame.
        replace (n + (m - n)) with m by lia. ss. iFrame.
      }
      iFrame.
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
    n < n' -> OwnDI_rest u n ∗ wsats u n ⊢ OwnDI_rest u n' ∗ wsats u n'.
  Proof.
    iIntros (LT) "(AUTH & SAT)".
    iPoseProof ((OwnDI_rest_nin _ _ _ LT) with "AUTH") as "(AUTH & NEW)". iFrame.
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
    : OwnDI_rest u n' ∗ wsats u n' ⊢
                 |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
                         ∗ OwnDI_rest u (S n) ∗ (prop n p -∗ wsats u (S n))).
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
    : OwnDI_rest u n' ∗ wsats u n' ∗ prop n p
                 ⊢ |==> ((∃ i, ⌜φ i⌝ ∧ OwnI u n i p)
                           ∗ OwnDI_rest u (S n) ∗ wsats u (S n)).
  Proof.
    iIntros "(A & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[A W]") as "(I & A & W)".
    1,2: eauto.
    iFrame. iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma OwnDI_rest_OwnI_le u n n' i p :
    OwnI u n i p ∗ OwnDI_rest u n' ⊢ ⌜n < n'⌝.
  Proof.
    iIntros "(I & (_ & AUTH))".
    unfold OwnI, OwnDI_rest, OwnI_rest.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    unfold OwnI_restR, maps_to_res, maps_to_res_dep in WF.
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

  Lemma OwnE_has u Es n E :
    (Es !! n = Some E) -> OwnE_all u Es ⊢ OwnE_all u (<[n:=E]>Es).
  Proof.
    iIntros (IN) "ES". setoid_rewrite insert_id; auto.
  Qed.

  Lemma OwnE_alloc u Es n:
    (Es !! n = None) -> OwnE_all u Es ⊢ |==> OwnE_all u (<[n := ⊤]>Es).
  Proof.
    iIntros (NIN) "[AUTH SAT]". unfold OwnE_rest, OwnEs.
    remember (<[n := ⊤]> Es) as Es'.
    assert (URA.updatable
              (OwnE_restR u Es)
              ((OwnE_restR u Es')
               ⋅
               (@maps_to_res _ (_==>_)%ra u (maps_to_res n (Some ⊤))))).
    { i. do 2 (apply pointwise_updatable; i).
      unfold OwnE_restR, maps_to_res.
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
      - setoid_rewrite lookup_insert_ne; auto. rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]". clear H3.
    iModIntro. unfold OwnE_all, OwnE_rest, OwnEs.
    iSplitL "AUTH"; eauto.
    subst. iApply big_sepM_insert; auto. iFrame.
  Qed.

  Lemma OwnE_acc_in u Es n E (IN : Es !! n = Some E) :
    OwnE_all u Es ⊢ OwnE u n E ∗ OwnE_all u (<[n := ∅]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnEs.
    iAssert (OwnE u n E ∗ ([∗ map] n0↦E0 ∈ delete n Es, OwnE u n0 E0))%I with "[SAT]" as "[EN SAT]".
    { iApply big_sepM_delete; auto. }
    iPoseProof (OwnM_persistently with "EN") as "#EN2". ss.
    iAssert ([∗ map] n0↦E0 ∈ <[n := ∅]>Es, OwnE u n0 E0)%I with "[SAT]" as "SAT".
    { iApply big_sepM_insert_delete. iFrame. iApply (OwnM_extends with "EN2").
      unfold maps_to_res. clear. exists ε. rewrite URA.unit_id.
      extensionalities u' n'. des_ifs.
    }
    iFrame. iClear "EN2". unfold OwnE_rest.
    iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id.
    extensionalities u' n'.
    unfold OwnE_restR. destruct (Nat.eqb_spec n' n).
    - subst. setoid_rewrite lookup_insert. rewrite IN. auto.
    - setoid_rewrite lookup_insert_ne; auto.
  Qed.

  Lemma OwnE_acc_new u Es n (NIN : Es !! n = None) :
    OwnE_all u Es ⊢ |==> OwnE u n ⊤ ∗ OwnE_all u (<[n := ∅]>Es).
  Proof.
    iIntros "ENS". iMod (OwnE_alloc with "ENS") as "ENS". eauto.
    iModIntro.
    assert (<[n:=∅]> Es = <[n:=∅]> (<[n:=⊤]> Es)).
    { setoid_rewrite insert_insert. auto. }
    rewrite H3. iApply OwnE_acc_in.
    - setoid_rewrite lookup_insert. auto.
    - iFrame.
  Qed.

  Lemma OwnE_all_union u Es n E1 E2 :
    OwnE_all u (<[n:=E1]> Es) ∗ OwnE u n E2 ⊢ OwnE_all u (<[n:=E1 ∪ E2]> Es).
  Proof.
    iIntros "[[AUTH SAT] EN]". unfold OwnE_all. iSplitL "AUTH".
    {
      iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id.
      extensionalities u' n'.
      unfold OwnE_restR. destruct (Nat.eqb_spec n' n).
      - subst. repeat setoid_rewrite lookup_insert. auto.
      - repeat setoid_rewrite lookup_insert_ne; auto.
    }
    iApply big_sepM_insert_delete.
    iAssert (OwnE u n E1 ∗ (OwnEs u (delete n (<[n:=E1]> Es))))%I with "[SAT]" as "[EN' SAT]".
    { iApply big_sepM_delete.
      - apply lookup_insert.
      - iFrame.
    }
    assert ((delete n (<[n:=E1]> Es)) = delete n Es).
    { setoid_rewrite delete_insert_delete. auto. }
    rewrite H3. iFrame. iApply OwnE_union. iFrame.
  Qed.

  Lemma OwnE_free u Es n :
    Es !! n = None -> OwnE_all u (<[n:=⊤]>Es) ⊢ |==> OwnE_all u Es.
  Proof.
    iIntros (NIN) "ENS". iPoseProof (OwnE_acc_in with "ENS") as "[EN ENS]". apply lookup_insert.
    rewrite insert_insert. unfold OwnE_all. iDestruct "ENS" as "[AUTH SAT]".
    iSplitL "EN AUTH".
    - unfold OwnE_rest, OwnE. iCombine "EN AUTH" as "AUTH".
      assert (URA.updatable
                ((maps_to_res u (@maps_to_res level CoPset.t n (Some ⊤)))
                 ⋅
                 OwnE_restR u (<[n:=∅]> Es))
                (OwnE_restR u Es)).
      { i. do 2 (apply pointwise_updatable; i).
        unfold OwnE_restR, maps_to_res.
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
      iDestruct "AUTH" as "[H AUTH]".
      iCombine "H AUTH" as "AUTH".
      iMod (OwnM_Upd H3 with "AUTH") as "AUTH". eauto.
    - unfold OwnEs. iModIntro.
      iPoseProof (big_sepM_insert with "SAT") as "[_ SAT]"; auto.
  Qed.

  Lemma OwnE_update_one u Es n E1 E2 :
    OwnE_all u (<[n:=E1]>Es) ⊢ (OwnE u n E1 -∗ OwnE u n E2) -∗ OwnE_all u (<[n:=E2]>Es).
  Proof.
    iIntros "E IMPL". iPoseProof (OwnE_acc_in with "E") as "[E K]".
    { apply lookup_insert. }
    iPoseProof ("IMPL" with "E") as "E".
    iEval (rewrite insert_insert) in "K".
    iPoseProof (OwnE_all_union with "[E K]") as "E". iFrame.
    replace (∅ ∪ E2) with E2 by set_solver.
    iFrame.
  Qed.

  Lemma OwnE_all_subset u Es n E1 E2 :
    (E1 ⊆ E2) -> OwnE_all u (<[n:=E2]>Es) ⊢ OwnE_all u (<[n:=E1]>Es).
  Proof.
    iIntros (SUB) "ES". iApply (OwnE_update_one with "ES").
    iIntros "E". iPoseProof (OwnE_subset with "E") as "[E1 _]". eauto. iFrame.
  Qed.

  Lemma OwnE_all_disjoint u Es n E1 E2 :
    E1 ## E2 -> OwnE_all u (<[n:=E1 ∪ E2]>Es) ⊢ OwnE_all u (<[n:=E1]>Es) ∗ OwnE u n E2.
  Proof.
    iIntros (HE) "ENS". iPoseProof (OwnE_acc_in with "ENS") as "[EN ENS]".
    { apply lookup_insert. }
    iPoseProof ((OwnE_disjoint _ _ _ _ HE) with "EN") as "[EN1 EN2]".
    iFrame. rewrite insert_insert.
    iApply (OwnE_update_one with "ENS"). iIntros. iFrame.
  Qed.

  Lemma OwnE_free_all u Es :
    OwnE_top Es -> OwnE_all u Es ⊢ |==> OwnE_all u ∅.
  Proof.
    pattern Es. revert Es. apply map_ind.
    { iIntros (TOP) "ES". ss. }
    iIntros (? ? ? NONE IND TOP) "ES".
    iMod (OwnE_free with "[ES]") as "ES". eauto.
    { eapply map_Forall_lookup_1 in TOP. 2: apply lookup_insert. iApply OwnE_all_subset; eauto. }
    iApply IND. 2: iFrame.
    eapply map_Forall_insert_1_2; eauto.
  Qed.

  Lemma OwnE_lookup_def u Es n :
    OwnE_all u Es ⊢ |==> OwnE_all u (<[n := lookup_def Es n]>Es).
  Proof.
    iIntros "ENS". unfold lookup_def, default. des_ifs; ss.
    - rewrite insert_id; auto.
    - iMod (OwnE_alloc with "ENS") as "ENS"; eauto.
  Qed.

  Lemma lookup_subseteq_def Es n E :
    E ⊆ (lookup_def Es n) -> subseteq_def Es n E.
  Proof.
    unfold lookup_def,default, subseteq_def. i. des_ifs.
  Qed.

  Lemma OwnE_init_wf u:
    URA.wf (OwnE_restR u ∅).
  Proof.
    unfold OwnE_restR. ur. i. ur. i. des_ifs; ur; des_ifs.
  Qed.
 
  Lemma empty_univ_split eu:
    empty_univ eu ⊢ (OwnE_all eu ∅ ** OwnDI_rest eu 0 ** empty_univ (pos_ext_0 eu) ** empty_univ (pos_ext_1 eu)).
  Proof.
    assert (ERA: URA.extends
              ((OwnE_restR eu ∅) ⋅
               (empty_univR (pos_ext_0 eu) (fun _ _ => Some ⊤ : CoPset.t)) ⋅
               (empty_univR (pos_ext_1 eu) (fun _ _ => Some ⊤ : CoPset.t)))
              (empty_univR eu (fun _ _ => Some ⊤ : CoPset.t) : OwnEsRA)).
    { unfold empty_univR, OwnE_restR.
      exists ε. ur. ur. extensionalities k n.
      rewrite lookup_empty.
      destruct (k =? eu)%positive eqn: EQ.
      { apply Pos.eqb_eq in EQ. subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto.
      r_solve.
    }

    assert (DRA: URA.extends
              ((OwnD_restR eu 0) ⋅
               (empty_univR (pos_ext_0 eu) (fun _ _ => Auth.black (Some ∅ : Gset.t)) : OwnDsRA) ⋅
               (empty_univR (pos_ext_1 eu) (fun _ _ => Auth.black (Some ∅ : Gset.t)) : OwnDsRA))
              (empty_univR eu (fun _ _ => Auth.black (Some ∅ : Gset.t)) : OwnDsRA)).
    { unfold empty_univR, OwnD_restR.
      exists ε. ur. ur. extensionalities k n.
      destruct (k =? eu)%positive eqn: EQ.
      { apply Pos.eqb_eq in EQ. subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto.
      r_solve.
    }

    assert (IRA: URA.extends
              ((OwnI_restR eu 0) ⋅
               (empty_univR (pos_ext_0 eu) (fun _ n => @Auth.black (_ ==> URA.agree (sProp n))%ra (fun _ => None)) : OwnIsRA sProp) ⋅
               (empty_univR (pos_ext_1 eu) (fun _ n => @Auth.black (_ ==> URA.agree (sProp n))%ra (fun _ => None)) : OwnIsRA sProp))                   
              (empty_univR eu (fun _ n => @Auth.black (_ ==> URA.agree (sProp n))%ra (fun _ => None)) : OwnIsRA sProp)).
    { unfold empty_univR, OwnI_restR.
      exists ε. ur. ur. extensionalities k n.
      destruct (k =? eu)%positive eqn: EQ.
      { apply Pos.eqb_eq in EQ. subst.
        rewrite ->pos_ext_0_sup_false, pos_ext_1_sup_false, pos_sup_refl.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_0 eu) k) eqn: SUP0.
      { rewrite pos_ext_1_disj; eauto.
        erewrite pos_sup_trans; try eassumption; try apply pos_ext_0_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      destruct (pos_sup (pos_ext_1 eu) k) eqn: SUP1.
      { erewrite pos_sup_trans; try eassumption; try apply pos_ext_1_sup_true.
        r_solve. setoid_rewrite URA.unit_id. eauto. }
      rewrite pos_sup_cases; eauto.
      r_solve.
    }

    iIntros "[[ERA DRA] IRA]".
    iPoseProof ((OwnM_extends ERA) with "ERA") as "[[NE E1] E2]".
    iPoseProof ((OwnM_extends DRA) with "DRA") as "[[ND D1] D2]".
    iPoseProof ((OwnM_extends IRA) with "IRA") as "[[NI I1] I2]".
    iFrame. unfold OwnEs. rewrite big_sepM_empty. eauto.
  Qed.
  
  Lemma world_init:
    empty_univ 1 ⊢ world 1 0 ∅.
  Proof.
    unfold world, wsats, univ_rest. s. 
    iIntros "E".
    iPoseProof (empty_univ_split with "E") as "[[[E DI] R] _]".
    iFrame. iExists (pos_ext_0 1). iFrame.
  Qed.

End WSATS.

Notation "M '!?' k" := (lookup_def M k) (at level 20).
(* Notation "E '⪿' '(' Es ',' n ')'" := (subseteq_def Es n E) (at level 70). *)
Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{Invs : @IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.

  Definition inv u (n : level) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI u n i p)%I.

  Definition FUpd u n (A : iProp) (Es1 Es2 : coPsets) (P : iProp) : iProp :=
    A ∗ wsats u n ∗ OwnE_all u Es1 -∗ #=> (A ∗ wsats u n ∗ OwnE_all u Es2 ∗ P).

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
    ⊢ A ∗ wsats u n' ∗ OwnE_all u Es -∗ #=> (A ∗ (prop n p -∗ wsats u n') ∗ OwnE_all u Es ∗ (inv u n N p)).
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
    iPoseProof ((OwnE_acc_in _ _ _ _ INE) with "ENS") as "[EN ENS]".
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
    iModIntro. iFrame. iPoseProof (OwnE_all_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ E ∖ ↑N) with (E ∖ ↑N). 2: set_solver.
    iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close _ _ _ i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplit; auto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". iFrame.
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnE_all_union with "[EN1 EN2]") as "ENS". iFrame.
    rewrite insert_id. iFrame. rewrite INE. f_equal.
    rewrite difference_union_L. set_solver.
  Qed.

  Lemma FUpd_open u n' A Es n N (LT : n < n') (IN : (↑N) ⊆ Es !? n) p :
    inv u n N p ⊢
        FUpd u n' A Es
        (<[n := (Es !? n)∖↑N]> Es)
        ((prop n p) ∗ ((prop n p) -∗ FUpd u n' A (<[n := (Es !? n)∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & ENS)".
    unfold lookup_def, subseteq_def in *. destruct (Es !! n) eqn:CASES; ss.
    - iApply FUpd_open_aux; auto. unfold inv; auto. iFrame.
    - iAssert (
          (#=> (A ∗ (wsats u n' ∗ (OwnE_all u (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd u n' A (<[n:=⊤ ∖ ↑N]> Es) (<[n:=⊤]>Es) emp))))))
            -∗
            #=> (A ∗ (wsats u n' ∗ (OwnE_all u (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd u n' A (<[n:=⊤ ∖ ↑N]> Es) Es emp))))))%I as "K".
      { iIntros ">[A [SAT [ENS [P K]]]]". iModIntro. iFrame. iIntros "P".
        iPoseProof ("K" with "P") as "K". iIntros "[A [SAT ENS]]".
        iPoseProof ("K" with "[A SAT ENS]") as ">[A [SAT [ENS _]]]". iFrame.
        iMod (OwnE_free with "ENS") as "ENS". auto.
        iModIntro. iFrame.
      }
      iApply "K". iClear "K".
      iMod (OwnE_alloc _ _ _ CASES with "ENS") as "ENS". remember (<[n:=⊤]> Es) as Es'.
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
    iPoseProof ((OwnE_acc_in _ _ n) with "ENS") as "[EN ENS]". apply lookup_insert.
    iPoseProof (OwnE_disjoint _ _ _ _ D with "EN") as "[EN1 EN]".
    iPoseProof (OwnE_all_union with "[ENS EN1]") as "ENS". iFrame.
    replace (∅ ∪ lookup_def Es1 n) with (lookup_def Es1 n) by set_solver.
    destruct (coPset_equiv_dec E ∅); cycle 1.
    { unfold lookup_def, default in D. des_ifs; ss.
      2:{ exfalso. set_solver. }
      rewrite insert_insert. rewrite (insert_id Es1).
      2:{ unfold lookup_def, default. rewrite Heq. ss. }
      iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
      destruct (Es2 !! n) eqn:CASES.
      2:{ iMod ((OwnE_acc_new _ _ _ CASES) with "ENS2") as "[EN2 _]".
          iPoseProof (OwnE_exploit with "[EN EN2]") as "%DIS". iFrame.
          set_solver.
      }
      unfold lookup_def. rewrite CASES. ss.
      iPoseProof ((OwnE_acc_in _ _ _ _ CASES) with "ENS2") as "[EN2 ENS]".
      iPoseProof (OwnE_union with "[EN EN2]") as "EN". iFrame.
      iPoseProof (OwnE_all_union with "[ENS EN]") as "ENS". iFrame.
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
        iMod (OwnE_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
      - replace (lookup_def Es1 n) with (⊤ : coPset).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iMod ((OwnE_free _ _ _ CASES) with "ENS") as "ENS".
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". iFrame.
        iMod (OwnE_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
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
    iPoseProof (OwnE_all_disjoint with "ENS") as "[ENS EN]".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & ENS)". iModIntro. iFrame.
    iApply OwnE_all_union. iFrame.
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
    iMod (OwnE_alloc with "EN") as "EN". eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_free u n' A Es n P :
    FromModal (Es !! n = None) modality_id P (FUpd u n' A (<[n:=⊤]>Es) Es P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)".
    iMod (OwnE_free with "EN") as "EN". eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general u n' A Es n E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd u n' A (<[n:=E1]>Es) (<[n:=E2]>Es) P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    iPoseProof (OwnE_acc_in with "EN") as "[EN ENS]". apply lookup_insert.
    iPoseProof ((OwnE_subset _ _ _ _ HE) with "EN") as "[EN1 _]".
    iPoseProof (OwnE_all_union with "[ENS EN1]") as "ENS". iFrame. rewrite insert_insert.
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
    IntoAcc (inv u n N p) (n < n' /\ (↑N) ⊆ Es !? n) True
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

Section WORLD_SPLIT.

  Context `{Σ : GRA.t}.
  Context `{sProp : level -> Type}.
  Context `{Invs : @IInvSet Σ sProp}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (OwnIsRA sProp) Σ}.
  
  Definition invE := (namespace * { n & sProp n })%type.

  Definition inv_embed u (e: invE) : iProp :=
    inv u (projT1 e.2) e.1 (projT2 e.2).

  Definition invs_embed u (es: list invE) : iProp :=
    [∗ list] e ∈ es, inv_embed u e.    
  
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
    Proof. i. ss.  eauto with solve_ndisj. (* solve_ndisj. *) Qed.
  End TEST.

  Theorem universe_spawn u n Es:
    world u n Es ⊢ (world u n Es ** ∃ v, world v 0 ∅).
  Proof.
    unfold world, univ_rest, wsats. s.
    iIntros "[W R]". iDestruct "R" as (eu) "E".
    iPoseProof (empty_univ_split with "E") as "[[[E DI] L] R]".
    iFrame. iSplitL "L"; eauto.
    iExists eu. iSplitR "R"; eauto. iFrame.
  Qed.

  Theorem multiverse_travel u u' n n' Es Es' m N N' p
    (LT: m < n)
    (IN: (↑N) ⊆ Es !? n)
    :
    world u n Es ∗ world u' n' Es' ∗ inv u m N p
    ⊢ #=>
    world u n (<[n := (Es !? n)∖↑N]> Es) **
    world u' n' Es' ** inv u' m N' p.
  Proof.
    
  Qed.

(*   Fixpoint invs_in (invs: list invE) Es := *)
(*     match invs with *)
(*     | [] => True *)
(*     | (N, existT n _) :: invs' => *)
(*         ↑N ⊆ Es !? n ∧ invs_in invs' (<[n := (Es !? n)∖↑N]> Es) *)
(*     end. *)

(*   Fixpoint invs_remove (invs: list invE) Es := *)
(*     match invs with *)
(*     | [] => Es *)
(*     | (N, existT n _) :: invs' => *)
(*         invs_remove invs' (<[n := (Es !? n)∖↑N]> Es) *)
(*     end. *)

(*   Lemma world_inv_lt u n Es m N p: *)
(*     world u n Es ** inv u m N p ⊢ world u n Es ** inv u m N p ** ⌜m < n⌝. *)
(*   Proof. *)
(*   Admitted. *)

(*   Lemma world_mon {u} n m (LE: n <= m): *)
(*     world u n ∅ ⊢ world u m ∅. *)
(*   Proof. *)
(*   Admitted. *)

(*   Theorem world_split u n invs Es *)
(*     (IN: invs_in invs Es) *)
(*     : *)
(*     world u n Es ** invs_embed u invs *)
(*     ⊢ #=> *)
(*       ∃ v, *)
(*       world u n (invs_remove invs Es) ** *)
(*       world v n ∅ ** invs_embed v invs ** *)
(*       (∀ m invs' n' (GEn: n' >= n) (GEm: n' >= m), *)
(*        (world u n' (invs_remove invs Es) ** *)
(*         world v m ∅ ** invs_embed v invs') *)
(*        -* *)
(*        #=> (world u n' Es ** invs_embed u invs')). *)
(*   Proof. *)
(*     iIntros "[W INVS]". iPoseProof (world_spawn with "W") as "[W V]". *)
(*     iDestruct "V" as (v) "V". iExists v. *)
(*     revert n Es IN. induction invs; i. *)
(*     { unfold invs_embed. ss. iFrame. *)
(*       iPoseProof ((world_mon 0 n) with "V") as "V"; try lia. iFrame. *)
(*       iModIntro. iIntros (m invs' n' LEn LEm) "[[W V] I]". iClear "INVS". *)
(*       induction invs'; ss. *)
(*       { iModIntro. iFrame. } *)
(*       destruct a as [N [m' p]]. iDestruct "I" as "[I Is]". *)
(*       unfold inv_embed at 1. s. unfold world at 2. *)
(*       iCombine "V I" as "C". iPoseProof (world_inv_lt with "C") as "[[[[[SAT E] DI] R] I] %LT]". *)
(*       iPoseProof ((FUpd_open _ m emp ∅) with "I") as "Upd"; eauto. *)
(*       Local Transparent FUpd. unfold FUpd. *)

      


(*         apply insert_id in Heq. s. *)
        

        
(*         Check lookup_insert. *)

(*         admit. } *)
      
      

        
(* Search default. *)
(*         default. rewrite lookup_insert. unfold default. Search (_ !! _). *)

      
      
      

      
      
      
      
    
(*   Qed. *)
    
  (* Theorem wclosed_split u n (invs1 invs2: list invE) *)
  (*   (DIS: inv_disj (invs1 ++ invs2)) *)
  (*   : *)
  (*   (world u n ∅ ** invs_embed u (invs1++invs2)) *)
  (*   ⊢ *)
  (*   ∃ u1 u2, *)
  (*   (world u1 n ∅ ** invs_embed u1 invs1) ** *)
  (*   (world u2 n ∅ ** invs_embed u2 invs2) ** *)
  (*   (∀ n1 n2 invs1' invs2', *)
  (*    ((world u1 n1 ∅ ** invs_embed u1 (invs1'++invs1)) ** *)
  (*     (world u2 n2 ∅ ** invs_embed u2 (invs2'++invs2))) *)
  (*    -* *)
  (*    (world u (max n (max n1 n2)) ∅ ** invs_embed u (invs1'++invs2'++invs1++invs2))). *)
  (* Proof. *)
    
    
  (* Qed. *)

(*  
  Definition update_dep {B: level -> Type} (bs: forall n, B n) (n: level) (b: B n): forall n, B n.
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
*)
  
  (* Lemma OwnE_split u: *)
  (*   OwnE_all u ∅ ⊢ #=> (OwnE_all (pos_ext_0 u) ∅ ** OwnE_all (pos_ext_1 u) ∅). *)
  (* Proof. *)
  (*   unfold OwnEs, OwnE_rest, OwnEs, OwnE. *)
  (*   rewrite !big_sepM_empty. *)
  (*   assert (URA.updatable (OwnE_restR u ∅) *)
  (*             ((OwnE_restR (pos_ext_0 u) ∅) ⋅ (OwnE_restR (pos_ext_1 u) ∅))). *)
  (*   { do 2 (apply pointwise_updatable; i). *)
  (*     unfold OwnE_restR, maps_to_res. *)
  (*     do 2 (unfold URA.add; unseal "ra"; ss). *)
  (*     rewrite lookup_empty. *)
  (*     destruct (pos_sup (pos_ext_0 u) a) eqn: SUP0. *)
  (*     { erewrite (pos_sup_trans u _ a); eauto using pos_ext_0_sup_true. *)
  (*       erewrite pos_ext_1_disj; eauto. *)
  (*       destruct (a =? pos_ext_1 u)%positive eqn: EQ. *)
  (*       { apply Pos.eqb_eq in EQ. subst. *)
  (*         erewrite pos_ext_0_disj in SUP0; ss; eauto using pos_sup_refl. } *)
  (*       r_solve. des_ifs. *)
  (*     } *)
  (*     destruct (pos_sup (pos_ext_1 u) a) eqn: SUP1. *)
  (*     { erewrite (pos_sup_trans u _ a); eauto using pos_ext_1_sup_true. *)
  (*       destruct (a =? pos_ext_0 u)%positive eqn: EQ. *)
  (*       { apply Pos.eqb_eq in EQ. subst. *)
  (*         erewrite pos_ext_1_disj in SUP1; ss; eauto using pos_sup_refl. } *)
  (*       r_solve. des_ifs. *)
  (*     } *)
  (*     destruct (a =? pos_ext_0 u)%positive eqn: EQ0. *)
  (*     { apply Pos.eqb_eq in EQ0. subst. rewrite pos_sup_refl in SUP0. ss. } *)
  (*     destruct (a =? pos_ext_1 u)%positive eqn: EQ1. *)
  (*     { apply Pos.eqb_eq in EQ1. subst. rewrite pos_sup_refl in SUP1. ss. } *)
  (*     des_ifs; r_solve; ii; r_solve; *)
  (*       rewrite URA.add_comm in H2; eapply URA.wf_mon; eauto. *)
  (*   } *)
  (*   eapply OwnM_Upd in H2. *)
  (*   iIntros "[H _]". iPoseProof (H2 with "H") as "H". iMod "H" as "[H1 H2]". *)
  (*   iFrame. eauto. *)
  (* Qed. *)

  
  (* Lemma OwnI_split u n inve invs Is (DIS: inv_disj (inve::invs)): *)
  (*   (OwnM (OwnI_restR u n) ** *)
  (*    (([∗ list] x ∈ seq 0 n, OwnM (OwnI_authR u x (Is x))) ** *)
  (*     ([∗ list] e ∈ (inve :: invs), invE_prop u e))) *)
  (*   ⊢ #=> *)
  (*   ((OwnM (OwnI_restR (pos_ext_0 u) n) ** *)
  (*     ([∗ list] x ∈ seq 0 n, OwnM (OwnI_authR (pos_ext_0 u) x (Is x))) ** *)
  (*     invE_prop (pos_ext_0 u) inve) ** *)
  (*    (OwnM (OwnI_restR (pos_ext_1 u) n) ** *)
  (*     ([∗ list] x ∈ seq 0 n, OwnM (OwnI_authR (pos_ext_1 u) x (Is x))) ** *)
  (*     ([∗ list] e ∈ invs, invE_prop (pos_ext_1 u) e))). *)
  (* Proof. *)
  (* Admitted. *)

  (* Lemma OwnD_split u n Ds: *)
  (*   (OwnM (OwnD_restR u n) ** *)
  (*    ([∗ list] a ∈ seq 0 n, OwnM (OwnD_authR u a (Ds a)))) *)
  (*   ⊢ #=> *)
  (*   ((OwnM (OwnD_restR (pos_ext_0 u) n) ** *)
  (*     ([∗ list] a ∈ seq 0 n, OwnM (OwnD_authR (pos_ext_0 u) a (Ds a)))) ** *)
  (*    (OwnM (OwnD_restR (pos_ext_1 u) n) ** *)
  (*     ([∗ list] a ∈ seq 0 n, OwnM (OwnD_authR (pos_ext_1 u) a (Ds a))))). *)
  (* Proof. *)
  (*   revert u. induction n; i; ss. *)
  (* Admitted. *)

      

    
  
  (* Lemma wclosed_split1 u n inve (invs: list invE): *)
  (*   inv_disj (inve::invs) -> *)
  (*   (wclosed u n ** [∗ list] e ∈ (inve::invs), invE_prop u e) *)
  (*   ⊢ #=> *)
  (*   ((wclosed (pos_ext_0 u) n ** invE_prop (pos_ext_0 u) inve) ** *)
  (*    (wclosed (pos_ext_1 u) n ** [∗ list] e ∈ invs, invE_prop (pos_ext_1 u) e)). *)
  (* Proof. *)
  (*   unfold wclosed, rest, wsats, wsat, OwnI_auth, OwnD_auth. *)
  (*   rewrite !big_sepL_sep. *)
  (*   iIntros (DIS) "[[[[DSE ISE] [DS SAT]] ES] INV]". *)
  (*   iPoseProof (big_sepL_seq_exist with "DS") as (Ds) "DS". *)
  (*   { exact (fun _ => ∅). } *)
  (*   iPoseProof (big_sepL_seq_exist with "SAT") as (Is) "SAT". *)
  (*   { exact (fun _ => ∅). } *)
  (*   rewrite !big_sepL_sep. *)
  (*   iDestruct "SAT" as "[IS SAT]". *)
  (*   iCombine "DSE DS" as "DS". *)
  (*   iCombine "ISE IS INV" as "IS". *)
  (*   iPoseProof (OwnE_split with "ES") as "ES". iMod "ES" as "[ES1 ES2]". iFrame. *)
  (*   iPoseProof (OwnI_split with "IS") as "IS"; eauto. *)
  (*   iMod "IS" as "[[[IX1 IY1] IZ1] [[IX2 IY2] IZ2]]". iFrame. *)
    
    


    
  (*   iPoseProof ((big_sepL_seq_exist_rev Is (fun x I => OwnM (OwnI_authR (pos_ext_0 u) x I))) with "IY1") as "IY1". *)
    
    
    

    
    
    
    
    
    
    

    
  (* Qed. *)


  (* Lemma OwnD_restR_split u n I: *)
  (*   URA.updatable *)
  (*     (OwnD_restR u n *)
  (*     [⋅ list] n' ∈ seq 0 n, OwnD_authR u n'  *)

  (*     ) *)
  (*     ((OwnD_restR (pos_ext_0 u) n) *)
  (*      ⋅ *)
  (*      (OwnD_restR (pos_ext_1 u) n)). *)
  (* Proof. *)
  (*   do 2 (apply pointwise_updatable; i). *)
    
    
  (* Qed. *)




    
  (*   iIntros (DIS) "[WC [INVE INVS]]". *)
  (*   assert (URA.updatable *)
  (*             (OwnD_restR u n) *)
  (*             ((OwnD_restR (pos_ext_0 u) n) *)
  (*              ⋅ *)
  (*              (OwnD_restR (pos_ext_1 u) n))). *)
  (*     { do 2 (apply pointwise_updatable; i). *)
  (*       unfold OwnE_restR, maps_to_res. *)
  (*       do 2 (unfold URA.add; unseal "ra"; ss). *)
  (*       destruct (a =? u)%positive eqn: EQ; cycle 1. *)
  (*       { apply Pos.eqb_neq in EQ. *)
  (*         destruct (excluded_middle_informative (a = u)); ss. *)
  (*         setoid_rewrite URA.unit_idl. reflexivity. } *)
  (*       apply Pos.eqb_eq in EQ. subst. *)
  (*       destruct (excluded_middle_informative _); ss. *)
  (*       destruct (excluded_middle_informative (a0 = n)). *)
  (*       - subst. rewrite lookup_insert. rewrite NIN. *)
  (*         rewrite URA.unit_id. reflexivity. *)
  (*       - rewrite lookup_insert_ne; auto. rewrite URA.unit_idl. reflexivity. *)
  (*     } *)


    
  (*   unfold OwnEs. *)
    
  (*   Search (OwnM (_: (_ ==> _)%ra)). *)
    
    
    
    
  (* Qed. *)
    
  
  (* Lemma wclosed_split u n (invs1 invs2: list invE): *)
  (*   inv_disj (invs1++invs2) -> *)
  (*   (wclosed u n ** [∗ list] e ∈ (invs1++invs2), invE_prop u e) *)
  (*   ⊢ *)
  (*   ∃ u1 u2, *)
  (*   (wclosed u1 n ** [∗ list] e ∈ invs1, invE_prop u1 e) ** *)
  (*   (wclosed u2 n ** [∗ list] e ∈ invs, invE_prop u2 e). *)
  (* Proof. *)
  (*   cut (inv_disj (invs1++invs2) -> *)
  (*        (wclosed u n ** [∗ list] e ∈ (invs1++invs2), invE_prop u e) *)
  (*          ⊢ *)
  (*          (wclosed (pos_ext_0 u) n ** [∗ list] e ∈ invs1, invE_prop (pos_ext_0 u) e) ** *)
  (*          (wclosed (pos_ext_1 u) n ** [∗ list] e ∈ invs1, invE_prop (pos_ext_0 u) e)). *)


    
  (* Qed. *)
    
    

  
End WORLD_SPLIT.


(* Goal (nroot .@ "gil") ## (nroot .@ "hur"). *)
(* eauto with solve_ndisj. *)
