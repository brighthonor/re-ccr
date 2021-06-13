Require Import NewStackHeader NewStack2 NewStack3B HoareDef SimModSem.
Require Import Coqlib.
Require Import Universe.
Require Import Skeleton.
Require Import PCM.
Require Import ModSem Behavior.
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
Require Import TODOYJ.
Require Import HTactics Logic IPM.
Require Import OpenDef STB.
Require Import TODO.

Set Implicit Arguments.

Local Open Scope nat_scope.



Section SIMMODSEM.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Let W: Type := ((Σ * Any.t)) * ((Σ * Any.t)).

  Notation sim stk_res0 stk_mgr0 :=
    (∀ h,
        (∃ P stk, <<SRC: (stk_res0: URA.car (t:=_stkRA)) h = Some (Ag.ag P)>> ∧
                         <<TGT: (stk_mgr0: gmap mblock (list Z)) !! h = Some stk>> ∧ <<PR: Forall P stk>>) ∨
        (<<SRC: (stk_res0: URA.car (t:=_stkRA)) h = None>> ∧
                <<TGT: (stk_mgr0: gmap mblock (list Z)) !! h = None>>)
    )
  .
(*   match (stk_res0: URA.car (t:=_stkRA)) h with *)
(*   | Some P => ∃ stk, <<TGT: (stk_mgr0: gmap mblock (list Z)) !! h = Some stk>> ∧ <<PR: Forall P stk>> *)
(*   | None => <<TGT: (stk_mgr0: gmap mblock (list Z)) !! h = None>> *)
(*   end) *)

  Let wf: W -> Prop :=
    @mk_wf _ unit
           (fun _ _ _stk_mgr0 =>
              (∃ stk_mgr0 (stk_res0: URA.car (t:=_stkRA)),
                  (⌜(<<PHYS: _stk_mgr0 = stk_mgr0↑>>) /\ (<<SIM: sim stk_res0 stk_mgr0>>)⌝)
                  ∧ ({{"O": OwnM ((Auth.black stk_res0): URA.car (t:=stkRA))}})
              )%I)
           (fun _ _ _ => ⌜True⌝%I)
  .

  Section AUX.
    Context {K: Type} `{M: URA.t}.
    Let RA := URA.pointwise K M.

    Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
    Proof. ii. r in EXT. des. subst. ur. ss. eexists; et. Qed.

    Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
    Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

    Lemma pw_add_disj_wf
          (f g: K -> M)
          (WF0: URA.wf (f: @URA.car RA))
          (WF1: URA.wf (g: @URA.car RA))
          (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
      :
        <<WF: URA.wf ((f: RA) ⋅ g)>>
    .
    Proof.
      ii; ss. ur. i. ur in WF0. ur in WF1. spc DISJ. des; rewrite DISJ.
      - rewrite URA.unit_idl; et.
      - rewrite URA.unit_id; et.
    Qed.

    Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
        <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
    Proof.
      i. unfold insert, fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
    Qed.

  End AUX.

  Variable global_stb: list (string * fspec).
  Hypothesis STBINCL: stb_incl (KDebugStb ++ StackStb) global_stb.

  Lemma _is_stack_wf
        h stk
    :
      <<WF: URA.wf (_is_stack h stk)>>
  .
  Proof. ur. ur. i. unfold _is_stack. des_ifs; ur; ss. i; clarify. Qed.

  Lemma sim_update
        stk_res0
        stk_mgr0
        (SIM: sim stk_res0 stk_mgr0)
        (h: mblock) P (stk: (list Z))
        (PR: Forall P stk)
    :
      <<SIM: sim (<[h:=Some (Ag.ag P)]>stk_res0) (<[h:=stk]> stk_mgr0)>>
  .
  Proof.
    ii.
    destruct (dec h h0).
    - subst. rewrite ! lookup_insert. unfold insert, fn_insert. des_ifs. ss. left. esplits; et.
    - rewrite lookup_insert_ne; ss. unfold insert, fn_insert. des_ifs.
  Qed.

  Lemma add_disj_insert
        (stk_res0: _stkRA) h P
        (DISJ: stk_res0 h = ε)
    :
        (stk_res0 ⋅ _is_stack h P) = <[h:=Some (Ag.ag P)]>stk_res0
  .
  Proof.
    unfold insert, fn_insert. extensionality b. ur. unfold _is_stack. des_ifs.
    - rewrite DISJ. rewrite URA.unit_idl. ss.
    - rewrite URA.unit_id. ss.
  Qed.

  Theorem sim_modsem: ModSemPair.sim (NewStack3B.StackSem global_stb) (NewStack2.StackSem).
  Proof.
    econstructor 1 with (wf:=wf); ss; et; swap 2 3.
    { econs; ss.
      - eapply to_semantic; cycle 1. { admit "ez - wf". } iIntros "H". iExists _, _. iSplit; ss; et.
        iSplit; ss; et.
      - eapply to_semantic; cycle 1. { eapply URA.wf_unit. } iIntros "H". iPureIntro. ss.
    }
    econs; ss.
    { unfold NewStack2.new_body, cfun. init. harg. fold wf. mDesAll. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      astart 0. astop. steps. rewrite Any.upcast_downcast in *. clarify.
      rename g into stk_mgr0. rename x0 into h. rename a1 into stk_res0. rename x into P. des_u.
      force_l. exists ((Vptr h 0)↑). steps.
      mOwnWf "O".
      (* assert(WF1: forall k, stk_res0 k <> Excl.boom). *)
      (* { eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). *)
      (*   destruct (stk_res0 k); ss. ur in WF0; ss. } *)

      hret _; ss.
      { iPoseProof (OwnM_Upd with "O") as "O".
        { eapply Auth.auth_alloc2. instantiate (1:=(_is_stack h P)).
          rewrite add_disj_insert; ss.
          { eapply (@pw_insert_wf); et.
            { eapply Auth.black_wf; et. }
            { ur; ss. eapply Ag.wf. }
          }
          specialize (SIM h). des; clarify.
        }
        iMod "O". iDestruct "O" as "[A B]". iModIntro. iSplitL "A"; et.
        iExists _, _. iSplit; ss; et. iSplit; ss; et. iPureIntro. ii.
        assert(B: stk_res0 h = None).
        { destruct (stk_res0 h) eqn:T; ss. specialize (SIM h). des; clarify. }
        rewrite add_disj_insert; ss. eapply sim_update; et.
      }
    }
    econs; ss.
    { unfold NewStack2.pop_body, cfun. init. harg. fold wf. des_ifs_safe. mDesAll. des; clarify.
      steps. rewrite Any.upcast_downcast in *. clarify. steps.
      astart 1. steps.
      rename a0 into stk_mgr0. rename n into h. rename a1 into stk_res0.
      mCombine "O" "A".
      mOwnWf "O".
      (* assert(A: forall k, URA.wf ((stk_res0 k): URA.car (t:=Excl.t _))). *)
      (* { eapply URA.wf_mon in WF0. *)
      (*   eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). ss. } *)
      assert(D: URA.wf ((stk_res0: @URA.car _stkRA) h)).
      { eapply URA.wf_mon in WF0. eapply Auth.black_wf in WF0. des. eapply pw_wf in WF0. ss. }
      assert(B: stk_res0 h = Some (Ag.ag P)).
      { dup WF0.
        eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
        spc WF0. des_ifs. eapply Opt.extends in WF0; ss. des; subst. eapply Ag.extends in EXT; subst; ss.
        rewrite WF0 in D. ur in D. ss. }
      hexploit (SIM h); et. intro T; des; [|by clarify]. rewrite B in *.
      apply some_injective in SRC. eapply (@Ag.ag_inj _ P P0) in SRC. subst. ss. steps.
      rewrite Any.upcast_downcast in *. sym in _UNWRAPN. clarify. rewrite TGT. steps.
      destruct stk as [|x stk1].
      - astop. steps. force_l. esplits. steps. hret _; ss. iDestruct "O" as "[A B]". iModIntro. iFrame.
        repeat iSplit; ss; et.
      - steps.
        assert(SIM0: sim (stk_res0) (<[h:=stk1]> stk_mgr0)).
        { replace stk_res0 with (<[h:=Some (Ag.ag P0)]>stk_res0); cycle 1.
          { extensionality h0. unfold insert, fn_insert. des_ifs. }
          eapply sim_update; et. inv PR; ss.
        }

        mDesOwn "O".
        acatch.
        { eapply STBINCL. stb_tac; ss. }
        steps. hcall _ _ _ with "O"; auto.
        { iModIntro. iSplitL; ss; et. }
        { esplits; ss; et. eauto with ord_step. }
        fold wf. steps. astop. steps. force_l. esplits. steps. hret _; ss.
        { iModIntro. iDestruct "POST" as "[% %]". subst. iFrame; ss; et. repeat iSplit; ss; et.
          iExists _. iPureIntro. esplits; ss; et. right. inv PR;ss. }
    }
    econs; ss.
    { unfold NewStack2.push_body, cfun. init. harg. fold wf. des_ifs_safe. mDesAll. des; clarify.
      steps. rewrite Any.upcast_downcast in *. steps.  ss. clarify.
      rename a1 into stk_mgr0. rename n0 into h. rename a2 into stk_res0. rename z into x.
      rewrite Any.upcast_downcast in *. sym in _UNWRAPN. clarify.
      mCombine "O" "PRE".
      mOwnWf "O".
      assert(A: forall k, URA.wf ((stk_res0 k): URA.car (t:=Opt.t (Ag.t _)))).
      { eapply URA.wf_mon in WF0.
        eapply Auth.black_wf in WF0. eapply pw_wf in WF0. des. ii. specialize (WF0 k). apply WF0. }
      assert(B: stk_res0 h = Some (Ag.ag P)).
      { dup WF0.
        eapply Auth.auth_included in WF0. des. unfold _is_stack in WF0. eapply pw_extends in WF0. des.
        spc WF0. des_ifs. eapply Opt.extends in WF0; et. des; subst. ss.
        eapply Ag.extends in EXT; subst; et. eapply Opt.wf; ss; et. rewrite <- WF0; et. }
      hexploit (SIM h); et. intro T; des; [|by clarify]. rewrite B in *.
      apply some_injective in SRC. apply (@Ag.ag_inj _ P P0) in SRC. subst. ss. rewrite TGT. steps.
      astart 1. acatch; ss.
      { eapply STBINCL. stb_tac; ss. }
      assert(SIM0: sim (stk_res0) (<[h:=x :: stk]> stk_mgr0)).
      { replace stk_res0 with (<[h:=Some (Ag.ag P0)]>stk_res0); cycle 1.
        { extensionality h0. unfold insert, fn_insert. des_ifs. }
        eapply sim_update; et.
      }
      mDesOwn "O".
      steps. hcall _ _ _ with "O"; auto.
      { iModIntro. iSplitL; ss; et. }
      { esplits; ss; et. eauto with ord_step. }
      fold wf. steps. astop. steps. force_l. esplits. steps. hret _; ss.
      { iModIntro. iDestruct "POST" as "[% %]". subst. iFrame; ss; et. }
    }
  Unshelve.
    all: ss.
  Qed.

End SIMMODSEM.



Section SIMMOD.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG stkRA Σ}.

  Variable global_stb: Sk.t -> list (string * fspec).
  Hypothesis STBINCL: forall sk, stb_incl (KDebugStb ++ StackStb) (global_stb sk).

  Theorem correct: ModPair.sim (NewStack3B.Stack global_stb) (NewStack2.Stack).
  Proof.
    econs; ss.
    { ii. eapply sim_modsem; ss. }
  Qed.

End SIMMOD.
