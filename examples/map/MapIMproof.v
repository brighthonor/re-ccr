Require Import MapHeader MapI MapM HoareDef SimModSem SimModSemFacts.
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
Require Import Mem1 MemOpen STB Invariant.

Require Import SimModSemFacts IProofMode IRed ITactics.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.

Local Open Scope nat_scope.




Section SIMMODSEM.
  Context `{_M: MapRA0.t}.

  (* Context `{_W: CtxWD.t}.
  Context `{@GRA.inG pending0RA Γ}.
  Context `{@GRA.inG CallableRA Γ}.
  Context `{@GRA.inG MapStateRA Γ}. *)

  Context `{@GRA.inG memRA Γ}. 
        
  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  (* Hypothesis STB_getM: forall sk, (GlobalStbM sk) "get" = Some get_specM. *)
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Section LEMMA. 

    Lemma callable_unique:
      callable -∗ callable -∗ False%I.
    Proof.
      Local Transparent callable.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. clear -H3.
      rr in H3. ur in H3. unseal "ra". des. ur in H3. ss.
    Qed.    

    Lemma pending0_unique:
      pending0 -∗ pending0 -∗ False%I.
    Proof.
      Local Transparent pending0.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. clear - H3.
      rr in H3. ur in H3. unseal "ra". des. ur in H3. ss.
    Qed.

    Lemma points_to_get_split blk ofs l k v
          (GET: nth_error l k = Some v)
      :
      OwnM((blk, ofs) |-> l) -∗ (OwnM((blk, (ofs + k)%Z) |-> [v])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l))).
    Proof.
      revert blk ofs k v GET. induction l; ss; i.
      { destruct k; ss. }
      destruct k; ss.
      { clarify. iIntros "H". rewrite points_to_split.
        iDestruct "H" as "[H0 H1]". iSplitL "H0".
        { rewrite Z.add_0_r. ss. }
        iIntros "H". iSplitL "H".
        { rewrite Z.add_0_r. ss. }
        { ss. }
      }
      { iIntros "H". rewrite points_to_split.
        iDestruct "H" as "[H0 H1]".
        iPoseProof (IHl with "H1") as "H1"; eauto.
        iDestruct "H1" as "[H1 H2]".
        replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
        iSplitL "H1"; auto. iIntros "H1". iSplitL "H0"; auto.
        iApply "H2". auto.
      }
    Qed.

    Lemma set_nth_success A (l: list A) (k: nat) v
          (SZ: k < length l)
      :
      exists l', set_nth k l v = Some l'.
    Proof.
      revert k v SZ. induction l; ss; i.
      { exfalso. lia. }
      { destruct k; ss; eauto.
        hexploit IHl; eauto.
        { instantiate (1:=k). lia. }
        i. des. rewrite H3. eauto.
      }
    Qed.

    Lemma points_to_set_split blk ofs l k v l'
          (GET: set_nth k l v = Some l')
      :
      OwnM((blk, ofs) |-> l) -∗ (∃ v', OwnM((blk, (ofs + k)%Z) |-> [v'])) ** ((OwnM((blk, (ofs + k)%Z) |-> [v]) -* OwnM((blk, ofs) |-> l'))).
    Proof.
      revert blk ofs k v l' GET. induction l; ss; i.
      { destruct k; ss. }
      destruct k; ss.
      { clarify. iIntros "H". rewrite points_to_split.
        iDestruct "H" as "[H0 H1]". iSplitL "H0".
        { rewrite Z.add_0_r. iExists _. ss. }
        iIntros "H". iEval (rewrite points_to_split). iSplitL "H".
        { rewrite Z.add_0_r. ss. }
        { ss. }
      }
      { iIntros "H". rewrite points_to_split.
        iDestruct "H" as "[H0 H1]".
        unfold option_map in GET. des_ifs.
        iPoseProof (IHl with "H1") as "H1"; eauto.
        iDestruct "H1" as "[H1 H2]". iDestruct "H1" as (v') "H1".
        replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
        iSplitL "H1"; auto. iIntros "H1".
        iEval (rewrite points_to_split). iSplitL "H0"; auto.
        iApply "H2". auto.
      }
    Qed.

    Lemma set_nth_map A B (f: A -> B) k l v
      :
      set_nth k (List.map f l) (f v) = option_map (List.map f) (set_nth k l v).
    Proof.
      revert k v. induction l; ss; i.
      { destruct k; ss. }
      { destruct k; ss. rewrite IHl. unfold option_map. des_ifs. }
    Qed.

    Lemma nth_error_map A B (f: A -> B) k l
      :
      nth_error (List.map f l) k = option_map f (nth_error l k).
    Proof.
      revert k. induction l; ss; i.
      { destruct k; ss. }
      { destruct k; ss. }
    Qed.

    Lemma repeat_nth A (a: A) n k
          (RANGE: k < n)
      :
      nth_error (List.repeat a n) k = Some a.
    Proof.
      revert k RANGE. induction n; ss; i.
      { lia. }
      { destruct k; ss. rewrite IHn; eauto. lia. }
    Qed.

    Lemma set_nth_length A k (a: A) l l'
          (SET: set_nth k l a = Some l')
      :
      length l' = length l.
    Proof.
      revert l l' SET. induction k; ss; i.
      { destruct l; ss. clarify. }
      { destruct l; ss. unfold option_map in *. des_ifs.
        ss. f_equal. eauto.
      }
    Qed.

    Lemma set_nth_error A k (a: A) l l' k'
          (SET: set_nth k l a = Some l')
      :
      nth_error l' k' = if Nat.eq_dec k' k then Some a else nth_error l k'.
    Proof.
      revert a l l' k' SET. induction k; ss; i.
      { destruct l; ss. clarify. des_ifs. destruct k'; ss. }
      { destruct l; ss. unfold option_map in *. des_ifs; ss.
        { erewrite IHk; eauto. des_ifs. }
        { destruct k'; ss. erewrite IHk; eauto. des_ifs. }
      }
    Qed.

    Lemma repeat_map A B (f: A -> B) (a: A) n
      :
      map f (repeat a n) = repeat (f a) n.
    Proof.
      induction n; ss. f_equal; auto.
    Qed.

    Lemma unfold_iter (E : Type -> Type) (A B : Type) (f : A -> itree E (A + B)) (x : A)
      :
      ITree.iter f x = lr <- f x;;
                       match lr with
                       | inl l => tau;; ITree.iter f l
                       | inr r => Ret r
                       end.
    Proof.
      eapply bisim_is_eq. eapply unfold_iter.
    Qed.

    Lemma points_to_nil blk ofs
      :
      ((blk, ofs) |-> []) = ε.
    Proof.
      Local Transparent URA.unit.
      ss. unfold points_to, Auth.white. f_equal.
      rewrite unfold_points_to.
      extensionality _blk. extensionality _ofs. unfold andb. des_ifs.
      exfalso. ss. lia.
    Qed.

    Lemma points_to_app blk ofs l0 l1
      :
      (blk, ofs) |-> (l0 ++ l1) = ((blk, ofs) |-> l0) ⋅ ((blk, (ofs + strings.length l0)%Z) |-> l1).
    Proof.
      revert ofs l1. induction l0; i; ss.
      { rewrite points_to_nil. rewrite URA.unit_idl. ss.
        replace (ofs + 0)%Z with ofs; ss. lia.
      }
      { rewrite points_to_split. rewrite (points_to_split blk ofs a l0).
        erewrite IHl0. rewrite URA.add_assoc. f_equal; ss.
        replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l0)))%Z with
          (ofs + 1 + strings.length l0)%Z; ss. lia.
      }
    Qed.

    Lemma OwnM_combine M `{@GRA.inG M Γ} a0 a1
      :
      (OwnM a0 ** OwnM a1) -∗ OwnM (a0 ⋅ a1).
    Proof.
      iIntros "[H0 H1]". iCombine "H0 H1" as "H". auto.
    Qed.

  End LEMMA.

  (***** Move and rename: APC & HoareCall LEMMAS *****)


  (* Try to match bind pattern *)
  Lemma APC_start_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb 
  :
    @isim _ I fls flt r g R RR true pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, interp_hEs_hAGEs stb o (trigger hAPC) >>= k_src) sti_tgt.
  Proof.
    unfold interp_hEs_hAGEs. rewrite! interp_trigger. grind.
    destruct sti_tgt. unfold HoareAPC.
    iIntros "K". 
    force. instantiate (1:= at_most).
    iApply "K".
  Qed.

  Lemma APC_stop_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb
  :
    @isim _ I fls flt r g R RR true pt (st_src, k_src tt) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K".
    rewrite unfold_APC. 
    force. instantiate (1:= true). steps. eauto.
  Qed.
  
  Lemma APC_step_clo
    I fls flt r g ps pt {R} RR st_src k_src sti_tgt  
    at_most o stb next fn vargs fsp
    (SPEC: stb fn = Some fsp)
    (NEXT: (next < at_most)%ord)
  :
    @isim _ I fls flt r g R RR true pt (st_src, HoareCall true o fsp fn vargs >>= (fun _ => _APC stb next o) >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => (tau;; Ret x) >>= k_src)) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K". prep.
    iEval (rewrite unfold_APC).
    force. instantiate (1:= false). steps.
    force. instantiate (1:= next). unfold guarantee.
    force. steps.
    force. instantiate (1:= (fn, vargs)). steps.
    rewrite SPEC. steps. grind.
    Unshelve. eauto.
  Qed.

  Lemma hcall_clo
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt
    fn varg_src varg_tgt o X (x: shelve__ X) (D: X -> ord) P Q
    (* PURE, ... *)
    (ORD: ord_lt (D x) o)
    (PURE: is_pure (D x))
  :
    (P x varg_src varg_tgt 
      ∗ I st_src st_tgt 
      ∗ (∀st_src0 st_tgt0 vret_src vret_tgt, 
             (Q x vret_src vret_tgt ∗ I st_src0 st_tgt0) 
          -∗ @isim _ I fls flt r g R RR true true (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)))
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, HoareCall true o (mk_fspec D P Q) fn varg_src >>= k_src) (st_tgt, trigger (Call fn varg_tgt) >>= k_tgt).
  Proof.
    iIntros "(P & IST & K)".
    unfold HoareCall. prep.
    force. instantiate (1:= x).
    force. instantiate (1:= varg_tgt).
    force. iSplitL "P"; [eauto|]. 
    call; [eauto|].
    steps. iApply "K". iFrame.
  Qed.

  (****************************)

  Local Notation universe := positive.
  (* Local Notation level := nat. *)

  (* Lemma initialized0_unique k : initialized0 k -∗ initialized0 k -∗ False.
  Proof. 
    iIntros "I0 I1". iCombine "I0 I1" as "I".
    iOwnWf "I". clear -H2.
    rr in H2. ur in H2. unseal "ra". des. ur in H0. ss.
  Qed. *)

  Definition init_points blk ofs f k :=  (OwnM ((blk, (ofs + k)%Z) |-> [Vint (f k)]))%I.
  (* Definition init_points blk ofs f k := (initialized0 k ∨ OwnM ((blk, (ofs + k)%Z) |-> [Vint (f k)]))%I. *)

  Fixpoint mem_index (sz: nat) : list Z :=
      match sz with 0 => [] | S k => (Z.of_nat k) :: mem_index k end.

  Definition mem_inv blk ofs f sz := ([∗ list] k ∈ (mem_index sz), init_points blk ofs f k)%I.

  (* Definition initial_inv := (∀ sz, ([∗ list] k ∈ (mem_index sz), initialized0 k))%I. *)

  Lemma mem_inv_split blk ofs f sz k (SZ: 0 <= k < sz): 
    mem_inv blk ofs f sz -∗ (init_points blk ofs f k ∗ (init_points blk ofs f k -* mem_inv blk ofs f sz)).
  Proof.
    i. iIntros "M". iEval (unfold mem_inv) in "M". 
    iInduction sz as [|sz0] "IH"; [lia|].
    des. eapply lt_n_Sm_le, le_lt_eq_dec in SZ0.
    destruct SZ0.
    { iDestruct "M" as "[I M]".
      iPoseProof ("IH" with "[]") as "H".
      { iPureIntro. eauto. }
      iPoseProof ("H" with "M") as "[I0 M]".
      iFrame. iIntros "I". iPoseProof ("M" with "I") as "M". iFrame.
    }
    iClear "IH". iDestruct "M" as "[I M]". subst. iFrame. eauto.
  Qed. 

  (* Fixpoint mem_inv_f blk ofs f sz :=
    match sz with
    | 0 => True%I
    | S sz' => (init_points blk ofs f sz' ∗ mem_inv_f blk ofs f sz')%I 
    end.

  Lemma mem_inv_unfold blk ofs f sz:
    mem_inv blk ofs f sz -∗ mem_inv_f blk ofs f sz.
  Proof. 
    induction sz; ss.
    iIntros "H". unfold mem_inv. s.
    iDestruct "H" as "[H0 H1]". iFrame.
    iApply IHsz. eauto.  
  Qed. *)

  (* Lemma mem_inv_split' blk ofs f sz k (SZ: 0 <= k < sz):
    mem_inv blk ofs f sz -∗ (init_points blk ofs f k ∗ ([∗ list] n ∈ (mem_index sz), if Z.eq_dec n k then True else init_points blk ofs f n)).
  Proof.
    induction sz; [lia|].
    destruct (classic (k = sz)).
    {
      subst. iIntros "H". unfold mem_inv. s.
      iDestruct "H" as "[H0 H1]". iFrame.
      destruct (Z.eq_dec sz sz); ss. iSplit; eauto.
      clear IHsz SZ e. generalize sz at 1 5. i.
      iStopProof. induction sz0; ss.
      iIntros "[H0 H1]". iSplitL "H0".
      { des_ifs. }
      iApply IHsz0. eauto.
    }
    iIntros "H". unfold mem_inv. s.
    iDestruct "H" as "[H0 H1]".
    destruct (Z.eq_dec sz k); [lia|].
    iFrame. iApply IHsz; eauto. lia.
  Qed. *)

  Lemma mem_inv_set blk ofs f sz k (SZ: 0 <= k < sz):
    mem_inv blk ofs f sz -∗ (∀x, init_points blk ofs f k ∗ (OwnM ((blk, (ofs + k)%Z) |-> [Vint x]) -∗ mem_inv blk ofs (fun n => if Z.eq_dec n k then x else (f n)) sz)).
  Proof.
    induction sz; [lia|].
    destruct (classic (k = sz)); cycle 1.
    {
      iIntros "H %". unfold mem_inv. s.
      iDestruct "H" as "[H0 H1]".
      replace (init_points blk ofs (λ n : Z, if Z.eq_dec n k then x else f n) sz) with (init_points blk ofs f sz).
      2: { unfold init_points. destruct (Z.eq_dec sz k); [lia|ss]. }
      iPoseProof (IHsz with "H1") as "H1"; [lia|]. 
      iSpecialize ("H1" $! x). iDestruct "H1" as "[H1 H2]".
      iFrame. iApply "H2".
    }
    clear IHsz SZ. subst.
    iIntros "H %". unfold mem_inv. s.
    iDestruct "H" as "[H0 H1]". iFrame.
    iIntros "OWN". iSplitL "OWN".
    { unfold init_points. des_ifs. }
    assert (forall (sz: nat) (NONZERO: sz > 0), sz = list_max (map (Z.to_nat) (mem_index sz)) + 1).
    { 
      i. induction sz0; [lia|].  
      s. destruct (classic (sz0 = 0)).
      { rewrite H3. eauto. }
      { assert (sz0 > 0) by lia. specialize (IHsz0 H4).
        replace (Z.to_nat sz0 `max` list_max (map Z.to_nat (mem_index sz0))) with (Z.to_nat sz0); lia.
      }
    }
    destruct (classic (sz = 0)).
    { rewrite H4. ss. }
    assert (sz > 0) by lia. hexploit (H3 sz H5).
    generalize sz at 2 3 7. i. 


    assert (sz > list_max (map Z.to_nat (mem_index sz0))) by lia. 
    clear H4 H5 H6.
    iStopProof. induction sz0; eauto. s.
    iIntros "[H0 H1]". iSplitL "H0".
    { unfold init_points. des_ifs. simpl in H7. lia. }
    iApply IHsz0; eauto. simpl in H7. lia.
  Qed.

  Definition init_map_st := (fun (_: Z) => 0%Z, 0%Z).
  
  Let Ist: Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt =>
             ((∃ blk ofs (f: Z -> Z) (sz: Z), 
                ⌜st_src = (f, sz)↑ /\  st_tgt = (Vptr blk ofs)↑⌝ 
                ∗ mem_inv blk ofs f (Z.to_nat sz) ∗ pending0 ∗ mapstate_full (init_map_st, Vnullptr)) 
             ∨ (⌜st_src = init_map_st↑ /\ st_tgt = Vnullptr↑⌝ ∗ mapstate_full (init_map_st, Vnullptr))
             ∨ (∃ st_src0 st_tgt0, callable ∗ mapstate (st_src0, st_tgt0) ∗ ⌜st_src = st_src0↑ /\ st_tgt = st_tgt0↑⌝))%I).

  Theorem sim: HModPair.sim (MapM.HMap GlobalStbM) (MapI.Map) Ist.
  Proof.
    sim_init.
    - iIntros "H". iSplitR; eauto. 
      steps. iRight. iLeft. iFrame. esplits; eauto.
    - unfold cfunU, initF, MapI.initF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (%Y & %M & P0 & C) & %X)". subst.
      iDestruct "IST" as "[IST|[IST|IST]]"; swap 2 3.
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P & M)".
        iExFalso. iApply (pending0_unique with "P P0").
      }
      {
        iDestruct "IST" as (? ?) "(C0 & _)".
        iExFalso. iApply (callable_unique with "C C0"). 
      }
      iDestruct "IST" as "[% M]".
      rewrite Any.upcast_downcast in G. inv G. simpl in G0. inv G0.
      des. subst. 
      steps.
      iApply APC_start_clo. instantiate (1:= 1 + x). prep. iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "alloc"). stb_tac. ss.  }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. }
      instantiate (1:= Any.upcast [Vint x]).
      rewrite HoareCall_parse. prep. 
      unfold HoareCallPre. steps.
      force. instantiate (1:= x). 
      force. instantiate (1:= Any.upcast [Vint x]). 
      force. iSplitR; [eauto|].
      iPoseProof (mapstate_update with "M") as "M".
      iMod "M". instantiate (1:= (((λ _ : Z, 0%Z), Z.of_nat x), Vnullptr)).
      iDestruct "M" as "[MB MW]".
      iCombine "C MW" as "IST". call.
      { 
        iRight. iRight. 
        iExists ((λ _ : Z, 0%Z), Z.of_nat x), Vnullptr. 
        iDestruct "IST" as "[C M]". iFrame. eauto. 
      }
      iDestruct "IST" as "[IST|[IST|IST]]".
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P & _)".
        iExFalso. iApply (pending0_unique with "P P0").
      }
      {
        iDestruct "IST" as "[% [MB0 MW]]". 
        iExFalso. iApply (mapstate_auth_unique with "MB MB0").  
      }
      iDestruct "IST" as (? ?) "[C [MW %]]".
      iPoseProof (mapstate_eq with "MB MW") as "%".
      des. subst. inv H4.
      unfold HoareCallPost. steps.
      iDestruct "ASM" as "[ASM %]".
      iDestruct "ASM" as ( ? ) "[% ASM]". subst.
      steps. 
      pattern 0%Z at 10.
      match goal with
      | |- ?P 0%Z => cut (P (x-x)%Z)
      end; ss.
      { rewrite Z.sub_diag. ss. }
      assert (OwnM ((b, 0%Z) |-> repeat Vundef x) -∗ OwnM ((b, 0%Z) |-> (repeat (Vint 0) (x - x) ++ repeat Vundef x))).
      { iIntros "H". rewrite Nat.sub_diag. ss. }
      iPoseProof (H3 with "ASM") as "O".
      iStopProof.
      cut (x <= x); [|lia].
      generalize x at 1 6 7 9 14. intros n. induction n; i; iIntros "(W & P0 & MB & C & MW & O)".
      { 
        rewrite unfold_iter. 
        steps. des_ifs; [lia|].
        iApply APC_stop_clo. steps. 
        force. force.
        iSplitL "W C". { iFrame. eauto. }
        iPoseProof (mapstate_update with "[MB MW]") as ">M"; [iFrame|].
        instantiate (1:= (init_map_st, Vnullptr)).
        steps. iSplit; [|eauto].
        iLeft. iExists _, _, _, _.
        iFrame. iSplit; eauto.
        replace (Z.to_nat x) with (x - 0); [|lia].
        rewrite app_nil_r.
        unfold mem_inv, init_points.
        replace (x - 0) with x; [|lia].
        iStopProof. induction x; eauto.
        iIntros "O"; s. 
        rewrite repeat_cons. rewrite points_to_app.
        iDestruct "O" as "[H0 H1]". rewrite repeat_length. iFrame.
        iApply IHx; [lia| |lia|lia|eauto].
        replace (x-x) with 0; [|lia].
        iIntros "H". rewrite points_to_app. rewrite repeat_length. s.
        rewrite points_to_nil. r_solve. 
        replace (0 + 0)%Z with 0%Z; [eauto|lia].
      }
      {
        rewrite unfold_iter. steps. des_ifs.
        2: { exfalso. lia. }
        steps. unfold scale_int at 1. des_ifs.
        2: { exfalso. eapply n0. eapply Z.divide_factor_r. }
        steps.
        assert (EQ: (0 + ((x - S n)%nat * 8) `div` 8) = (x - S n)).
        { rewrite Nat.div_mul; ss. }
        assert (
        OwnM ((b, 0%Z) |-> (repeat (Vint 0) (x - S n) ++ Vundef :: repeat Vundef n))
        -∗
        (OwnM ((b, Z.of_nat (x - S n)) |-> [Vundef]) ** (OwnM ((b, Z.of_nat (x - S n)) |-> [Vint 0]) -* OwnM ((b, 0%Z) |-> (repeat (Vint 0) (x - n) ++ repeat Vundef n))))
        ).
        { 
          iIntros "H". rewrite points_to_app. rewrite points_to_split.
          iDestruct "H" as "[H0 [H1 H2]]". iSplitL "H1".
          {
            replace (x - S n: Z) with (0 + strings.length (repeat (Vint 0) (x - S n)))%Z; ss.
            rewrite repeat_length. lia.
          }
          iIntros "H1". rewrite points_to_app.
          remember ((b, 0%Z) |-> repeat (Vint 0) (x - n)).
          remember ((b, (0 + length (repeat (Vint 0) (x - n)))%Z) |-> repeat Vundef n).
          assert (OwnM c ∗ OwnM c0 -∗ OwnM (c ⋅ c0)).
          { iIntros "[H0 H1]". iCombine "H0 H1" as "H". eauto. }
          subst. iApply H5.
          iSplitL "H0 H1".
          {
            assert (LEN: x - S n = length (repeat (Vint 0) (x - S n))%Z).
            { rewrite repeat_length. refl. }
            iEval (rewrite LEN) in "H1".
            iCombine "H0 H1" as "H". iEval (rewrite <- points_to_app) in "H".
            replace (repeat (Vint 0) (x - S n) ++ [Vint 0]) with (repeat (Vint 0) ((x - S n) + 1)).
            { replace (x - S n + 1) with (x - n); ss. lia. }
            { rewrite repeat_app; ss. }
          }
          replace (0 + strings.length (repeat (Vint 0) (x - n)))%Z with
          (0 + strings.length (repeat (Vint 0) (x - S n)) + 1)%Z; ss.
          repeat rewrite repeat_length. rewrite <- Z.add_assoc. lia.
        }
        iPoseProof (H5 with "O") as "[H0 H1]".
        iApply APC_step_clo.
        { eapply STBINCLM. instantiate (2:= "store"). stb_tac. ss. }
        { eapply OrdArith.lt_from_nat. instantiate (1:=n). lia. }
        instantiate (1:= (Any.upcast [Vptr b (0 + ((x - Z.pos (Pos.of_succ_nat n)) * 8) `div` 8); Vint 0])).
        rewrite HoareCall_parse. prep.
        unfold HoareCallPre.
        force. Unshelve. 2: { eapply (b, (x - S n)%Z, Vint 0). }
        force. Unshelve. 2: { eapply ([Vptr b (0 + ((x - Z.pos (Pos.of_succ_nat n)) * 8) `div` 8); Vint 0]↑). }
        force. iSplitL "H0". 
        { 
          iSplit; eauto. iSplit; eauto. 
          iExists Vundef. iSplitR.
          { 
            iPureIntro. 
            replace (0 + ((x - Z.pos (Pos.of_succ_nat n)) * 8) `div` 8)%Z with (x - Z.pos (Pos.of_succ_nat n))%Z; eauto. 
            rewrite Z.div_mul; lia.
          }
          replace (x - Z.pos (Pos.of_succ_nat n))%Z with (Z.of_nat (Init.Nat.sub x (S n))); [eauto|lia].
        }
        steps. iCombine "MB MW" as "M". 
        iPoseProof (mapstate_update with "M") as ">[MB MW]". instantiate (1:= ((λ _ : Z, 0%Z, Z.of_nat x), Vptr b 0)).
        iCombine "C MW" as "IST".
        call.
        { 
          iRight. iRight. iDestruct "IST" as "[C MW]".
          iExists _, _. iFrame. eauto.
        }
        iDestruct "IST" as "[IST|[IST|IST]]".
        { 
          iDestruct "IST" as (? ? ? ?) "(_ & _ & P & _)".  
          iExFalso. iApply (pending0_unique with "P P0").
        }
        {
          iDestruct "IST" as "[_ [MB0 _]]".
          iExFalso. iApply (mapstate_auth_unique with "MB MB0").  
        }
        iDestruct "IST" as (? ?) "(C & MW & %)".
        iPoseProof (mapstate_eq with "MB MW") as "%".
        des. inv H7.    
        unfold HoareCallPost. steps.
        iDestruct "ASM" as "[ASM %]".
        iDestruct "ASM" as "[H0 %]". subst.
        steps. 
        replace (x - Z.pos (Pos.of_succ_nat n) + 1)%Z with (x - n)%Z; [|lia].
        replace (x - Z.pos (Pos.of_succ_nat n))%Z with (Z.of_nat (Init.Nat.sub x (S n))); [|lia].
        iPoseProof ("H1" with "H0") as "O". 
        iPoseProof (mapstate_update with "[MB MW]") as ">[MB MW]";[iFrame|].
        instantiate (1:= (λ _ : Z, 0%Z, Z.of_nat x, Vnullptr)).
        iApply IHn; [lia|iFrame].
      }

    (***********************************)
    - unfold cfunU, getF, MapI.getF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (% & INIT) & %)". subst. 
      rewrite Any.upcast_downcast in *. steps.
      iDestruct "IST" as "[IST|[IST|IST]]"; swap 1 3.
      { 
        iDestruct "IST" as (? ?) "[C _]". 
        iExFalso. iApply (callable_unique with "C INIT").
      }
      {
        iDestruct "IST" as "[% _]".
        des. subst. steps. exfalso. lia. 
      }
      iDestruct "IST" as (? ? ? ?) "(% & MEM & P0 & M)".
      des. subst. steps. 
      unfold scale_int. des_ifs; cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      steps. iApply APC_start_clo. instantiate (1:= 1).
      prep. iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "load"). stb_tac. ss. }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. } 
      symmetry in G0. inv G0.
      replace (ofs + (x * 8) `div` 8)%Z with (ofs + Z.to_nat x)%Z. 
      2: { rewrite Z_div_mult; ss. lia. }
      instantiate (1:= (Any.upcast [Vptr blk (ofs + Z.to_nat x)])).
      iPoseProof (mem_inv_split with "MEM") as "[IP MEM]".
      { instantiate (1:= Z.to_nat x). lia. }
      prep. unfold HoareCall.
      force. instantiate (1:= (blk, (ofs + Z.to_nat x)%Z, _)).
      force. force.
      iSplitL "IP".
      { 
        iFrame. repeat iSplit; eauto.
      }
      iPoseProof (mapstate_update with "M") as ">[MB MW]".
      instantiate (1:= (f, sz, Vptr blk ofs)).
      iCombine "INIT MW" as "IST".
      call.
      {
        iRight. iRight. iDestruct "IST" as "[C MW]".
        iExists (f, sz), (Vptr blk ofs). iFrame.
        iSplit; eauto.
      }
      iDestruct "IST" as "[IST|[IST|IST]]".
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P & _)".
        iExFalso. iApply (pending0_unique with "P P0").
      }
      {
        iDestruct "IST" as "[_ [MB0 _]]".
        iExFalso. iApply (mapstate_auth_unique with "MB MB0"). 
      }
      iDestruct "IST" as (? ?) "(C & MW & %)".
      iPoseProof (mapstate_eq with "MB MW") as "%". 
      des. inv H4.
      steps. 
      rewrite unfold_APC. 
      force. instantiate (1:= true). steps. 
      force. instantiate (1:= vret).
      iDestruct "ASM" as "[[A %] %]". subst.
      steps. force.
      iSplitL "W C".
      { iFrame. iPureIntro. do 3 f_equal. lia. }
      iCombine "MB MW" as "M". iPoseProof (mapstate_update with "M") as ">M".
      instantiate (1:= (init_map_st, Vnullptr)).
      steps. iSplitL; eauto. iLeft. iFrame.
      iExists blk, ofs, f, sz. iSplit; eauto.
      iApply "MEM". unfold init_points. eauto.
    
    (***********************************)  
    - unfold cfunU, setF, MapI.setF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (% & INIT) & %)". subst. 
      rewrite Any.upcast_downcast in *. steps.
      iDestruct "IST" as "[IST|[IST|IST]]"; swap 1 3.
      { 
        iDestruct "IST" as (? ?) "[C _]". 
        iExFalso. iApply (callable_unique with "C INIT").
      }
      {
        iDestruct "IST" as "[% _]".
        des. subst. steps. exfalso. lia. 
      }
      iDestruct "IST" as (? ? ? ?) "(% & MEM & P0 & M)".
      des. subst. steps. 
      unfold scale_int. des_ifs; cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      steps. iApply APC_start_clo. instantiate (1:= 1).
      prep. iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "store"). stb_tac. ss. }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. }
      instantiate (1:= Any.upcast [Vptr blk (ofs + (x0 * 8) `div` 8); Vint x1]).
      symmetry in Heq, Heq0. inv Heq. inv Heq0.
      replace (ofs + (x0 * 8) `div` 8)%Z with (ofs + Z.to_nat x0)%Z. 
      2: { rewrite Z_div_mult; ss. lia. }
      iPoseProof (mem_inv_set with "MEM") as "MEM".
      (* iPoseProof (mem_inv_split with "MEM") as "[IP MEM]". *)
      { instantiate (1:= Z.to_nat x0). lia. }
      iSpecialize ("MEM" $! x1). iDestruct "MEM" as "[IP MEM]".
      unfold HoareCall.
      force. instantiate (1:= (blk, (ofs + Z.to_nat x0)%Z, _)).
      force. force. iSplitL "IP".
      { iSplit; eauto. }
      iPoseProof (mapstate_update with "M") as ">[MB MW]".
      instantiate (1:= ((λ n : Z, if Z.eq_dec n x0 then x1 else f n, sz), (Vptr blk ofs))).
      iCombine "INIT MW" as "IST". call.
      {
        iRight. iRight. iDestruct "IST" as "[C MW]". 
        iExists _, _. iFrame. iSplit; eauto.
      }
      iDestruct "IST" as "[IST|[IST|IST]]".
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P & _)".
        iExFalso. iApply (pending0_unique with "P P0"). 
      }
      {
        iDestruct "IST" as "[_ [MB0 _]]".
        iExFalso. iApply (mapstate_auth_unique with "MB MB0").
      }
      iDestruct "IST" as (? ?) "[C [MW %]]".
      iPoseProof (mapstate_eq with "MB MW") as "%".
      des. inv H4.
      steps. iDestruct "ASM" as "[[A %] %]". subst.
      iApply APC_stop_clo. steps.
      force. force.
      iSplitL "W C". { iFrame. eauto. }
      iCombine "MB MW" as "M". iPoseProof (mapstate_update with "M") as ">M".
      instantiate (1:= (init_map_st, Vnullptr)).
      steps. iSplitL; eauto. iLeft. iExists _, _, _, _.
      iSplit; eauto. iFrame. iPoseProof ("MEM" with "A") as "MEM".
      assert (Z.of_nat (Z.to_nat x0) = x0) by lia.
      rewrite H3. eauto.

      (***********************************)
    - unfold cfunU, set_by_userF, MapI.set_by_userF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (% & INIT) & %)". subst. 
      rewrite Any.upcast_downcast in *. steps.
      rewrite STB_setM. steps.
      inv G. inv G0.
      unfold HoareCall.
      force. Unshelve. 2: { econs. eapply y1. eapply y2. eapply (y4, y). }
      force. instantiate (1:= [Vint y4; Vint y]↑).
      force. iSplitL "INIT W". { iFrame. eauto. }
      call; [eauto|].
      steps.
      iDestruct "ASM" as "(W & C & %)". subst.
      force. instantiate (1:= y3↑).
      force. iSplitL "W C". { iFrame. eauto. }
      rewrite G. steps. eauto.
  Qed.

End SIMMODSEM.
