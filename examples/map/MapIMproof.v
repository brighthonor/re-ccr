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
  Context `{_W: CtxWD.t}.
  Context `{@GRA.inG MapRA0 Γ}.
  Context `{@GRA.inG memRA Γ}. 

  (* Let wf: _ -> W -> Prop :=
        @inv_wf
          _ _
          unit
          (fun _ st_src st_tgt =>
             ((∃ blk ofs l (f: Z -> Z) (sz: Z), ⌜st_src = (f, sz)↑ /\ (length l = Z.to_nat sz) /\ (forall k (SZ: (0 <= k < sz)%Z), nth_error l (Z.to_nat k) = Some (f k)) /\ st_tgt = (Vptr blk ofs)↑⌝ ** OwnM ((blk, ofs) |-> (List.map Vint l)) ** pending0) ∨ (⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I)
  . *)


        
  Variable GlobalStbM: Sk.t -> gname -> option fspec.
  Hypothesis STBINCLM: forall sk, stb_incl (to_stb MemStb) (GlobalStbM sk).
  Hypothesis STB_setM: forall sk, (GlobalStbM sk) "set" = Some set_specM.

  Section LEMMA. 
    Lemma pending0_unique:
      pending0 -∗ pending0 -∗ False%I.
    Proof.
      Local Transparent pending0.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. clear - H1.
      rr in H1. ur in H1. unseal "ra". des. ur in H1. ss.
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
        i. des. rewrite H1. eauto.
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
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt.
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
    @isim _ I fls flt r g R RR ps pt (st_src, _APC stb at_most o >>= (fun x => tau;; Ret x) >>= k_src) sti_tgt.
  Proof.
    destruct sti_tgt.
    iIntros "K".
    iEval (rewrite unfold_APC).
    force. instantiate (1:= false). steps.
    force. instantiate (1:= next). unfold guarantee.
    force. steps.
    force. instantiate (1:= (fn, vargs)). steps.
    rewrite SPEC. steps. grind.
    Unshelve. eauto.
  Qed.

  (* Lemma hcall_clo
    I fls flt r g ps pt {R} RR st_src st_tgt k_src k_tgt
    fn vargs o fsp
    (* PURE, ... *)
  :
    (* ((∀st_src0 st_tgt0 vret_src vret_tgt, (I st_src0 st_tgt0) -∗ @isim _ I fls flt r g R RR true pt (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt))) *)
    (I st_src st_tgt ∗ (∀st_src0 st_tgt0 vret_src vret_tgt, (I st_src0 st_tgt0) -∗ @isim _ I fls flt r g R RR true pt (st_src0, k_src vret_src) (st_tgt0, k_tgt vret_tgt)))
  -∗  
    @isim _ I fls flt r g R RR ps pt (st_src, HoareCall true o fsp fn vargs >>= k_src) (st_tgt, trigger (Call fn vargs) >>= k_tgt).
  Proof.
  Admitted. *)

  (****************************)

  Local Notation universe := positive.
  (* Local Notation level := nat. *)

  Lemma initialized0_unique k : initialized0 k -∗ initialized0 k -∗ False.
  Proof. 
    iIntros "I0 I1". iCombine "I0 I1" as "I".
    iOwnWf "I". clear -H1.
    rr in H1. ur in H1. unseal "ra". des. ur in H0. ss.
  Qed.

  Definition init_points blk ofs f k := (initialized0 k ∨ OwnM ((blk, (ofs + k)%Z) |-> [Vint (f k)]))%I.

  Fixpoint mem_index (sz: nat) : list Z :=
      match sz with 0 => [] | S k => (Z.of_nat k) :: mem_index k end.

  Definition mem_inv blk ofs f sz := ([∗ list] k ∈ (mem_index sz), init_points blk ofs f k)%I.

  (* Fixpoint mem_inv blk ofs f sz : iProp := 
    match sz with
    | 0 => True%I
    | S sz0 => init_points blk ofs f sz0 ∗ mem_inv blk ofs f sz0
    end.    *)

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

  Let Ist: Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt =>
             ((∃ blk ofs (f: Z -> Z) (sz: Z), 
             ⌜st_src = (f, sz)↑⌝ 
             ∗ mem_inv blk ofs f (Z.to_nat sz) ∗ pending0) 
             ∨ (⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I).

  (* Let Ist: Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt =>
             ((∃ blk ofs (f: Z -> Z) (sz: Z), 
             ⌜st_src = (f, sz)↑ /\  st_tgt = (Vptr blk ofs)↑⌝ 
             ∗ mem_inv blk ofs f (Z.to_nat sz) ∗ pending0) 
             ∨ (⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I). *)

  (* Let Ist: Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt =>
             ((∃ blk ofs (f: Z -> Z) (sz: Z), 
             ⌜st_src = (f, sz)↑ /\  st_tgt = (Vptr blk ofs)↑⌝ 
             ∗ (∀ k (SZ: (0 <= k < sz)%Z), initialized0 k ∨ OwnM ((blk, (ofs + k)%Z) |-> [Vint (f k)])) ∗ pending0) 
             ∨ (⌜st_src = (fun (_: Z) => 0%Z, 0%Z)↑⌝))%I). *)
            
  Theorem sim: HModPair.sim (MapM.HMap GlobalStbM) (MapI.Map) Ist.
  Proof.
    econs; eauto; ii; econs; cycle 1; [s|sim_split].
    - iIntros "_". iSplitR; eauto. 
      steps. iRight. iFrame. esplits; eauto.
    - unfold cfunU, initF, MapI.initF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)". subst.
      iDestruct "IST" as "[IST|%]".
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P)".
        iExFalso. iApply (pending0_unique with "P P0").
      }
      rewrite Any.upcast_downcast in G. inv G. simpl in G0. inv G0.
      (* des. subst.  *)
      steps. 
      iApply APC_start_clo. instantiate (1:= 1 + x).
      iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "alloc"). stb_tac. ss.  }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. }

      (*** TODO: Make a lemma for < HoareCall / Call >***)
      instantiate (1:= Any.upcast [Vint x]).
      rewrite HoareCall_parse. prep. 
      unfold HoareCallPre. steps.
      force. instantiate (1:= x). 
      force. instantiate (1:= Any.upcast [Vint x]). 
      force. iSplitR; [eauto|].
      iRename "P0" into "IST". call.
      {   
        iLeft. iExists _, _, (λ _ : Z, 0%Z), x.
        iFrame. iSplit.
        { 
          iPureIntro. esplits; eauto.
          admit.
        }
        admit. 
      } 
      unfold HoareCallPost.
      steps.
      iDestruct "ASM" as "[ASM %]".
      iDestruct "ASM" as ( ? ) "[% ASM]". subst.
      (* iPoseProof () *)
      steps. 
      admit.

    - unfold cfunU, getF, MapI.getF, interp_sb_hp, HoareFun, ccallU. s.
      steps. iDestruct "ASM" as "(W & (% & INIT) & %)". subst. 
      rewrite Any.upcast_downcast in *. steps.
      iDestruct "IST" as "[IST|%]"; cycle 1.
      { des. subst. steps. exfalso. lia. }
      iDestruct "IST" as (? ? ? ?) "(% & MAP & P0)".
      des. subst. steps. 
      unfold scale_int. des_ifs; cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      steps. iApply APC_start_clo. instantiate (1:= 1).
      iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "load"). stb_tac. ss. }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. } 
      symmetry in G0. inv G0.
      replace (ofs + (x * 8) `div` 8)%Z with (ofs + Z.to_nat x)%Z. 
      2: { rewrite Z_div_mult; ss. lia. }
      instantiate (1:= (Any.upcast [Vptr blk (ofs + Z.to_nat x)])).
      iPoseProof (mem_inv_split with "MAP") as "[IP MAP]".
      { instantiate (1:= Z.to_nat x). lia. }

      prep. unfold HoareCall.
      force. instantiate (1:= (blk, (ofs + Z.to_nat x)%Z, _)).
      force. force.
      iDestruct "IP" as "[INIT'|POINT]".
      { 
        iExFalso. iApply (initialized0_unique with "INIT").
        iEval (rewrite ZifyInst.of_nat_to_nat_eq) in "INIT'".
        inv G1. replace (Z.max 0 x) with x. 2: { destruct x; eauto. lia. }
        eauto.
      } 
      iSplitL "POINT".
      { 
        iFrame. repeat iSplit; eauto.
      } 
      iCombine "P0 INIT MAP" as "IST".
      call.
      {
        iDestruct "IST" as "(P0 & INIT & MAP)".
        iLeft. iExists blk, ofs, f ,sz. iFrame.
        repeat iSplit; eauto.
        iApply "MAP". iLeft.  
        iEval (rewrite ZifyInst.of_nat_to_nat_eq).
        inv G1. replace (Z.max 0 x) with x. 2: { destruct x; eauto. lia. }
        eauto.
      }
      steps. 
      rewrite unfold_APC. 
      force. instantiate (1:= true). steps. 
      force. instantiate (1:= vret).
      iDestruct "ASM" as "[[A %] %]". subst.
      steps. force.
      iSplitR "IST".
      { 
        iFrame. 
        iSplit.
        { admit. }
        { iPureIntro. do 3 f_equal. lia. }  
      }
      (* instantiate (1:= Vint (f y3)). steps. *)
      steps. eauto.
    
    - unfold cfunU, setF, MapI.setF, interp_sb_hp, HoareFun, ccallU. s.
      steps. destruct y0. iDestruct "ASM" as "%". des_ifs.
      iDestruct "IST" as "[IST|%]"; cycle 1.
      { subst. steps. exfalso. lia. }
      iDestruct "IST" as (? ? ? ? ?) "(% & MAP & P0)".
      des. subst.
      rewrite G. steps.
      rewrite Heq. rewrite Heq0. steps.
      unfold scale_int. des_ifs; cycle 1.
      { exfalso. eapply n0. eapply Z.divide_factor_r. }
      steps. iApply APC_start_clo. instantiate (1:= 1).
      iApply APC_step_clo.
      { eapply STBINCLM. instantiate (2:= "store"). stb_tac. ss. }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. }
      instantiate (1:= Any.upcast [Vptr blk (ofs + (y4 * 8) `div` 8); Vint y5]).
      hexploit set_nth_success.
      { rewrite H2. instantiate (1:= Z.to_nat y4). lia. }
      i. des.
      iPoseProof (points_to_set_split with "MAP") as "[A B]".
      { rewrite set_nth_map. rewrite H1. ss.  }
      iDestruct "A" as ( ? ) "A".
      replace (ofs + (y4 * 8) `div` 8)%Z with (ofs + Z.to_nat y4)%Z. 
      2: { rewrite Z_div_mult; ss. lia. }
      unfold HoareCall.
      force. instantiate (1:= ((blk, ofs), v')).
      force. instantiate (1:= Any.upcast [Vptr blk (ofs + Z.to_nat y4); Vint y5]).
      force. iSplitL "A". { iFrame. admit.  }
      iCombine "P0 B" as "IST".
      call.
      { admit. }
      steps.
      rewrite unfold_APC.
      force. instantiate (1:= true). steps.
      force. force. iSplitR.
      { eauto. }
      iDestruct "ASM" as "[[A %] %]". subst.
      steps. eauto.
     
  Admitted.





(* 
  Theorem correct: refines2 [MapI.Map] [MapM.Map GlobalStbM].
  Proof.
    eapply adequacy_local2. econs; ss. i. rr.
    econstructor 1 with (wf:=wf) (le:=inv_le top2); ss; et; cycle 2.
    { eexists (inl tt). rr. econs; ss. eapply to_semantic. iIntros "_". iRight. auto. }
    { eapply inv_le_PreOrder. ss. }
    econs; ss.
    { unfold MapI.initF, MapM.initF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      { mDesAll. subst. mAssertPure False; ss. iApply (pending0_unique with "A1 A"). }
      mDesAll. subst.
      steps_safe. rewrite ! Any.pair_split. s. steps_safe. rewrite ! Any.pair_split. s.
      
      astart (1 + x). acatch.
      { eapply STBINCLM. stb_tac. ss. }
      { eapply OrdArith.lt_from_nat. eapply Nat.lt_succ_diag_r. }
      icall_open _ with "".
      { iModIntro. ss. }
      { ss. }
      ss. mDesAll. subst. ired_both. force_r. steps.
      pattern 0%Z at 15.
      match goal with
      | |- ?P 0%Z => cut (P (x - x)%Z)
      end; ss.
      { rewrite Z.sub_diag. ss. }
      mAssert (OwnM ((a, 0%Z) |-> (repeat (Vint 0) (x - x) ++ repeat Vundef x))) with "A1".
      { rewrite Nat.sub_diag. ss. }
      revert fr1 mr_src1 ACC.
      cut (x <= x).
      2:{ lia. }
      generalize x at 1 4 5 7 13. intros n. induction n; i.
      { rewrite unfold_iter. steps. des_ifs.
        { exfalso. lia. }
        astop. steps. iret _; ss.
        iModIntro. iSplit.
        { iLeft. iSplits. iSplitR "A"; eauto. iSplit; eauto.
          { iPureIntro. esplits; eauto.
            { instantiate (1:=List.repeat 0%Z (Z.to_nat x)). eapply repeat_length. }
            { i. rewrite repeat_nth; auto. lia. }
          }
          { replace (Z.to_nat x) with (x - 0).
            2:{ lia. }
            rewrite app_nil_r. rewrite repeat_map. ss.
          }
        }
        { ss. }
      }
      { rewrite unfold_iter. steps. des_ifs.
        2:{ exfalso. lia. }
        steps. unfold scale_int at 1. des_ifs.
        2:{ exfalso. eapply n0. eapply Z.divide_factor_r. }
        steps_safe.
        assert (EQ: (0 + ((x - S n)%nat * 8) `div` 8) = (x - S n)).
        { rewrite Nat.div_mul; ss. }
        mAssert (OwnM ((a, Z.of_nat (x - S n)) |-> [Vundef]) ** (OwnM ((a, Z.of_nat (x - S n)) |-> [Vint 0]) -* OwnM ((a, 0%Z) |-> (repeat (Vint 0) (x - n) ++ repeat Vundef n)))) with "A2".
        { rewrite points_to_app. rewrite points_to_split.
          iDestruct "A2" as "[A0 [A1 A2]]".
          iSplitL "A1".
          { replace (x - S n: Z) with (0 + strings.length (repeat (Vint 0) (x - S n)))%Z; ss.
            rewrite repeat_length. lia.
          }
          { iIntros "A1". rewrite points_to_app. iApply OwnM_combine.
            iSplitL "A0 A1".
            { assert (LEN: x - S n = length (repeat (Vint 0) (x - S n))%Z).
              { symmetry. rewrite repeat_length. auto. }
              iEval (rewrite LEN) in "A1".
              iCombine "A0 A1" as "A". iEval (rewrite <- points_to_app) in "A".
              replace (repeat (Vint 0) (x - S n) ++ [Vint 0]) with (repeat (Vint 0) ((x - S n) + 1)).
              { replace (x - S n + 1) with (x - n); ss. lia. }
              { rewrite repeat_app; ss. }
            }
            { replace (0 + strings.length (repeat (Vint 0) (x - n)))%Z with
                (0 + strings.length (repeat (Vint 0) (x - S n)) + 1)%Z; ss.
              repeat rewrite repeat_length. rewrite <- Z.add_assoc. lia.
            }
          }
        }
        mDesSep "A1" as "A1" "FR".
        acatch.
        { eapply STBINCLM. stb_tac. ss. }
        { eapply OrdArith.lt_from_nat. instantiate (1:=n). lia. }
        icall_open (_, _, _) with "A1".
        { iModIntro. iSplit; et. iExists _. iFrame. iPureIntro. rewrite Z.div_mul; ss.
          f_equal. f_equal. f_equal. lia.
        }
        { ss. }
        steps. mDesAll. subst. steps.
        mAssert _ with "FR POST" as "A2".
        { iApply ("FR" with "POST"). }
        replace (x - Z.pos (Pos.of_succ_nat n) + 1)%Z with (x - n)%Z.
        2:{ lia. }
        red in WLE. clarify. rename n into nnn. rename x into xxx. eapply IHn; eauto. lia.
      }
    }
    econs; ss.
    { unfold MapI.getF, MapM.getF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. rewrite ! Any.pair_split. s. steps.
      exfalso. lia. }
      mDesAll. des. steps. rewrite ! Any.pair_split. s. steps.  
      unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps_safe. astart 1. acatch.
      { eapply STBINCLM. stb_tac. ss. }
      mApply points_to_get_split "A1".
      2:{ eapply map_nth_error. eauto. }
      mDesAll.
      replace ((a0 + (z * 8) `div` 8)%Z) with ((a0 + Z.to_nat z)%Z); auto.
      2:{ rewrite Z_div_mult; ss. lia. }
      icall_open _ with "A1".
      { iModIntro. instantiate (1:= (_, _, _)). ss. iSplit; eauto. }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _, _, _. iSplitR "A"; eauto.
      iSplit; eauto. iApply "A2". auto.
    }
    econs; ss.
    { unfold MapI.setF, MapM.setF, ccallU. init. iarg. mDesAll. subst.
      mDesOr "INV".
      2:{ mDesAll. subst. steps. rewrite ! Any.pair_split. s. steps. rewrite ! Any.pair_split. s.  
       exfalso. lia. }
      mDesAll. des. steps. rewrite ! Any.pair_split. s. steps. rewrite ! Any.pair_split. s. 
      unfold scale_int. des_ifs.
      2:{ exfalso. eapply n. eapply Z.divide_factor_r. }
      steps_safe. astart 1. acatch.
      { eapply STBINCLM. stb_tac. ss. }
      hexploit set_nth_success.
      { rewrite PURE0. instantiate (1:=Z.to_nat z). lia. }
      i. des.
      mApply points_to_set_split "A1".
      2:{ rewrite set_nth_map. rewrite H1. ss. }
      mDesAll.
      replace ((a0 + (z * 8) `div` 8)%Z) with ((a0 + Z.to_nat z)%Z); auto.
      2:{ rewrite Z_div_mult; ss. lia. }
      icall_open _ with "A1".
      { iModIntro. iSplit; et. instantiate (1:= (_, _, _)). ss. iExists _. iSplit; eauto. }
      { ss. }
      ss. mDesAll. subst. steps. astop. steps.
      iret _; ss. iModIntro. iSplit; ss.
      iLeft. iExists _. iExists _, _, _, _. iSplitR "A"; eauto.
      iSplit; eauto.
      2:{ iApply "A2". eauto. }
      { iPureIntro. esplits; eauto.
        { erewrite set_nth_length; eauto. }
        { i. ss. erewrite set_nth_error; eauto. des_ifs; eauto. exfalso. lia. }
      }
    }
    econs; ss.
    { unfold MapI.set_by_userF, MapM.set_by_userF, ccallU.
      init. iarg. mDesAll. subst. steps_safe.
      rewrite STB_setM. steps_safe.
      icall_weaken set_specM _ _ with "*".
      { refl. }
      { iModIntro. eauto. }
      { ss. }
      steps. mDesAll. subst. rewrite _UNWRAPU2. steps.
      iret _; ss. iModIntro. iSplit; ss.
    }
    Unshelve. all: ss.
  Qed. *)

End SIMMODSEM.
