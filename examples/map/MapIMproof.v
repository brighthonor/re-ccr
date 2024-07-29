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
Require Import Mem1 STB Invariant.

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

    (* Lemma callable_unique:
      callable -∗ callable -∗ False%I.
    Proof.
      Local Transparent callable.
      iIntros "H0 H1". iCombine "H0 H1" as "H".
      iOwnWf "H". exfalso. clear -H3.
      rr in H3. ur in H3. unseal "ra". des. ur in H3. ss.
    Qed.     *)

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
      (blk, ofs) |-> l -∗ ((blk, (ofs + k)%Z) |-> [v]) ∗ ((blk, (ofs + k)%Z) |-> [v] -* (blk, ofs) |-> l).
    Proof.
      revert blk ofs k v GET. induction l; ss; i.
      { destruct k; ss. }
      destruct k; ss.
      { clarify. iIntros "H". 
        iPoseProof (points_to_split with "H") as "[H0 H1]". iSplitL "H0".
        { rewrite Z.add_0_r. ss. }
        iIntros "H". iApply points_to_split. iSplitL "H".
        { rewrite Z.add_0_r. ss. }
        { ss. }
      }
      { iIntros "H". iPoseProof (points_to_split with "H") as "[H0 H1]".
        iPoseProof (IHl with "H1") as "H1"; eauto.
        iDestruct "H1" as "[H1 H2]".
        replace (ofs + Z.pos (Pos.of_succ_nat k))%Z with (ofs + 1 + k)%Z by lia.
        iSplitL "H1"; auto. iIntros "H1". iApply points_to_split. iSplitL "H0"; auto.
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
      (blk, ofs) |-> l -∗ (∃ v', (blk, (ofs + k)%Z) |-> [v']) ** (((blk, (ofs + k)%Z) |-> [v] -* (blk, ofs) |-> l')).
    Proof.
      revert blk ofs k v l' GET. induction l; ss; i.
      { destruct k; ss. }
      destruct k; ss.
      { clarify. iIntros "H". iPoseProof (points_to_split with "H") as "[H0 H1]".
        iSplitL "H0".
        { rewrite Z.add_0_r. iExists _. ss. }
        iIntros "H". iApply points_to_split. iSplitL "H".
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
      ((blk, ofs) |-> []) = OwnM ε.
    Proof.
      Local Transparent URA.unit.
      ss. unfold points_to, points_to_r, Auth.white. do 2 f_equal.
      rewrite unfold_points_to_r.
      extensionality _blk. extensionality _ofs. unfold andb. des_ifs.
      exfalso. ss. lia.
    Qed.
    
    Lemma points_to_add_unit blk ofs l
      :
      (blk, ofs) |-> l -∗ (OwnM ε ∗ (blk, ofs) |-> l).
    Proof.
      iIntros "H". assert (ofs = ofs); eauto. revert H1. 
      generalize ofs at 2 4. i. unfold points_to.
      replace (points_to_r (blk, ofs) l) with (points_to_r (blk, ofs) l ⋅ ε); [|r_solve].
      iDestruct "H" as "[H0 H1]". rewrite H1. iFrame.
    Qed.  


    (* Lemma emp_own_unit: emp -∗ OwnM ε.
    Proof.
      uiprop. i. *)

    Lemma points_to_app blk ofs l0 l1
      :
      (blk, ofs) |-> (l0 ++ l1) ⊣⊢ ((blk, ofs) |-> l0) ∗ ((blk, (ofs + strings.length l0)%Z) |-> l1).
    Proof.
      revert ofs l1. induction l0; i; ss.
      { 
        rewrite points_to_nil. unfold points_to. iSplit.
        - iIntros "H". replace (points_to_r (blk, ofs) l1) with (ε ⋅ (points_to_r (blk, ofs) l1)); [|r_solve].
          iDestruct "H" as "[H0 H1]". rewrite Z.add_0_r. iFrame.  
        - iIntros "[_ H]". rewrite Z.add_0_r. iFrame.
      }
      rewrite points_to_split. rewrite (points_to_split blk ofs a l0). erewrite IHl0. 
      replace (ofs + Z.pos (Pos.of_succ_nat (strings.length l0)))%Z with (ofs + 1 + strings.length l0)%Z; [|lia].
      iSplit.
      - iIntros "(H0 & H1 & H2)". iFrame.
      - iIntros "[[H0 H1] H2]". iFrame.
    Qed.

    Lemma OwnM_combine M `{@GRA.inG M Γ} a0 a1
      :
      (OwnM a0 ** OwnM a1) -∗ OwnM (a0 ⋅ a1).
    Proof.
      iIntros "[H0 H1]". iCombine "H0 H1" as "H". auto.
    Qed.

  End LEMMA.

  (***** Move and rename: APC & HoareCall LEMMAS *****)

  (* Lemma APC_start_clo
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
  Qed. *)



  (****************************)

  Local Notation universe := positive.
  (* Local Notation level := nat. *)

  Definition init_points blk ofs f k :=  ((blk, (ofs + k)%Z) |-> [Vint (f k)])%I.

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

  Lemma mem_inv_set blk ofs f sz k (SZ: 0 <= k < sz):
    mem_inv blk ofs f sz -∗ (∀x, init_points blk ofs f k ∗ (((blk, (ofs + k)%Z) |-> [Vint x]) -∗ mem_inv blk ofs (fun n => if Z.eq_dec n k then x else (f n)) sz)).
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
      { rewrite H1. eauto. }
      { assert (sz0 > 0) by lia. specialize (IHsz0 H2).
        replace (Z.to_nat sz0 `max` list_max (map Z.to_nat (mem_index sz0))) with (Z.to_nat sz0); lia.
      }
    }
    destruct (classic (sz = 0)).
    { rewrite H2. ss. }
    assert (sz > 0) by lia. hexploit (H1 sz H3).
    generalize sz at 2 3 7. i. 


    assert (sz > list_max (map Z.to_nat (mem_index sz0))) by lia. 
    clear H2 H3 H4.
    iStopProof. induction sz0; eauto. s.
    iIntros "[H0 H1]". iSplitL "H0".
    { unfold init_points. des_ifs. simpl in H5. lia. }
    iApply IHsz0; eauto. simpl in H5. lia.
  Qed.

  Definition init_map_st := (fun (_: Z) => 0%Z, 0%Z).
  
  Let Ist: Any.t -> Any.t -> iProp := 
    (fun st_src st_tgt =>
             ((∃ blk ofs (f: Z -> Z) (sz: Z), 
                ⌜st_src = Any.pair (f, sz)↑ tt↑ /\  st_tgt = Any.pair (Vptr blk ofs)↑ tt↑⌝ 
                ∗ mem_inv blk ofs f (Z.to_nat sz) ∗ pending0) 
             ∨ (⌜st_src = Any.pair init_map_st↑ tt↑ /\ st_tgt = Any.pair Vnullptr↑ tt↑⌝))%I).
             (* ∨ (∃ st_src0 st_tgt0, callable ∗ mapstate (st_src0, st_tgt0) ∗ ⌜st_src = st_src0↑ /\ st_tgt = st_tgt0↑⌝). *)

  Let Mem := HMem (fun _ => false).

  Theorem sim: HModPair.sim (HMod.add (MapM.HMap GlobalStbM) Mem) (HMod.add MapI.Map Mem) Ist.
  Proof.  
  (* Admitted. *)
    (* Takes 9 minutes for Qed *)

    sim_init.
    - iIntros "[H0 H1]". iFrame. iRight. eauto.
    - unfold cfunU, initF, MapI.initF, interp_sb_hp, HoareFun, ccallU. s.
      st. (* need to optimize *)
      iDestruct "ASM" as "(W & (%Y & %M & P0) & %X)". subst.
      st.
      iDestruct "IST" as "[IST|%]".
      {
        iDestruct "IST" as (? ? ? ?) "(_ & _ & P)".
        iExFalso. iApply (pending0_unique with "P P0").
      }
      des. subst.
      inline_r. 
      st. force. instantiate (1:= x).
      st. force. instantiate (1:= [Vint x]↑).
      st. force. iSplitR. { eauto. }
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st.
      rewrite unfold_APC.
      st. destruct y0; cycle 1.
      { unfold guarantee, triggerNB. st. inv y6. }
      unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
      st. iDestruct "GRT" as "[GRT %]". iDestruct "GRT" as ( ? ) "(% & POINTS)". subst. st.
      unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
      st. force. st. force. iSplitL "W". { eauto. }
      rewrite Any.upcast_downcast in G. inv G. inv G0. st.
      pattern 0%Z at 36.
      match goal with
      | |- ?P 0%Z => cut (P (x-x)%Z)
      end; ss.
      { rewrite Z.sub_diag. ss. }
      assert (POINTS: ((b, 0%Z) |-> repeat Vundef x) -∗ ((b, 0%Z) |-> (repeat (Vint 0) (x - x) ++ repeat Vundef x))).
      { iIntros "H". rewrite Nat.sub_diag. ss. }
      iPoseProof (POINTS with "POINTS") as "O".
      iStopProof. cut (x <= x); [|lia].
      generalize x at 1 4 5 11. intros n. induction n; i; iIntros "(P0 & O)".
      { 
        rewrite unfold_iter. st. destruct (Z_lt_le_dec (x - 0) x).
        { exfalso. lia. }
        st. iSplitL; [|eauto].
        iLeft. iFrame. iExists b, 0%Z, (fun _ => 0%Z), x.
        iSplit; eauto. unfold mem_inv, init_points.
        replace (x - 0) with x; [|lia].
        rewrite app_nil_r.
        iStopProof. induction x; eauto.
        iIntros "O"; s. 
        replace (Z.to_nat (Z.pos (Pos.of_succ_nat x))) with (S x); [|lia].
        rewrite repeat_cons. rewrite points_to_app.
        iDestruct "O" as "[H0 H1]". rewrite repeat_length.
        iPoseProof (IHx with "H0") as "IH"; [lia| |lia|lia| ].
        {
          replace (x-x) with 0; [|lia].
          iIntros "H". rewrite points_to_app. rewrite repeat_length. s.
          rewrite points_to_nil. 
          replace (0 + 0)%Z with 0%Z; [eauto|lia].
          iApply points_to_add_unit. eauto.
        }
        replace (Z.to_nat x) with x; [|lia]. iFrame.
      }

      rewrite unfold_iter. st.
      destruct (Z_lt_le_dec (x - Z.pos (Pos.of_succ_nat n)) x).
      2: { exfalso. lia. }
      st. unfold scale_int at 1.
      destruct (Zdivide_dec 8 ((x - Z.pos (Pos.of_succ_nat n)) * 8)).
      2: { exfalso. eapply n0. eapply Z.divide_factor_r. }
      st.
      assert (EQ: (0 + ((x - S n)%nat * 8) `div` 8) = (x - S n)).
      { rewrite Nat.div_mul; ss. }
      assert (
        ((b, 0%Z) |-> (repeat (Vint 0) (x - S n) ++ Vundef :: repeat Vundef n))
        -∗
        (((b, Z.of_nat (x - S n)) |-> [Vundef]) ** (((b, Z.of_nat (x - S n)) |-> [Vint 0]) -* ((b, 0%Z) |-> (repeat (Vint 0) (x - n) ++ repeat Vundef n))))
      ).
      { 
        clear IHn.
        iIntros "H". rewrite points_to_app. rewrite points_to_split.
        iDestruct "H" as "[H0 [H1 H2]]". iSplitL "H1".
        {
          replace (x - S n: Z) with (0 + strings.length (repeat (Vint 0) (x - S n)))%Z; ss.
          rewrite repeat_length. lia.
        }
        iIntros "H1". rewrite points_to_app. subst.
        iSplitL "H0 H1".
        {
          assert (LEN: x - S n = length (repeat (Vint 0) (x - S n))%Z).
          { rewrite repeat_length. refl. }
          iEval (rewrite LEN) in "H1".
          iPoseProof (points_to_app with "[H0 H1]") as "H". 
          { iSplitL "H0"; iFrame. }
          replace (repeat (Vint 0) (x - S n) ++ [Vint 0]) with (repeat (Vint 0) ((x - S n) + 1)).
          { replace (x - S n + 1) with (x - n); ss. lia. }
          { rewrite repeat_app; ss. }
        }
        replace (0 + strings.length (repeat (Vint 0) (x - n)))%Z with
        (0 + strings.length (repeat (Vint 0) (x - S n)) + 1)%Z; ss.
        repeat rewrite repeat_length. rewrite <- Z.add_assoc. lia.
      }
      
      iPoseProof (H2 with "O") as "[H0 H1]".

      inline_r.
      replace ((0 + ((x - Z.pos (Pos.of_succ_nat n)) * 8) `div` 8))%Z with (x - S n)%Z.
      2: { rewrite Z.div_mul; lia. }
      st. force. instantiate (1:= (b, (x - S n)%Z, Vint 0)).
      st. force.
      st. force. iSplitL "H0". 
      {   
        iSplit; eauto. replace ((x - Z.pos (Pos.of_succ_nat n))%Z) with (x - (S n))%Z; [|lia].
        iExists Vundef. iSplit; eauto.
        replace (Z.of_nat (Init.Nat.sub x (S n))) with (Z.sub (Z.of_nat x) (Z.of_nat (S n))); [|lia].
        iFrame.
      }
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st.
      rewrite unfold_APC.
      st. destruct y3; cycle 1.
      { unfold guarantee, triggerNB. st. inv y5. }
      st. iDestruct "GRT" as "((O & %) & %)". subst.
      st. replace (x - Z.pos (Pos.of_succ_nat n) + 1)%Z with (x - n)%Z; [|lia].
      iApply IHn; [lia|iFrame].
      replace (Z.of_nat (Init.Nat.sub x (S n))) with (Z.sub (Z.of_nat x) (Z.of_nat (S n))); [|lia].
      iApply ("H1" with "O").

    - unfold cfunU, getF, MapI.getF, interp_sb_hp, HoareFun, ccallU. s.
      st. iDestruct "ASM" as "(W & % & %)". subst. st.
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      { 
        iDestruct "IST" as "%". des. subst. 
        unfold ModSem.run_l. rewrite ! Any.pair_split. st.
        unfold assume. st. lia.
      }
      iDestruct "IST" as (? ? ? ?) "(% & (M & P))". des. subst.
      unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
      unfold assume. st. unfold scale_int. 
      destruct (Zdivide_dec 8 (x * 8)); cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      rewrite Any.upcast_downcast in G. inv G. inv G0.
      st. 
      replace (ofs + (y4 * 8) `div` 8)%Z with (ofs + Z.to_nat y4)%Z; cycle 1.
      { rewrite Z_div_mult; ss. lia. }
      iPoseProof (mem_inv_split with "M") as "[IP M]".
      { instantiate (1:= Z.to_nat y4). lia. }
      inline_r.
      st. force. instantiate (1:= (blk, (ofs + Z.to_nat y4)%Z, Vint (f (Z.to_nat y4)))).
      st. force.
      st. force.
      iSplitL "W". { eauto. }
      st. force.
      st. force. iSplitL "IP".
      { iSplit; eauto. }
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. rewrite unfold_APC.
      st. destruct y3; cycle 1.
      { unfold guarantee, triggerNB. st. inv y6. }
      st. iDestruct "GRT" as "[[GRT %] %]". subst.
      st. iSplitL; cycle 1.
      { iPureIntro. do 3 f_equal. lia. }
      iLeft. iExists blk, ofs, f, sz.
      iPoseProof ("M" with "GRT") as "M". iFrame. eauto.

    - unfold cfunU, setF, MapI.setF, interp_sb_hp, HoareFun, ccallU. s.
      st. iDestruct "ASM" as "(W & % & %)". subst.
      rewrite Any.upcast_downcast in G. inv G. inv G0.
      iDestruct "IST" as "[IST|IST]"; cycle 1.
      { 
        iDestruct "IST" as "%". des. subst. 
        unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l. 
        unfold assume. st. lia.
      }
      iDestruct "IST" as (? ? ? ?) "(% & M & P)". des. subst.
      unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
      st. unfold assume. st.
      unfold ModSem.run_l. rewrite ! Any.pair_split. fold ModSem.run_l.
      st. 
      unfold scale_int. destruct (Zdivide_dec 8 (y5 * 8)); cycle 1.
      { exfalso. eapply n. eapply Z.divide_factor_r. }
      st. force. st. force. iSplitL "W".
      { iFrame. eauto. }
      replace (ofs + (y5 * 8) `div` 8)%Z with (ofs + Z.to_nat y5)%Z. 
      2: { rewrite Z_div_mult; ss. lia. }
      iPoseProof (mem_inv_set with "M") as "M".
      { instantiate (1:= Z.to_nat y5). lia. }
      iSpecialize ("M" $! y6). iDestruct "M" as "[IP M]".
      inline_r.
      st. force. instantiate (1:= (blk, (ofs + Z.to_nat y5)%Z, Vint y6)).
      st. force.
      st. force. iSplitL "IP".
      { iSplit; eauto. }
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. rewrite unfold_APC.
      st. destruct y3; cycle 1.
      { unfold guarantee, triggerNB. st. inv y7. }
      st. iDestruct "GRT" as "[[O %] %]". subst.
      st. iSplit; eauto.
      iLeft. iExists blk, ofs, (λ n : Z, if Z.eq_dec n (Z.to_nat y5) then y6 else f n), sz.
      iPoseProof ("M" with "O") as "M". iFrame.
      iPureIntro. esplits; eauto.
      repeat f_equal. extensionality x. des_ifs; lia.

    - unfold cfunU, set_by_userF, MapI.set_by_userF, interp_sb_hp, HoareFun, ccallU. s.
      st. iDestruct "ASM" as "(W & % & %)". subst.
      rewrite Any.upcast_downcast in G. inv G. inv G0.
      st. rewrite STB_setM. st.
      unfold HoareCall.
      force. Unshelve. 2: { econs. eapply y1. eapply y2. eapply (y4, y). }
      force. instantiate (1:= [Vint y4; Vint y]↑).
      st. force. iSplitL "W". { iFrame. eauto. }
      call; [eauto|].
      st. iDestruct "ASM" as "(W & _ & %)". subst.
      force. st. force. iSplitL "W". { eauto. } 
      rewrite G0. st. iFrame. eauto.

   (***************** MEMORY FUNCTIONS ******************)
    - unfold cfunU, Mem1.alloc_spec, interp_sb_hp, HoareFun, ccallU. s.
      st. force. instantiate (1:= y0). 
      st. force.
      st. force. iSplitL "ASM"; [eauto|].
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. force. instantiate (1:= y2). 
      rewrite unfold_APC. 
      st. force. instantiate (1:= y3). 
      destruct y3; cycle 1.
      { unfold guarantee, triggerNB. st. inv y5. }
      st. force. st. force. st. force.
      iSplitL "GRT". { iFrame. }
      st. eauto.
    - unfold cfunU, Mem1.free_spec, interp_sb_hp, HoareFun, ccallU. s.
      st. force. instantiate (1:= (y1, y2)). 
      st. force.
      st. force. iSplitL "ASM"; [eauto|].
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. force. instantiate (1:= y3). 
      rewrite unfold_APC. 
      st. force. instantiate (1:= y4). 
      destruct y4; cycle 1.
      { unfold guarantee, triggerNB. st. inv y6. }
      st. force. st. force. st. force.
      iSplitL "GRT". { iFrame. }
      st. eauto.
    - unfold cfunU, Mem1.load_spec, interp_sb_hp, HoareFun, ccallU. s.
      st. force. instantiate (1:= (y0, y3, y2)). 
      st. force.
      st. force. iSplitL "ASM"; [eauto|].
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. force. instantiate (1:= y4). 
      rewrite unfold_APC. 
      st. force. instantiate (1:= y5). 
      destruct y5; cycle 1.
      { unfold guarantee, triggerNB. st. inv y7. }
      st. force. st. force. st. force.
      iSplitL "GRT". { iFrame. }
      st. eauto.
    - unfold cfunU, Mem1.store_spec, interp_sb_hp, HoareFun, ccallU. s.
      st. force. instantiate (1:= (y0, y3, y2)). 
      st. force.  
      st. force. iSplitL "ASM"; [eauto|].
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. force. instantiate (1:= y4). 
      rewrite unfold_APC. 
      st. force. instantiate (1:= y5). 
      destruct y5; cycle 1.
      { unfold guarantee, triggerNB. st. inv y7. }
      st. force. st. force. st. force.
      iSplitL "GRT". { iFrame. }
      st. eauto.
    - unfold cfunU, Mem1.cmp_spec, interp_sb_hp, HoareFun, ccallU. s.
      st. force. instantiate (1:= (y1, y2)).
      st. force.
      st. force. iSplitL "ASM"; [eauto|].
      st. rewrite interp_hAGEs_hapc. st.
      unfold HoareAPC. st. force. instantiate (1:= y3).
      rewrite unfold_APC. 
      st. force. instantiate (1:= y4). 
      destruct y4; cycle 1.
      { unfold guarantee, triggerNB. st. inv y6. }
      st. force. st. force. st. force.
      iSplitL "GRT". { iFrame. }
      st. eauto.
  Qed. 
  
End SIMMODSEM.
