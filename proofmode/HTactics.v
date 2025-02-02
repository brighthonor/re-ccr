Require Import Coqlib.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import Any.
Require Import HoareDef.
Require Import SimModSem.
Require Import STB.

Require Import Relation_Definitions.
Require Import Relation_Operators.
Require Import RelationPairs.
From ExtLib Require Import
     Data.Map.FMapAList.
Require Import Red IRed.
Require Import ProofMode.
Require Import Invariant.

Set Implicit Arguments.

#[export] Hint Resolve sim_itree_mon: paco.
#[export] Hint Resolve cpn8_wcompat: paco.


Lemma ord_from_lt_sub (n1 n2: nat)
      (LT: n1 < n2)
  :
    ((n2 - n1 - 1)%nat + n1 < n2)%ord.
Proof.
  rewrite <- OrdArith.add_from_nat. eapply OrdArith.lt_from_nat. lia.
Qed.

Create HintDb ord_step.
#[export] Hint Resolve OrdArith.lt_add_r OrdArith.lt_from_nat: ord_step.
#[export] Hint Extern 5 => eapply Nat.lt_succ_diag_r: ord_step.
#[export] Hint Extern 5 => eapply ord_from_lt_sub; lia: ord_step.
#[export] Hint Extern 1000 => lia: ord_step.
(* Hint Rewrite <- OrdArith.add_from_nat: ord_step. *)

Ltac oauto :=
  try by (simpl; let bar := fresh in place_bar bar; clear_until bar; eauto with ord_step).

Create HintDb ord_step2.
#[export] Hint Resolve Ord.S_lt: ord_step2.
Ltac oauto2 := simpl; try apply Ord.S_lt; try by oauto.

Fixpoint Ord_S_n (o: Ord.t) (n: nat) :=
  match n with
  | 0 => o
  | S n' => Ord.S (Ord_S_n o n')
  end.

Lemma Ord_S_n_le o n: (o <= Ord_S_n o n)%ord.
Proof.
  induction n; ss.
  { refl. }
  { etrans; et. eapply Ord.lt_le. eapply Ord.S_lt. }
Qed.

Ltac ired_l := try (prw _red_gen 2 1 0).
Ltac ired_r := try (prw _red_gen 1 1 0).

Ltac ired_both := ired_l; ired_r.



(* "safe" simulation constructors *)
Section SIM.
  Variable world: Type.

  Let st_local: Type := (Any.t).
  Let W: Type := (Any.t) * (Any.t).

  Variable wf: world -> W -> Prop.
  Variable le: relation world.

  Variable fl_src fl_tgt: alist gname (Any.t -> itree Es Any.t).


  Variant _safe_sim_itree
          (r g: forall (R_src R_tgt: Type) (RR: st_local -> st_local -> R_src -> R_tgt -> Prop), bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop)
          {R_src R_tgt} (RR: st_local -> st_local -> R_src -> R_tgt -> Prop)
    : bool -> bool -> world -> st_local * itree Es R_src -> st_local * itree Es R_tgt -> Prop :=
  | safe_sim_itree_ret
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      v_src v_tgt
      (RET: RR st_src0 st_tgt0 v_src v_tgt)
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, (Ret v_src)) (st_tgt0, (Ret v_tgt))
  | safe_sim_itree_call
      i_src0 i_tgt0 w st_src0 st_tgt0
      fn varg k_src k_tgt
      (SIM: exists w0,
          (<<WF: wf w0 (st_src0, st_tgt0)>>) /\
          (<<K: forall w1 vret st_src1 st_tgt1 (WLE: le w0 w1) (WF: wf w1 (st_src1, st_tgt1)),
              r _ _ RR true true w (st_src1, k_src vret) (st_tgt1, k_tgt vret)>>))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src0, trigger (Call fn varg) >>= k_src)
                      (st_tgt0, trigger (Call fn varg) >>= k_tgt)

  | safe_sim_itree_syscall
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      fn varg rvs k_src k_tgt
      (K: forall vret,
          r _ _ RR true true w0 (st_src0, k_src vret) (st_tgt0, k_tgt vret))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Syscall fn varg rvs) >>= k_src)
                      (st_tgt0, trigger (Syscall fn varg rvs) >>= k_tgt)

  | safe_sim_itree_tau_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR true i_tgt0 w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, tau;; i_src) (st_tgt0, i_tgt)

  | safe_sim_itree_tau_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      i_src i_tgt
      (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src) (st_tgt0, tau;; i_tgt)
  | safe_sim_itree_choose_tgt
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X i_src k_tgt
      (K: forall (x: X), r _ _ RR i_src0 true w0 (st_src0, i_src) (st_tgt0, k_tgt x))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                      (st_tgt0, trigger (Choose X) >>= k_tgt)
                      
  | safe_sim_itree_take_src
      i_src0 i_tgt0 w0 st_src0 st_tgt0
      X k_src i_tgt
      (K: forall (x: X), r _ _ RR true i_tgt0 w0 (st_src0, k_src x) (st_tgt0, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (Take X) >>= k_src)
                      (st_tgt0, i_tgt)
  
  | safe_sim_itree_supdate_src
    i_src0 i_tgt0 w0 st_src0 st_tgt0
    X k_src i_tgt
    (run: st_local -> st_local * X)
    (K: r _ _ RR true i_tgt0 w0 (fst (run st_src0), k_src (snd (run st_src0))) (st_tgt0, i_tgt))
  :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, trigger (SUpdate run) >>= k_src)
                    (st_tgt0, i_tgt)

  | safe_sim_itree_supdate_tgt
    i_src0 i_tgt0 w0 st_src0 st_tgt0
    X i_src k_tgt
    (run: st_local -> st_local * X)
    (K: r _ _ RR i_src0 true w0 (st_src0, i_src) (fst (run st_tgt0), k_tgt (snd (run st_tgt0))))
  :
    _safe_sim_itree r g RR i_src0 i_tgt0 w0 (st_src0, i_src)
                    (st_tgt0, trigger (SUpdate run) >>= k_tgt)

  | safe_sim_itree_inline_src
      i_src0 i_tgt0 w st_src st_tgt
      f fn varg k_src i_tgt
      (FUN: alist_find fn fl_src = Some f)
      (K: r _ _ RR true i_tgt0 w (st_src, (f varg) >>= k_src) (st_tgt, i_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src, trigger (Call fn varg) >>= k_src)
                      (st_tgt, i_tgt)
  | safe_sim_itree_inline_tgt
      i_src0 i_tgt0 w st_src st_tgt
      f fn varg i_src k_tgt
      (FUN: alist_find fn fl_tgt = Some f)
      (K: r _ _ RR i_src0 true w (st_src, i_src) (st_tgt, (f varg) >>= k_tgt))
    :
      _safe_sim_itree r g RR i_src0 i_tgt0 w (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt)  
  .

  Lemma safe_sim_sim r g:
    @_safe_sim_itree (gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r g) (gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) g g)
    <8=
    gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r g.
  Proof.
    i. eapply sim_itreeC_spec. inv PR; try by (econs; eauto).
    des. econs; eauto.
  Qed.

End SIM.



Section HLEMMAS.
  Context `{Σ: GRA.t}.
  Local Opaque GRA.to_URA.

  Variant mk_wf (A: Type) 
          (R: A -> Any.t -> Any.t -> iProp)
    : A -> Any.t * Any.t -> Prop :=
  | mk_wf_intro
      a
      mr_src mp_src mp_tgt
      (RSRC: URA.wf mr_src -> R a mp_src mp_tgt mr_src)
    :
      mk_wf R a ((Any.pair mp_src mr_src↑), mp_tgt)
  .

  Definition inv_wf
             `{@GRA.inG invRA Σ}
             A 
             (R: A -> Any.t -> Any.t -> iProp)
    : _ -> (Any.t *  Any.t -> Prop) :=
    @mk_wf
      (A + Any.t * Any.t)%type
      (fun a' mp_src mp_tgt =>
         match a' with
         | inl a => R a mp_src mp_tgt
         | inr (mp_src1, mp_tgt1) => inv_closed ** ⌜mp_src1 = mp_src /\ mp_tgt1 = mp_tgt⌝
         end)%I
  .

  (* Lemma hcall_clo_ord_weaken'
        (fsp1: fspec) 
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A) FR

        (le: A -> A -> Prop) r rg a n m mr_src0 mp_src0 fl_src fl_tgt
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        fr0 I
        (ACC: current_iProp (fr0 ⋅ mr_src0) I)

        (UPDATABLE:
           I ⊢ #=> (FR ** R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) (mp_src1 mp_tgt1: Any.t) a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      fr1
                      (ACC: current_iProp (fr1 ⋅ mr_src1) (FR ** R a1 mp_src1 mp_tgt1 ** fsp1.(postcond) x vret_src vret_tgt))
          ,
                gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) rg rg _ _ eqr true true a
                  (Any.pair mp_src1 mr_src1↑, k_src (fr1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
                :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _ eqr m n a
             (Any.pair mp_src0 mr_src0↑, (HoareCall tbr ord_cur fsp0 fn varg_src) fr0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    subst. unfold HoareCall, mput, mget, assume, guarantee.
    ired_both. apply sim_itreeC_spec. econs 8.
    hexploit (WEAKER x). i. des.
    assert (exists mr_src0' rarg_src fr_src0',
               (<<UPDATABLE: URA.updatable (fr0 ⋅ mr_src0) (mr_src0' ⋅ (rarg_src ⋅ fr_src0'))>>) /\
               (<<RSRC: R a0 mp_src0 mp_tgt0 mr_src0'>>) /\
               (<<FRS: FR fr_src0'>>) /\
               (<<PRE: fsp0.(precond) x_tgt varg_src varg_tgt rarg_src>>)).
    { inv ACC. uipropall. 
      hexploit UPDATABLE; try apply IPROP.
      { eapply URA.updatable_wf; et. }
      i. des. subst.
      hexploit PRE; et. i. uipropall. 
      hexploit (H b); et.
      { eapply URA.updatable_wf; et. etrans; et. etrans; et. eapply URA.extends_updatable.
        exists (a2 ⋅ b0). r_solve. }
      i; des.
      esplits; et.
      etrans; et. etrans; et.
        replace (b0 ⋅ (r1 ⋅ a2)) with (b0 ⋅ a2 ⋅ r1) by r_solve.
      eapply URA.updatable_add; et. rewrite URA.add_comm; ss.
    }
    des. exists (rarg_src, fr_src0', mr_src0').
    repeat (ired_both; apply sim_itreeC_spec; econs 12). s. rewrite Any.pair_split.
    repeat (ired_both; apply sim_itreeC_spec; econs 8). unshelve esplits; eauto.
    { replace (rarg_src ⋅ fr_src0' ⋅ mr_src0') with (mr_src0' ⋅ (rarg_src ⋅ fr_src0')) by r_solve. ss. }

    repeat (ired_both; apply sim_itreeC_spec; econs 12).
    repeat (ired_both; apply sim_itreeC_spec; econs 8). exists x_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs 8). exists varg_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs 8). unshelve esplits; eauto.
    repeat (ired_both; apply sim_itreeC_spec; econs 8). unshelve esplits; eauto.
    { r in MEASURE. des_ifs; ss; des_ifs. eapply Ord.le_lt_lt; et. }
    { i. spc PURE0. r in MEASURE. des_ifs; ss; des_ifs. }
    { i. spc PURE1. r in MEASURE. des_ifs; ss; des_ifs. }
    repeat (ired_both; apply sim_itreeC_spec; econs).
    { econs; eauto. }
    i. repeat (ired_both; apply sim_itreeC_spec; econs). i. 
    repeat (ired_both; apply sim_itreeC_spec; econs). inv WF.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i.
    repeat (ired_both; apply sim_itreeC_spec; econs). i. 
    ired_both. eapply POST; eauto. hexploit POST0. i.
    uipropall. hexploit (H x0); et.
    { eapply URA.wf_extends; et. exists (fr_src0' ⋅ mr_src). r_solve. }
    i. des. econs.
    { cbn. esplits; et. eapply RSRC0; et. eapply URA.wf_extends; et. exists (fr_src0' ⋅ x0). r_solve. }
    { ss. }
    replace (fr_src0' ⋅ mr_src ⋅ r1) with (r1 ⋅ fr_src0' ⋅ mr_src) by r_solve.
    rewrite <- ! URA.add_assoc.
    eapply URA.updatable_add; et. refl.
  Qed.

  Lemma hcall_clo_ord_weaken
        Hns Rn Invn
        (fsp1: fspec) 
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        (le: A -> A -> Prop)  r rg a n m mr_src0 mp_src0 fl_src fl_tgt
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        fr0 l
        (ACC: current_iPropL (fr0 ⋅ mr_src0) l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) mp_src1 mp_tgt1 a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      fr1
                      (ACC: current_iPropL (fr1 ⋅ mr_src1) ((Invn, R a1 mp_src1 mp_tgt1) :: (Rn, fsp1.(postcond) x vret_src vret_tgt) :: snd (alist_pops Hns l)))
          ,
            gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) rg rg _ _ eqr true true a
                   ((Any.pair mp_src1 mr_src1↑), k_src (fr1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _ eqr m n a
             ((Any.pair mp_src0 mr_src0↑), (HoareCall tbr ord_cur fsp0 fn varg_src) fr0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    subst. eapply hcall_clo_ord_weaken'; et.
    { instantiate (2:=from_iPropL (snd (alist_pops Hns l))).
      etrans.
      { eapply iPropL_alist_pops. }
      iIntros "[H0 H1]".
      iPoseProof (UPDATABLE with "H0") as "> [H0 H2]".
      iModIntro. iFrame.
    }
    i. eapply POST; et. red. ss.
    eapply current_iProp_entail; et.
    iIntros "[[H0 H1] H2]". iFrame.
  Qed.

  Lemma hcall_clo_weaken
        Hns Rn Invn 
        (fsp1: fspec)
        (x: shelve__ fsp1.(meta))

        A (a0: shelve__ A)

        (le: A -> A -> Prop)  r rg a n m mr_src0 mp_src0 fl_src fl_tgt
        (fsp0: fspec)
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        (WEAKER: fspec_weaker fsp1 fsp0)

        fr0 l
        (ACC: current_iPropL (fr0 ⋅ mr_src0) l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (fsp1.(precond) x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (fsp1.(measure) x) ord_cur /\
               (tbr = true -> is_pure (fsp1.(measure) x)) /\ (tbr = false -> (fsp1.(measure) x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) mp_src1 mp_tgt1 a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      fr1
                      (ACC: current_iPropL (fr1 ⋅ mr_src1) (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, fsp1.(postcond) x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
            gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) rg rg _ _ eqr true true a
                   ((Any.pair mp_src1 mr_src1↑), k_src (fr1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _ eqr m n a
             ((Any.pair mp_src0 mr_src0↑), (HoareCall tbr ord_cur fsp0 fn varg_src) fr0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply (@hcall_clo_ord_weaken _ _ _); eauto.
  Qed.

  Lemma hcall_clo
        Hns Rn Invn
        X (x: shelve__ X)
        A (a0: shelve__ A)
        
        (D: X -> ord)
        (P: X -> Any.t -> Any.t -> iProp)
        (Q: X -> Any.t -> Any.t -> iProp)
        (le: A -> A -> Prop)  r rg a n m mr_src0 mp_src0 fl_src fl_tgt
        mp_tgt0 k_tgt k_src
        fn tbr ord_cur varg_src varg_tgt
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)

        fr0 l
        (ACC: current_iPropL (fr0 ⋅ mr_src0) l)

        (UPDATABLE:
           from_iPropL (fst (alist_pops Hns l)) ⊢ #=> (R a0 mp_src0 mp_tgt0 ** (P x varg_src varg_tgt: iProp)))

        (PURE: ord_lt (D x) ord_cur /\
               (tbr = true -> is_pure (D x)) /\ (tbr = false -> (D x) = ord_top))

        (POST: forall (vret_tgt : Any.t) (mr_src1: Σ) mp_src1 mp_tgt1 a1
                      (vret_src: Any.t)
                      (WLE: le a0 a1)
                      fr1
                      (ACC: current_iPropL (fr1 ⋅ mr_src1) (@cons (prod string (bi_car iProp)) (Invn, R a1 mp_src1 mp_tgt1) (@cons (prod string (bi_car iProp)) (Rn, Q x vret_src vret_tgt) (snd (alist_pops Hns l)))))
          ,
                gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) rg rg _ _ eqr true true a
                       ((Any.pair mp_src1 mr_src1↑), k_src (fr1, vret_src)) (mp_tgt1, k_tgt vret_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _ eqr m n a
             ((Any.pair mp_src0 mr_src0↑), (HoareCall tbr ord_cur (mk_fspec D P Q) fn varg_src) fr0 >>= k_src)
             (mp_tgt0, trigger (Call fn varg_tgt) >>= k_tgt)
  .
  Proof.
    eapply hcall_clo_weaken; eauto.
    { refl. }
    { eauto. }
    { eauto. }
    { eauto. }
  Qed.

  Lemma harg_clo
        A Rn Invn 
         r rg
        X (P: X -> Any.t -> Any.t -> iProp) varg
        mpr_src mp_tgt f_tgt k_src fl_src fl_tgt
        a (le: A -> A -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (WF: mk_wf R a (mpr_src, mp_tgt))
        m n
        (ARG:
           forall x varg_src
                  fr0 (mr_src: Σ) mp_src
                  (ACC: current_iPropL (fr0 ⋅ mr_src) (@cons (prod string (bi_car iProp)) (Rn, P  x varg_src varg) (@cons (prod string (bi_car iProp)) (Invn, R a mp_src mp_tgt) (@nil (prod string (bi_car iProp)))))),
             gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _  eqr true n a
                    ((Any.pair mp_src mr_src↑), k_src (fr0, (x, varg_src)))
                    (mp_tgt, f_tgt))
    :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _  eqr m n a
             (mpr_src, (HoareFunArg P varg >>= k_src))
             (mp_tgt, f_tgt)
  .
  Proof.
    inv WF.
    unfold HoareFunArg,  mput, mget, assume, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro x.
    repeat (ired_both; apply sim_itreeC_spec; econs). intros varg_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intros rarg_src.
    repeat (ired_both; apply sim_itreeC_spec; econs). intros VALID.
    repeat (ired_both; apply sim_itreeC_spec; econs). intro PRE.
    ired_both. eapply ARG; et.
    red. econs; ss; cycle 1.
    { instantiate (1:=rarg_src ⋅ mr_src). refl. }
    { ss. rr. uipropall. esplits; et.
      { rewrite URA.unit_id. et. }
      { eapply RSRC; et. eapply URA.wf_mon. instantiate (1:=(rarg_src)). r_wf VALID. }
            { rr. uipropall. }
    }
  Qed.

  Lemma hret_clo
        A (a: shelve__ A) 
         r rg n m mr_src mp_src a0
        X (Q: X -> Any.t -> Any.t -> iProp)
        x vret_src vret_tgt fl_src fl_tgt
        mp_tgt
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        (R: A -> Any.t -> Any.t -> iProp)

        fr0 l
        (ACC: current_iPropL (fr0 ⋅ mr_src) l)

        (WLE: le a0 a)

        (UPDATABLE:
           (from_iPropL l) ⊢ #=> (R a mp_src mp_tgt ** (Q  x vret_src vret_tgt: iProp)))

        (EQ: forall (mr_src1: Σ) (WLE: le a0 a) (WF: mk_wf R a ((Any.pair mp_src mr_src1↑), mp_tgt)),
            eqr ((Any.pair mp_src mr_src1↑)) mp_tgt vret_tgt vret_tgt)
    :
      gpaco8 (_sim_itree (mk_wf R) le fl_src fl_tgt) (cpn8 (_sim_itree (mk_wf R) le fl_src fl_tgt)) r rg _ _  eqr m n a0
             ((Any.pair mp_src mr_src↑), (HoareFunRet Q x (fr0, vret_src)))
             (mp_tgt, (Ret vret_tgt))
  .
  Proof.
    subst. unfold HoareFunRet, mput, mget, guarantee.
    repeat (ired_both; apply sim_itreeC_spec; econs). exists vret_tgt.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    assert (exists mr_src1 rret_src,
               (<<UPDATABLE: URA.updatable (fr0 ⋅ mr_src) (mr_src1 ⋅ rret_src)>>) /\
               (<<RSRC: R a mp_src mp_tgt mr_src1>>) /\
               (<<PRE: Q  x vret_src vret_tgt rret_src>>)).
    { red in ACC. inv ACC. uipropall.
      hexploit (UPDATABLE r0); et.
      { eapply URA.updatable_wf; et. }
      i. des. subst. exists a1, b. splits; et.
      etrans; et.
    }
    des. exists (rret_src, ε, mr_src1).
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits.
    { rewrite URA.unit_id. replace (rret_src ⋅ mr_src1) with (mr_src1 ⋅ rret_src) by r_solve. ss. }
    repeat (ired_both; apply sim_itreeC_spec; econs). unshelve esplits; et.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    eapply EQ; et. econs; et.
  Qed.

  Lemma APC_start_clo
        (at_most: Ord.t) 
        (o: ord)
        A  r rg a m n mp_src0 fl_src fl_tgt
        k_src
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (POST: gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr true n a
                      (mp_src0,
                       (interp_hCallE_tgt  stb o (_APC at_most) ctx)>>= k_src)
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr m n a
             (mp_src0,
              (interp_hCallE_tgt stb o APC ctx) >>= k_src)
             (itr_tgt).
  Proof. 
    subst.  unfold APC. destruct itr_tgt. ired_both.
    (* ired_both. (prw _red_gen 2 1 0). *)
    (* rewrite interp_tgt_bind.
    ired_both.
    rewrite interp_tgt_triggere.
    ired_both. *)
    (* rewrite bind_bind. *)
    (* rewrite bind_bind. *)
    apply sim_itreeC_spec; econs.
    (* eapply sim_itreeC_choose_src. *)
    exists at_most.
    repeat (ired_both; apply sim_itreeC_spec; econs).
    ired_both. et.
    (* Unshelve. all: ss. *)
  Qed.

  Lemma APC_stop_clo
        (o: ord) 
        A  r rg a n m mp_src0 fl_src fl_tgt
        k_src
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt ctx

        (POST: gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr true n a
                      (mp_src0, k_src (ctx, ()))
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr m n a
              (mp_src0,
              (interp_hCallE_tgt  stb o (_APC at_most) ctx) >>= k_src)
             (itr_tgt).
  Proof. 
    subst. destruct itr_tgt.
    rewrite unfold_APC.
    rewrite interp_tgt_bind.  rewrite interp_tgt_triggere. rewrite bind_bind. rewrite bind_bind.
    apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists true. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    rewrite bind_ret_l. simpl. rewrite interp_tgt_ret. 
    ired_both. et.
  Qed.

  Lemma APC_step_clo
        (fn: gname) (args: Any.t) (next: Ord.t)
        
        (o: ord)
        A  r rg a n m mp_src0 fl_src fl_tgt
        k_src ctx0
        (at_most: Ord.t)
        (wf: A -> Any.t * Any.t -> Prop)
        (le: A -> A -> Prop)
        (eqr: Any.t -> Any.t -> Any.t -> Any.t -> Prop)
        stb itr_tgt

        (fsp: fspec)
        (FIND: stb fn = Some fsp)
        (NEXT: (next < at_most)%ord)

        (POST: gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr true n a
                      (mp_src0,
                       ('(ctx1, _) <- (HoareCall true o fsp fn args ctx0);;
                        Tau (ITree.bind (interp_hCallE_tgt  stb o (_APC next) ctx1) k_src)))
                      (itr_tgt))
    :
      gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) r rg _ _ eqr m n a
             (mp_src0, (interp_hCallE_tgt  stb o (_APC at_most) ctx0) >>= k_src)
             (itr_tgt).
  Proof. 
    subst. destruct itr_tgt.
    rewrite unfold_APC.
    rewrite interp_tgt_bind.  rewrite interp_tgt_triggere. rewrite bind_bind. rewrite bind_bind.
    apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists false. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l.
     (* rewrite interp_tgt_bind.  rewrite interp_tgt_triggere. rewrite bind_bind. rewrite bind_bind. *)
    apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists next. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. 
    (* rewrite interp_tgt_bind. rewrite interp_tgt_guarantee. rewrite bind_bind. rewrite bind_bind. *)
    unfold guarantee. ired_l. apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    split.
    { auto. }
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. 
    (* rewrite interp_tgt_bind.  rewrite interp_tgt_triggere. rewrite bind_bind. rewrite bind_bind. *)
    apply sim_itreeC_spec. eapply sim_itreeC_choose_src.
    exists (fn, args).
    ired_l. apply sim_itreeC_spec. eapply sim_itreeC_tau_src.
    ired_l. 
    (* rewrite interp_tgt_bind. rewrite interp_tgt_hcall. rewrite bind_bind. rewrite bind_bind. *)
    ss. rewrite FIND. ss. subst. ired_l.
    match goal with
    | [SIM: gpaco8 _ _ _ _ _ _ _ _ _ _ ?i0 _ |- gpaco8 _ _ _ _ _ _ _ _ _ _ ?i1 _] =>
      replace i1 with i0; et
    end.
    f_equal. grind.
  Qed. *)

  (* Lemma trivial_init_clo
        A wf (le: A -> A -> Prop) r rg w arg mrp_src mp_tgt itr_tgt  stb body RR
        m n
        (INIT:
           gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg Any.t Any.t
                  RR true n w
                  (mrp_src, fun_to_tgt  stb (mk_specbody fspec_trivial body) arg)
                  (mp_tgt, itr_tgt))
    :
      gpaco8 (_sim_itree wf le) (cpn8 (_sim_itree wf le)) r rg Any.t Any.t
             RR m n w
             (mrp_src, KModSem.disclose_ksb_tgt  stb (ksb_trivial body) arg)
             (mp_tgt, itr_tgt).
  Proof.
    unfold KModSem.disclose_ksb_tgt.
    apply sim_itreeC_spec. econs; eauto. i. destruct x; et.
  Qed. *)

End HLEMMAS.


Ltac prep := ired_both.

Ltac _force_l :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapN ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, guarantee ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ guarantee ?P) _ (_, _))) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1

   (* TODO: handle interp_hCallE_tgt better and remove this case *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ITree.bind (interp _ (guarantee ?P )) _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_src; [exists name]|contradict name]; cycle 1; clear name

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_tgt; apply sim_itreeC_spec; econs; unseal i_tgt
  end
.

Ltac _force_r :=
  prep;
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapU ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|exfalso]; cycle 1
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, assume ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    destruct (classic P) as [name|name]; [ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_tgt; [exists name]|contradict name]; cycle 1

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, ?i_src) (_, ?i_tgt)) ] =>
    seal i_src; apply sim_itreeC_spec; econs; unseal i_src
  end
.

Ltac _step :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name
 
  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.

Ltac _step_safe :=
  match goal with
  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, trigger (Choose _) >>= _) (_, ?i_tgt)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerUB >>= _) (_, _)) ] =>
    unfold triggerUB; ired_l; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, unwrapU ?ox >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapU ox) as tvar eqn:thyp; unfold unwrapU in thyp; subst tvar;
    let name := fresh "_UNWRAPU" in
    destruct (ox) eqn:name; [|unfold triggerUB; ired_both; _force_l; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, assume ?P >>= _) (_, _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar;
    let name := fresh "_ASSUME" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_take_src; intro name

  (*** blacklisting ***)
  (* | [ |- (gpaco5 (_sim_itree wf) _ _ _ _ (_, _) (_, trigger (Take _) >>= _)) ] => idtac *)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, triggerNB >>= _) (_, _)) ] =>
    unfold triggerNB; ired_r; _step; done
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, unwrapN ?ox >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (unwrapN ox) as tvar eqn:thyp; unfold unwrapN in thyp; subst tvar;
    let name := fresh "_UNWRAPN" in
    destruct (ox) eqn:name; [|unfold triggerNB; ired_both; _force_r; ss; fail]
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, guarantee ?P >>= _)) ] =>
    let tvar := fresh "tmp" in
    let thyp := fresh "TMP" in
    remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar;
    let name := fresh "_GUARANTEE" in
    ired_both; apply sim_itreeC_spec; eapply sim_itreeC_choose_tgt; intro name
 
  (*** blacklisting ***)
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, trigger (Call _ _) >>= _) (_, _)) ] =>
    try (eapply safe_sim_sim; econs 2); try (eapply safe_sim_sim; econs 5); try (eapply safe_sim_sim; econs 6); try (eapply safe_sim_sim; econs 9) 

  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call _ _) >>= _)) ] =>
    try (eapply safe_sim_sim; econs 2); try (eapply safe_sim_sim; econs 4); try (eapply safe_sim_sim; econs 7); try (eapply safe_sim_sim; econs 8) 

  | _ => (*** default ***)
    eapply safe_sim_sim; econs; i
  end;
  match goal with
  | [ |- exists (_: unit), _ ] => esplits; [eauto|..]; i
  | [ |- exists _, _ ] => fail 1
  | _ => idtac
  end
.


Ltac _steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl).
Ltac steps := repeat ((*** pre processing ***) prep; try _step; (*** post processing ***) simpl; des_ifs_safe).

Ltac _steps_safe := repeat ((*** pre processing ***) prep; try _step_safe; (*** post processing ***) simpl).
Ltac steps_safe := repeat ((*** pre processing ***) prep; try _step_safe; (*** post processing ***) simpl; des_ifs_safe).

Ltac force_l := _force_l.
Ltac force_r := _force_r.



Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) (tgt0, tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' src1 tgt1 '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n ((Any.pair src0 src1), src2) ((Any.pair tgt0 tgt1), tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' src1 '//' tgt1 '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").

Notation "wf n '------------------------------------------------------------------' src0 tgt0 '------------------------------------------------------------------' '------------------------------------------------------------------' src2 tgt2"
  :=
    (gpaco8 (_sim_itree wf _ _ _) _ _ _ _ _ _ _ _ n (src0, src2) (tgt0, tgt2))
      (at level 100,
       format "wf  n '//' '------------------------------------------------------------------' '//' src0 '//' tgt0 '//' '------------------------------------------------------------------' '//' '//' '------------------------------------------------------------------' '//' src2 '//' '//' '//' tgt2 '//' ").


Section TEST.
  Context `{Σ: GRA.t}.
  Let wf := (mk_wf (fun (_ : unit) (_ _ : Any.t) => bi_pure True)).
  Let le := fun (_ _: unit) => True.
  Variable srcs0: Any.t.
  Variable tgts0: Any.t.
  Variable fl_src fl_tgt: alist gname (Any.t -> itree Es Any.t).

  Goal gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt
       (srcs0, triggerUB >>= idK) (tgts0, triggerUB >>= idK).
  Proof.
    steps.
  Qed.

  Goal gpaco8 (_sim_itree wf le fl_src fl_tgt) (cpn8 (_sim_itree wf le fl_src fl_tgt)) bot8 bot8 Any.t Any.t (fun _ _ => eq) false false tt
       (srcs0, triggerNB >>= idK) (tgts0, triggerNB >>= idK).
  Proof.
    steps.
  Qed.

End TEST.

(* 
Ltac astep_full _fn _args _next _n1 :=
  eapply (@APC_step_clo _ _fn _args _next _n1);
  [(try by ((try stb_tac); refl))|
   oauto|
  ].

Ltac astep _fn _args :=
  eapply (@APC_step_clo _ _fn _args);
  [(try by ((try stb_tac); refl))|
   oauto|
  ].

Ltac acatch :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, _) (_, trigger (Call ?fn ?args) >>= _)) ] =>
    astep fn args
  end.

Ltac astart _at_most :=
  eapply (@APC_start_clo _ _at_most)
.

Ltac astop :=
  match goal with
  | [ |- (gpaco8 (_sim_itree _ _ _ _) _ _ _ _ _ _ _ _ _ (_, interp_hCallE_tgt _ _ APC _ >>= _) (_, _)) ] => astart 0
  | _ => idtac
  end;
  eapply APC_stop_clo.

Ltac init :=
  let varg_src := fresh "varg_src" in
  let varg := fresh "varg" in
  let EQ := fresh "EQ" in
  let w := fresh "w" in
  let mrp_src := fresh "mrp_src" in
  let mp_tgt := fresh "mp_tgt" in
  let WF := fresh "WF" in
  split; ss; intros varg_src varg EQ w mrp_src mp_tgt WF;
  try subst varg_src; cbn; ginit;
  try (unfold fun_to_tgt, cfunN, cfunU; rewrite HoareFun_parse); simpl

  .

Ltac harg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  eapply (@harg_clo _ _ PRE INV);
  [eassumption
  |
  ]; i.

Tactic Notation "hret" uconstr(a) :=
  eapply (@hret_clo _ _ a); unshelve_goal;
  [eassumption
  |
  |start_ipm_proof
  |try by (i; (try unfold lift_rel); esplits; et)
  ].

Tactic Notation "hcall" uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo _ Hns POST INV _ x _ a);
  unshelve_goal;
  [eassumption
  |start_ipm_proof
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Tactic Notation "hcall_weaken" uconstr(fsp) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let Hns := select_ihyps Hns in
  eapply (@hcall_clo_weaken _ Hns POST INV fsp x _ a);
  unshelve_goal;
  [
  |eassumption
  |start_ipm_proof
  |
  |on_current ltac:(fun H => try clear H); i; on_current ltac:(fun H => simpl in H)
  ].

Ltac iarg :=
  let PRE := constr:("PRE") in
  let INV := constr:("INV") in
  let CLOSED := constr:("☃CLOSED") in
  eapply (@harg_clo _ _ PRE INV);
  [eassumption
  |
  ];
  i;
  mDesSep PRE as CLOSED PRE;
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ ?w _ _)] =>
    destruct w as [?|[?mp_src ?mp_tgt]]; simpl;
    [
        |mAssertPure False; ss; iDestruct "INV" as "[INV _]"; iApply (inv_closed_unique with "☃CLOSED INV")
    ]
  end.

Tactic Notation "icall_open" uconstr(x) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := constr:("☃CLOSED") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo _ Hns POST INV _ x _ (inr (_, _)));
  unshelve_goal;
  [eassumption
  |start_ipm_proof; iSplitL "☃CLOSED"; [iModIntro; iSplitL "☃CLOSED"; [iExact "☃CLOSED"|ss]|]
  |
  |
  on_current ltac:(fun H => try clear H);
  intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
  on_current ltac:(fun H => simpl in H);
  [exfalso; match goal with | H: inv_le _ _ _ |- _ => cbn in H; inv H end
  |mDesSep "☃CLOSED" as "☃CLOSED" "☃TMP"; mPure "☃TMP" as [[] []]
  ]
  ].

Tactic Notation "icall_weaken" uconstr(ftsp) uconstr(x) uconstr(a) "with" constr(Hns) :=
  let POST := get_fresh_name_tac "POST" in
  let INV := get_fresh_name_tac "INV" in
  let CLOSED := constr:("☃CLOSED") in
  let TMP := constr:("☃TMP") in
  let Hns := select_ihyps Hns in
  let Hns := constr:("☃CLOSED"::Hns) in
  eapply (@hcall_clo_weaken _ Hns POST INV ftsp x _ (inl a));
  unshelve_goal;
  [|eassumption
   |start_ipm_proof; iFrame "☃CLOSED"
   |
   |on_current ltac:(fun H => try clear H);
    intros ? ? ? ? [|[?mp_src ?mp_tgt]]; i; simpl;
    on_current ltac:(fun H => simpl in H);
    [
      mDesSep POST as "☃CLOSED" POST
    |
    mDesSep INV as "☃CLOSED" INV;
    mDesSep POST as "☃TMP" POST;
    mAssertPure False; [iApply (inv_closed_unique with "☃TMP ☃CLOSED")|ss]
    ]
  ].

Tactic Notation "iret" uconstr(a) :=
  eapply (@hret_clo _ _ (inl a)); unshelve_goal;
  [eassumption
  |
  |start_ipm_proof; iFrame "☃CLOSED"
  |try by (i; (try unfold lift_rel); esplits; et)
  ].


Global Opaque _APC APC interp interp_hCallE_tgt.

Global Opaque HoareFun HoareFunArg HoareFunRet HoareCall.

Definition __hide_mark A (a : A) : A := a.
Lemma intro_hide_mark: forall A (a: A), a = __hide_mark a. refl. Qed.

Ltac hide_k :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ (_, ?isrc >>= ?ksrc) (_, ?itgt >>= ?ktgt)) ] =>
    erewrite intro_hide_mark with (a:=ksrc);
    erewrite intro_hide_mark with (a:=ktgt);
    let name0 := fresh "__KSRC__" in set (__hide_mark ksrc) as name0; move name0 at top;
    let name0 := fresh "__KTGT__" in set (__hide_mark ktgt) as name0; move name0 at top
  end.

Ltac unhide_k :=
  do 2 match goal with
  | [ H := __hide_mark _ |- _ ] => subst H
  end;
  rewrite <- ! intro_hide_mark
.

Ltac deflag :=
  match goal with
  | [ |- (gpaco8 _ _ _ _ _ _ _ true true _ _ _) ] =>
    eapply sim_itree_progress_flag
  | [ |- (gpaco8 _ _ _ _ _ _ _ _ _ _ _ _) ] =>
    eapply sim_itree_flag_down
  | _ => fail
  end. *)