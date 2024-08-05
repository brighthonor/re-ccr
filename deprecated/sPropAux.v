From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Import Coqlib PCM PCMAux IProp IPM SRF sProp.
Require Import RobustIndexedInvariants.

Local Notation level := nat.

Module WD.

  Section WD.

  Context `{_W: CtxSL.t}.
  Context `{_W0: @GRA.inG (OwnIsRA SRFSyn.t) Σ}.
  
  Variant shape : Type :=
  | _owni (u: positive) (i: positive)
  .

  Definition degree (s: shape) (sProp: Type) : Type :=
    match s with
    | _owni u i => fin 1
    end.

  Global Instance syntax: PF.t := {
      shp := shape;
      deg := degree;
    }.

  Definition interp n (s: shape) : (degree s (SRFSyn._t n) -> SRFSyn.t n) -> (degree s (SRFSyn._t n) -> iProp) -> iProp :=
    match s with
    | _owni u i => fun p _ => @OwnI _ SRFSyn.t _ u n i (p 0%fin)
    end.

  Global Instance t: SRFMSem.t := interp.

  Context `{_W1: @SRFMSemG.inG _ _ _ t β}.
  
  Definition owni {n} u i (p: SRFSyn.t n) :=
    ⟨ _owni u i, fun _ => p ⟩%SRF.
  
  End WD.

End WD.

Module CtxSLSTWD.
  
  Class t
    `{_C: CtxSLST.t}
    `{_C: @GRA.inG (OwnIsRA SRFSyn.t) Σ}
    `{_C: @SRFMSemG.inG _ _ _ WD.t β}
    := ctxSL: unit.

End CtxSLSTWD.

Module WDRed.
  Section RED.

  Context `{_C: CtxSLSTWD.t}.

  Lemma owni n u i (p: SRFSyn.t n) :
    SRFSem.t n (WD.owni u i p) = OwnI u n i p.
  Proof.
    unfold WD.owni. SRF_red_all. reflexivity.
  Qed.

  End RED.
End WDRed.

Ltac WD_red := (try rewrite ! @WDRed.owni
               ).

Ltac WD_red_all := (try rewrite ! @WDRed.owni in *
                   ).

(***

  Tests

 ***)


Section test.

  Context `{_C: CtxSLSTWD.t}.
  Context `{_U: @GRA.inG OwnEsRA Γ}.
  
  Variable x: SRFSyn.t 3.

  Definition gee: iProp := ⟦ x ⟧.

  Definition foo : SRFSyn.t 0 :=
    (<ownm> maps_to_res 1%positive (@maps_to_res nat CoPset.t 1 (Some ∅))).

End test.

























Section WSATS.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.


  Import Atom.

  (** Definitions for wsat. *)

  Definition syn_inv_auth n (ps : gmap positive (Formula n)) : Atom.t :=
    syn_inv_auth_l (map_to_list ps).

  Lemma red_syn_inv_auth n ps :
    ⟪syn_inv_auth n ps, n⟫ = inv_auth n ps.
  Proof.
    ss. rewrite list_to_map_to_list. ss.
  Qed.

  Definition syn_inv_satall_fun n : positive -> Formula n -> Formula n :=
    fun i p => ((p ∗ ⟨ownd n {[i]}⟩) ∨ ⟨owne n {[i]}⟩)%F.

  Definition syn_inv_satall n (ps : gmap positive (Formula n)) : Formula n :=
    ([∗ n , formulaT map] k ↦ p ∈ ps, syn_inv_satall_fun n k p)%F.

  Lemma red_syn_inv_satall_fun n i p :
    ⟦syn_inv_satall_fun n i p, n⟧ = ((⟦p, n⟧ ∗ (OwnD n {[i]})) ∨ (OwnE n {[i]}))%I.
  Proof.
    unfold syn_inv_satall_fun. red_tl. auto.
  Qed.

  Lemma red_syn_inv_satall n ps :
    ⟦syn_inv_satall n ps, n⟧ = inv_satall n ps.
  Proof.
    ss. unfold syn_inv_satall. rewrite red_tl_big_sepM. ss.
  Qed.

  Definition syn_wsat n : Formula (S n) :=
    (∃ (I : τ{pgmapT Φ, S n}), ⤉(⟨syn_inv_auth n I⟩ ∗ (syn_inv_satall n I)))%F.

  Lemma red_syn_wsat n :
    ⟦syn_wsat n, S n⟧ = wsat n.
  Proof.
    unfold syn_wsat, wsat. red_tl. f_equal. extensionalities I.
    red_tl. rewrite red_syn_inv_auth. rewrite red_syn_inv_satall. auto.
  Qed.

  (** Definitions for wsats. *)

  Fixpoint lifts {n} (p : Formula n) m {struct m} : Formula (m + n) :=
    match m with
    | O => p
    | S m' => (⤉(@lifts n p m'))%F
    end.

  (* Definition syn_wsats n : Formula (S n) := *)
  (*   syn_big_sepL1 n (baseT nat) (seq 0 n) (fun m => lifts (syn_wsat m) (n - (S m))). *)

  Fixpoint lifts_seps (p : forall n, Formula (S n)) n : Formula n :=
    match n with
    | O => emp%F
    | S m => ((⤉(lifts_seps p m)) ∗ (p m))%F
    end.

  Lemma unfold_lifts_seps p n :
    lifts_seps p (S n) = (⤉(lifts_seps p n) ∗ (p n))%F.
  Proof. ss. Qed.

  Lemma red_lifts_seps (p : forall n, Formula (S n)) n :
    ⟦lifts_seps p n, n⟧ = sep_conjs (fun i => ⟦p i, S i⟧) n.
  Proof.
    induction n; ss.
    red_tl. rewrite IHn. auto.
  Qed.

  Definition syn_wsats n : Formula n := lifts_seps syn_wsat n.

  Lemma unfold_syn_wsats n :
    syn_wsats (S n) = (⤉(syn_wsats n) ∗ (syn_wsat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_wsats n :
    ⟦syn_wsats n, n⟧ = wsats n.
  Proof.
    unfold syn_wsats, wsats. replace wsat with (fun i => ⟦syn_wsat i, S i⟧).
    apply red_lifts_seps.
    extensionalities i. apply red_syn_wsat.
  Qed.

  (** Definitions for OwnEs. *)

  Definition syn_owne_satall_fun x : level -> coPset -> (Formula x) :=
    fun n E => ⟨owne n E⟩%F.

  Definition syn_owne_satall x (Es : coPsets) : Formula x :=
    ([∗ x , coPset map] k ↦ E ∈ Es, syn_owne_satall_fun x k E)%F.

  Lemma red_syn_owne_satall x Es :
    ⟦syn_owne_satall x Es, x⟧ = OwnE_satall Es.
  Proof.
    unfold syn_owne_satall. rewrite red_tl_big_sepM. ss.
  Qed.

  Definition syn_ownes x (Es : coPsets) : Formula x :=
    (⟨syn_owne_auth Es⟩ ∗ (syn_owne_satall x Es))%F.

  Lemma red_syn_ownes x Es :
    ⟦syn_ownes x Es, x⟧ = OwnEs Es.
  Proof.
    unfold syn_ownes, OwnEs. red_tl. f_equal. apply red_syn_owne_satall.
  Qed.

  (** Definitions for inv and FUpd. *)

  Definition syn_inv (n : level) (N : namespace) (p : Formula n) : Formula n :=
    (∃ (i : τ{positive}), ⌜i ∈ (nclose N : coPset)⌝ ∧ ⟨owni i p⟩)%F.

  Lemma red_syn_inv n N p :
    ⟦syn_inv n N p, n⟧ = inv n N p.
  Proof.
    done.
  Qed.

  Definition syn_fupd (n : level) (A : Formula n) (Es1 Es2 : coPsets) (p : Formula n) : Formula n :=
    (A ∗ syn_wsats n ∗ syn_ownes _ Es1 -∗ |==> (A ∗ syn_wsats n ∗ syn_ownes _ Es2 ∗ p))%F.

  Lemma red_syn_fupd n A Es1 Es2 p :
    ⟦syn_fupd n A Es1 Es2 p, n⟧ = FUpd n ⟦A, n⟧ Es1 Es2 ⟦p, n⟧.
  Proof.
    Local Transparent FUpd.
    unfold syn_fupd, FUpd. red_tl.
    rewrite ! red_syn_ownes. rewrite ! red_syn_wsats. auto.
    Local Opaque FUpd.
  Qed.

End WSATS.
Global Opaque syn_wsat syn_wsats syn_ownes syn_inv syn_fupd.

Section OBLIG.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Local Notation _dataT := ((nat + id_tgt_type) * nat * Ord.t * Qp * nat)%type.
  Local Notation dataT := (fun (n : level) => (_dataT * Formula n)%type).

  Import Atom.

  Definition syn_obl_arrow n : dataT n -> Formula n :=
    fun '(i, k, c, q, x, f) =>
      ((□ (f -∗ □ f))
         ∗
         ((⟨obl_arrow_done1 x⟩ ∗ ⟨obl_arrow_done2 k⟩ ∗ f)
          ∨
            ⟨obl_arrow_pend i k c q⟩))%F.

  Lemma red_syn_obl_arrow n d :
    ⟦syn_obl_arrow n d, n⟧ = ObligationRA.arrow n d.
  Proof.
    unfold syn_obl_arrow. des_ifs.
  Qed.

  Definition syn_arrows_sat_list n (l : list (dataT n)) : Formula n :=
    syn_sat_list n _ dataT n (syn_obl_arrow n) l.

  Lemma red_syn_arrows_sat_list n l :
    ⟦syn_arrows_sat_list n l, n⟧ = Regions.sat_list _ _ (ObligationRA.arrow n) l.
  Proof.
    unfold syn_arrows_sat_list. rewrite red_tl_sat_list. f_equal.
    extensionalities t. apply red_syn_obl_arrow.
  Qed.

  (* Check (⇣ Ord.t)%ftype. *)
  (* Check (⇣ (nat + nat)%type)%ftype. *)
  (* Fail Check (⇣ (sum_tid id_tgt_type))%ftype. *)

  Definition syn_arrows_sat n : Formula (S n) :=
    (∃ (l : τ{ listT ((⇣(nat + id_tgt_type)) * (⇣nat) * (⇣Ord.t) * (⇣Qp) * (⇣nat) * Φ)%ftype, S n }),
        ⤉(⟨obl_arrows_regions_black l⟩ ∗ syn_arrows_sat_list n l))%F.

  Lemma red_syn_arrows_sat n :
    ⟦syn_arrows_sat n, S n⟧ = ObligationRA.arrows_sat n.
  Proof.
    unfold syn_arrows_sat. red_tl. unfold ObligationRA.arrows_sat, Regions.sat.
    f_equal. extensionality l. red_tl. ss.
    rewrite red_syn_arrows_sat_list. f_equal.
  Qed.

  Definition syn_arrows_sats n : Formula n := lifts_seps syn_arrows_sat n.

  Lemma unfold_syn_arrows_sats n :
    syn_arrows_sats (S n) = (⤉(syn_arrows_sats n) ∗ (syn_arrows_sat n))%F.
  Proof. apply unfold_lifts_seps. Qed.

  Lemma red_syn_arrows_sats n :
    ⟦syn_arrows_sats n, n⟧ = ObligationRA.arrows_sats n.
  Proof.
    unfold syn_arrows_sats, ObligationRA.arrows_sats. unfold Regions.nsats.
    replace (λ i : level, Regions.sat i (ObligationRA.arrows i))
            with (fun i => ⟦syn_arrows_sat i, S i⟧).
    apply red_lifts_seps.
    extensionalities i. apply red_syn_arrows_sat.
  Qed.

  Definition syn_fairI n : Formula n := (⟨obl_edges_sat⟩ ∗ syn_arrows_sats n)%F.

  Lemma red_syn_fairI n :
    ⟦syn_fairI n, n⟧ = fairI n.
  Proof.
    unfold syn_fairI, fairI. red_tl. rewrite red_syn_arrows_sats. ss.
  Qed.

End OBLIG.
Global Opaque syn_obl_arrow syn_arrows_sat_list syn_arrows_sat syn_arrows_sats.

Section SIMI.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  Definition syn_default_I n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> Formula n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (⟨ob_ths ths⟩ ∗ ⟨ob_st_src st_src⟩ ∗ ⟨ob_st_tgt st_tgt⟩ ∗ ⟨fair_src im_src⟩ ∗ ⟨fair_tgt im_tgt ths⟩ ∗ ⟨obl_edges_sat⟩ ∗ syn_arrows_sats n ∗ ⟨obl_arrows_auth n⟩)%F.

  Lemma red_syn_default_I n ths ims imt sts stt :
    ⟦syn_default_I n ths ims imt sts stt, n⟧ = default_I n ths ims imt sts stt.
  Proof.
    unfold syn_default_I, default_I. red_tl. ss.
    rewrite red_syn_arrows_sats. auto.
  Qed.

  Definition syn_default_I_past tid n
    : TIdSet.t -> (@FairBeh.imap id_src_type owf) -> (@FairBeh.imap (nat + id_tgt_type) nat_wf) -> st_src_type -> st_tgt_type -> Formula n :=
    fun ths im_src im_tgt st_src st_tgt =>
      (∃ (im_tgt0 : τ{ ((nat + id_tgt_type)%type -> nat_wfT) }),
          (⌜fair_update im_tgt0 im_tgt (prism_fmap inlp (tids_fmap tid ths))⌝)
            ∗ (syn_default_I n ths im_src im_tgt0 st_src st_tgt))%F.

  Lemma red_syn_default_I_past tid n ths ims imt sts stt :
    ⟦syn_default_I_past tid n ths ims imt sts stt, n⟧ = default_I_past tid n ths ims imt sts stt.
  Proof.
    unfold syn_default_I_past, default_I_past. red_tl. ss.
    f_equal. extensionalities im_tgt0. red_tl. rewrite red_syn_default_I. auto.
  Qed.

  Definition syn_wpsim n tid Es
    : forall {R_src R_tgt : Type}, (R_src -> R_tgt -> Formula n) -> bool -> bool -> itree srcE R_src -> itree tgtE R_tgt -> Formula n
    :=
    fun R_src R_tgt Q ps pt itr_src itr_tgt =>
      (∀ (ths : τ{ tidsetT })
         (im_src : τ{ id_src_type -> owfT })
         (im_tgt : τ{ ((nat + id_tgt_type)%type -> nat_wfT) })
         (st_src : τ{ st_src_type })
         (st_tgt : τ{ st_tgt_type }),
          (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n Es))
            -∗
            (Syntax.sisim tid
                          (fun ths ims imt sts stt =>
                             ((syn_default_I n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
                          (fun ths ims imt sts stt =>
                             ((syn_default_I_past tid n ths ims imt sts stt)
                                ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F)
                          Q ps pt itr_src itr_tgt ths im_src im_tgt st_src st_tgt)
      )%F.

  Lemma red_isim_eq_1 n :
    (λ (ths0 : TIdSet.t) (ims : FairBeh.imap id_src_type owf) (imt : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (sts : st_src_type) (stt : st_tgt_type),
      ⟦ (syn_default_I n ths0 ims imt sts stt ∗ ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ syn_ownes n ∅)%F,
        n ⟧) =
      (λ (ths0 : TIdSet.t) (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
        (default_I n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗ wsats n ∗ OwnEs ∅)%I).
  Proof.
    extensionalities ths0 ims imt sts stt. red_tl.
    rewrite red_syn_default_I. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
  Qed.

  Lemma red_isim_eq_2 tid n rr :
  (λ (R_src R_tgt : Type) (QQ : R_src
                                → R_tgt
                                  → TIdSet.t
                                    → FairBeh.imap id_src_type owf
                                      → FairBeh.imap (sum_tid id_tgt_type) nat_wf
                                        → st_src_type → st_tgt_type → iProp) 
     (ps0 pt0 : bool) (itr_src0 : itree (threadE id_src_type st_src_type) R_src) 
     (itr_tgt : itree (threadE id_tgt_type st_tgt_type) R_tgt) (ths0 : TIdSet.t) 
     (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap 
                                                           (sum_tid id_tgt_type) nat_wf) 
     (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
     (∃ (Q0 : R_src → R_tgt → iProp) (_ : QQ =
                                          (λ (r_src : R_src) (r_tgt : R_tgt) 
                                             (ths1 : TIdSet.t) (im_src1 : 
                                                                FairBeh.imap id_src_type owf) 
                                             (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) 
                                             (st_src1 : st_src_type) 
                                             (st_tgt1 : st_tgt_type),
                                             (default_I_past tid n ths1 im_src1 im_tgt1 st_src1
                                                st_tgt1 ∗ wsat_auth n ∗ 
                                              wsats n ∗ OwnEs ∅) ∗ Q0 r_src r_tgt)),
        rr R_src R_tgt Q0 ps0 pt0 itr_src0 itr_tgt ∗
        default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗ 
        wsats n ∗ OwnEs ∅)%I) =
  (λ (R_src R_tgt : Type) (QQ : R_src
                                → R_tgt
                                  → TIdSet.t
                                    → FairBeh.imap id_src_type owf
                                      → FairBeh.imap (sum_tid id_tgt_type) nat_wf
                                        → st_src_type → st_tgt_type → iProp) 
     (ps0 pt0 : bool) (itr_src0 : itree (threadE id_src_type st_src_type) R_src) 
     (itr_tgt : itree (threadE id_tgt_type st_tgt_type) R_tgt) (ths0 : TIdSet.t) 
     (im_src0 : FairBeh.imap id_src_type owf) (im_tgt0 : FairBeh.imap 
                                                           (sum_tid id_tgt_type) nat_wf) 
     (st_src0 : st_src_type) (st_tgt0 : st_tgt_type),
     (∃ (Q0 : R_src → R_tgt → iProp) (_ : QQ =
                                          (λ (r_src : R_src) (r_tgt : R_tgt) 
                                             (ths1 : TIdSet.t) (im_src1 : 
                                                                FairBeh.imap id_src_type owf) 
                                             (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) 
                                             (st_src1 : st_src_type) 
                                             (st_tgt1 : st_tgt_type),
                                             ⟦ (syn_default_I_past tid n ths1 im_src1 im_tgt1
                                                  st_src1 st_tgt1 ∗ ⟨ syn_wsat_auth n ⟩ ∗
                                                syn_wsats n ∗ syn_ownes n ∅)%F, n ⟧ ∗
                                             Q0 r_src r_tgt)),
        rr R_src R_tgt Q0 ps0 pt0 itr_src0 itr_tgt ∗
        ⟦ (syn_default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ 
                              ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ syn_ownes n ∅)%F, n ⟧)%I).
  Proof.
    extensionalities R_src R_tgt QQ ps0 pt0 itr_src0.
    extensionalities itr_tgt0 ths0 im_src0 im_tgt0 st_src0 st_tgt0.
    f_equal. extensionalities Q0. red_tl.
    rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
    replace
      (λ (r_src : R_src) (r_tgt : R_tgt) (ths1 : TIdSet.t) (im_src1 : 
                                                             FairBeh.imap id_src_type owf) 
         (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src1 : st_src_type) 
         (st_tgt1 : st_tgt_type),
        (⟦ (syn_default_I_past tid n ths1 im_src1 im_tgt1 st_src1 st_tgt1 ∗
                               ⟨ syn_wsat_auth n ⟩ ∗ syn_wsats n ∗ syn_ownes n ∅)%F, n ⟧ ∗ Q0 r_src r_tgt)%I)
      with
      (λ (r_src : R_src) (r_tgt : R_tgt) (ths1 : TIdSet.t) (im_src1 : 
                                                             FairBeh.imap id_src_type owf) 
         (im_tgt1 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src1 : st_src_type) 
         (st_tgt1 : st_tgt_type),
        ((default_I_past tid n ths1 im_src1 im_tgt1 st_src1 st_tgt1 ∗ 
                         wsat_auth n ∗ wsats n ∗ OwnEs ∅) ∗ Q0 r_src r_tgt)%I).
    auto.
    extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
    extensionalities st_src1 st_tgt1.
    red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
  Qed.

  Lemma red_isim_eq_3 RS RT tid n Q :
  (λ (r_src : RS) (r_tgt : RT) (ths0 : TIdSet.t) (ims : FairBeh.imap id_src_type owf) 
     (imt : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (sts : st_src_type) 
     (stt : st_tgt_type),
     (⟦ (syn_default_I_past tid n ths0 ims imt sts stt ∗ ⟨ syn_wsat_auth n ⟩ ∗ 
         syn_wsats n ∗ syn_ownes n ∅)%F, n ⟧ ∗ ⟦ Q r_src r_tgt, n ⟧)%I) =
  (λ (r_src : RS) (r_tgt : RT) (ths0 : TIdSet.t) (im_src0 : FairBeh.imap id_src_type owf) 
     (im_tgt0 : FairBeh.imap (sum_tid id_tgt_type) nat_wf) (st_src0 : st_src_type) 
     (st_tgt0 : st_tgt_type),
     ((default_I_past tid n ths0 im_src0 im_tgt0 st_src0 st_tgt0 ∗ wsat_auth n ∗ 
                      wsats n ∗ OwnEs ∅) ∗ ⟦ Q r_src r_tgt, n ⟧)%I).
  Proof.
    extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
    extensionalities st_src1 st_tgt1.
    red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
  Qed.

  Lemma red_syn_wpsim
        n tid Es RS RT (Q : RS -> RT -> Formula n) ps pt itr_src itr_tgt :
    ⟦syn_wpsim n tid Es Q ps pt itr_src itr_tgt, n⟧
      =
      wpsim n tid Es ibot7 ibot7 (fun rs rt => ⟦Q rs rt, n⟧) ps pt itr_src itr_tgt.
  Proof.
    unfold syn_wpsim, wpsim. red_tl. simpl.
    f_equal. extensionalities ths. red_tl.
    f_equal. extensionalities im_src. red_tl.
    f_equal. extensionalities im_tgt. red_tl.
    f_equal. extensionalities st_src. red_tl.
    f_equal. extensionalities st_tgt. red_tl.
    rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
    f_equal. unfold isim_simple.
    f_equal; ss.
    - apply red_isim_eq_1.
    - unfold ibot7. symmetry. apply red_isim_eq_2.
    - unfold ibot7. symmetry. apply red_isim_eq_2.
    - apply red_isim_eq_3.
  Qed.



  (* State interp with lens. *)
  Definition syn_view_interp n {S V} (l : Lens.t S V) (SI : S -> Formula n) (VI : V -> Formula n) : Prop :=
    forall s, ⟦SI s , n⟧ ⊢ ( ⟦VI (Lens.view l s), n⟧ ∗ ∀ x, ⟦VI x, n⟧ -∗ ⟦SI (Lens.set l x s), n⟧ ).

  Definition syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> Formula n) : Formula (S n) :=
    (∃ (SI : τ{(st_src_type -> Φ)%ftype, S n}) (p : τ{Φ, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_src st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_src p)) ∗ ⌜syn_view_interp n l SI VI⌝)%F.

  Lemma red_syn_src_interp_as n {V} (l: Lens.t st_src_type V) (VI: V -> Formula n) :
    ⟦syn_src_interp_as n l VI, S n⟧ = (src_interp_as l VI).
  Proof.
    unfold syn_src_interp_as. unfold src_interp_as.
    red_tl. ss. f_equal. extensionalities SI.
    red_tl. ss. f_equal. extensionalities p.
    red_tl. ss. repeat f_equal. unfold syn_view_interp.
    apply propositional_extensionality. split; i.
    - econs. auto.
    - inv H. auto.
  Qed.

  Definition syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> Formula n) : Formula (S n) :=
    (∃ (SI : τ{(st_tgt_type -> Φ)%ftype, S n}) (p : τ{Φ, S n}),
        (⌜⟦p, n⟧ = (∃ st, St_tgt st ∗ ⟦(SI st), n⟧)%I⌝)
          ∗ (⤉(syn_inv n N_state_tgt p)) ∗ ⌜syn_view_interp n l SI VI⌝)%F.

  Lemma red_syn_tgt_interp_as n {V} (l: Lens.t st_tgt_type V) (VI: V -> Formula n) :
    ⟦syn_tgt_interp_as n l VI, S n⟧ = (tgt_interp_as l VI).
  Proof.
    unfold syn_tgt_interp_as. unfold tgt_interp_as.
    red_tl. ss. f_equal. extensionalities SI.
    red_tl. ss. f_equal. extensionalities p.
    red_tl. ss. repeat f_equal. unfold syn_view_interp.
    apply propositional_extensionality. split; i.
    - econs. auto.
    - inv H. auto.
  Qed.

End SIMI.
Global Opaque
       syn_default_I syn_default_I_past syn_wpsim
       syn_src_interp_as syn_tgt_interp_as.

Section TRIPLE.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Let srcE := threadE id_src_type st_src_type.
  Let tgtE := threadE id_tgt_type st_tgt_type.

  Import Atom.

  (* Definition syn_triple_gen *)
  (*            n tid (P : Formula n) {RV} (Q : RV -> Formula n) (Es1 Es2 : coPsets) *)
  (*   : forall {R_src R_tgt : Type} (TERM : R_src -> R_tgt -> Formula n), bool -> bool -> itree srcE R_src -> itree tgtE RV -> ktree tgtE RV R_tgt -> Formula n *)
  (*   := *)
  (*   fun R_src R_tgt TERM ps pt itr_src code ktr_tgt => *)
  (*     ( *)
  (*       (* let N := (S n) in *) *)
  (*       let I0 := (fun ths ims imt sts stt => ((syn_default_I n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F) *)
  (*      in *)
  (*      let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid n ths ims imt sts stt) ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n ∅))%F) *)
  (*      in *)
  (*      let I2 := (fun ths im_src im_tgt st_src st_tgt Es => (syn_default_I_past tid n ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth n⟩ ∗ syn_wsats n ∗ syn_ownes n Es))) *)
  (*      in *)
  (*      Syntax.striple_format tid I0 I1 I2 P Q Es1 Es2 TERM ps pt itr_src code ktr_tgt)%F. *)

  Definition syn_term_cond n (tid : thread_id) (R_term : Type) : R_term -> R_term -> Formula n :=
    fun rs rt => ((⟨ow_ths tid⟩ ∗ ⟨obl_duty inlp tid []⟩) ∗ (⌜rs = rt⌝))%F.

  Lemma red_syn_term_cond n tid R_term :
    (fun (rs rt : R_term) => ⟦syn_term_cond n tid R_term rs rt, n⟧)
    =
      (term_cond n tid (R_term:=R_term)).
  Proof.
    extensionalities rs rt. unfold syn_term_cond. red_tl. f_equal.
  Qed.

  Definition syn_triple_gen
             n tid (P : Formula (S n)) {RV} (Q : RV -> Formula (S n)) (Es1 Es2 : coPsets)
    : forall {R_term : Type}, bool -> bool -> itree srcE R_term -> itree tgtE RV -> ktree tgtE RV R_term -> Formula (S n)
    :=
    fun R_term ps pt itr_src code ktr_tgt =>
      (let N := (S n) in
        let I0 := (fun ths ims imt sts stt => ((syn_default_I N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ syn_ownes N ∅))%F)
       in
       let I1 := (fun ths ims imt sts stt => ((syn_default_I_past tid N ths ims imt sts stt) ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ syn_ownes N ∅))%F)
       in
       let I2 := (fun ths im_src im_tgt st_src st_tgt Es => (syn_default_I_past tid N ths im_src im_tgt st_src st_tgt ∗ (⟨syn_wsat_auth N⟩ ∗ syn_wsats N ∗ syn_ownes N Es)))
       in
       Syntax.striple_format tid I0 I1 I2 P Q Es1 Es2 (fun rs rt => ⤉ (syn_term_cond n tid R_term rs rt)) ps pt itr_src code ktr_tgt)%F.

  Lemma red_syn_triple_gen
        n tid (P : Formula (S n)) RV (Q : RV -> Formula (S n)) Es1 Es2
        R_term ps pt itr_src code (ktr_tgt : ktree tgtE RV R_term)
    :
    ⟦syn_triple_gen n tid P Q Es1 Es2 ps pt itr_src code ktr_tgt, S n⟧
    =
      triple_gen (S n) n tid ⟦P, S n⟧ (fun rv => ⟦Q rv, S n⟧) Es1 Es2 ps pt itr_src code ktr_tgt.
  Proof.
    unfold syn_triple_gen, triple_gen. red_tl. unfold triple_format.
    apply f_equal. extensionalities rr. apply f_equal. extensionalities gr.
    apply f_equal.
    match goal with
    | [ |- (?A -∗ _)%I = (?B -∗ _)%I] => replace A with B
    end.
    match goal with
    | [ |- (_ -∗ ?C)%I = (_ -∗ ?D)%I] => replace C with D
    end.
    auto.
    - unfold wpsim.
      apply f_equal. extensionalities ths.
      apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt.
      apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt.
      red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
      f_equal. f_equal.
      + symmetry. apply (red_isim_eq_1 (S n)).
      + apply (red_isim_eq_2 _ (S n)).
      + apply (red_isim_eq_2 _ (S n)).
      + symmetry.
        extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
        extensionalities st_src1 st_tgt1.
        red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
    - apply f_equal. extensionalities rv. apply f_equal.
      unfold wpsim.
      apply f_equal. extensionalities ths.
      apply f_equal. extensionalities im_src. apply f_equal. extensionalities im_tgt.
      apply f_equal. extensionalities st_src. apply f_equal. extensionalities st_tgt.
      red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes.
      f_equal. f_equal.
      + symmetry. apply (red_isim_eq_1 (S n)).
      + apply (red_isim_eq_2 _ (S n)).
      + apply (red_isim_eq_2 _ (S n)).
      + symmetry.
        extensionalities r_src r_tgt ths1 im_src1 im_tgt1.
        extensionalities st_src1 st_tgt1.
        red_tl. rewrite red_syn_default_I_past. rewrite red_syn_wsats. rewrite red_syn_ownes. ss.
  Qed.

  Definition syn_atomic_triple
             tid n (Es : coPsets)
             (P : Formula (S n)) {RV} (code : itree tgtE RV) (Q : RV -> Formula (S n))
    : Formula (S n)
    :=
    (∀ (R_term : τ{metaT})
       (* (TERM : τ{(R_src -> R_tgt -> Φ)%ftype, n}) *)
       (ps pt : τ{bool})
       (itr_src : τ{codeT id_src_type st_src_type R_term, S n})
       (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%ftype, S n}),
        (syn_triple_gen n tid P Q Es Es ps pt itr_src code ktr_tgt))%F.

  Lemma red_syn_atomic_triple
        tid n (Es : coPsets)
        (P : Formula (S n)) RV (code : itree tgtE RV) (Q : RV -> Formula (S n))
    :
    ⟦syn_atomic_triple tid n Es P code Q, S n⟧
    =
      atomic_triple tid n Es ⟦P, S n⟧ code (fun v => ⟦Q v, S n⟧).
  Proof.
    unfold syn_atomic_triple, atomic_triple. red_tl.
    apply f_equal. extensionalities R_term. red_tl.
    apply f_equal. extensionalities ps. red_tl.
    apply f_equal. extensionalities pt. red_tl.
    apply f_equal. extensionalities itr_src. red_tl.
    apply f_equal. extensionalities itr_tgt. red_tl.
    apply red_syn_triple_gen.
  Qed.

  Definition syn_non_atomic_triple
             tid n (Es : coPsets)
             (P : Formula (S n)) {RV} (code : itree tgtE RV) (Q : RV -> Formula (S n))
    : Formula (S n)
    :=
    (∀ (R_term : τ{metaT})
       (ps pt : τ{bool})
       (itr_src : τ{codeT id_src_type st_src_type R_term})
       (ktr_tgt : τ{(RV -> codeT id_tgt_type st_tgt_type R_term)%ftype, S n}),
        (syn_triple_gen n tid P Q Es ∅ ps pt (trigger Yield;;; itr_src) code ktr_tgt))%F.

  Lemma red_syn_non_atomic_triple
        tid n (Es : coPsets)
        (P : Formula (S n)) RV (code : itree tgtE RV) (Q : RV -> Formula (S n))
    :
    ⟦syn_non_atomic_triple tid n Es P code Q, S n⟧
    =
      non_atomic_triple tid n Es ⟦P, S n⟧ code (fun v => ⟦Q v, S n⟧).
  Proof.
    unfold syn_non_atomic_triple, non_atomic_triple. red_tl.
    apply f_equal. extensionalities R_term. red_tl.
    apply f_equal. extensionalities ps. red_tl.
    apply f_equal. extensionalities pt. red_tl.
    apply f_equal. extensionalities itr_src. red_tl.
    apply f_equal. extensionalities itr_tgt. red_tl.
    apply red_syn_triple_gen.
  Qed.

End TRIPLE.

Section DERIV.

  Context {AA : AuxAtom}.
  Context {STT : StateTypes}.

  Context `{Σ : GRA.t}.
  Context `{AAI : @AAInterp Σ AA}.
  Context {TLRAS : @TLRAs AA STT Σ}.

  Import Atom.

  Definition syn_until_promise {Id} {n} (p : Prism.t _ Id) (i : Id) k l (f P : Formula n) :=
    (⟨obl_promise p i k l f⟩ ∗ (P ∨ (□ f)))%F.

  Definition syn_until_tpromise {n} k l (f P : Formula n) :=
    (⟨obl_tpromise k l f⟩ ∗ (P ∨ (□ f)))%F.

  Lemma red_syn_until_promise
        {Id} n (p : Prism.t _ Id) (i : Id) k l (f P : Formula n) :
    ⟦syn_until_promise p i k l f P, n⟧ = until_promise p i k l f P.
  Proof.
    unfold syn_until_promise. red_tl. f_equal.
  Qed.

  Lemma red_syn_until_tpromise
        n k l (f P : Formula n) :
    ⟦syn_until_tpromise k l f P, n⟧ = until_thread_promise k l f P.
  Proof.
    unfold syn_until_tpromise. red_tl. f_equal.
  Qed.

End DERIV.

(** Notations. *)

(* Fancy update. *)
Notation "'=|' x '|=(' A ')={' Es1 ',' Es2 '}=>' P" := (syn_fupd x A Es1 Es2 P) (at level 90) : formula_scope.
Notation "'=|' x '|={' Es1 ',' Es2 '}=>' P" := (=|x|=( ⌜True⌝%F )={ Es1, Es2}=> P)%F (at level 90) : formula_scope.
Notation "P =| x |=( A )={ Es1 , Es2 }=∗ Q" := (P -∗ =|x|=(A)={Es1,Es2}=> Q)%F (at level 90) : formula_scope.
Notation "P =| x |={ Es1 , Es2 }=∗ Q" := (P -∗ =|x|={Es1,Es2}=> Q)%F (at level 90) : formula_scope.

Notation "'=|' x '|=(' A ')={' Es '}=>' P" := (syn_fupd x A Es Es P) (at level 90) : formula_scope.
Notation "'=|' x '|={' Es '}=>' P" := (=|x|=( ⌜True⌝%F )={ Es }=> P)%F (at level 90) : formula_scope.
Notation "P =| x |=( A )={ Es }=∗ Q" := (P -∗ =|x|=(A)={Es}=> Q)%F (at level 90) : formula_scope.
Notation "P =| x |={ Es }=∗ Q" := (P -∗ =|x|={Es}=> Q)%F (at level 90) : formula_scope.

(* State. *)
Notation "'TID' ( tid )" :=
  (⟨Atom.ow_ths tid⟩)%F (at level 50, tid at level 1, format "TID ( tid )") : formula_scope.

(* Liveness logic. *)
Notation "'◆' [ k , l ]" :=
  (⟨Atom.obl_lo k l⟩)%F (at level 50, k, l at level 1, format "◆ [ k ,  l ]") : formula_scope.
Notation "'◇' [ k ]( l , a )" :=
  (⟨Atom.obl_pc k l a⟩)%F (at level 50, k, l, a at level 1, format "◇ [ k ]( l ,  a )") : formula_scope.
Notation "'live[' k ']' q " :=
  (⟨Atom.obl_live k q⟩)%F (at level 50, k, q at level 1, format "live[ k ] q") : formula_scope.
Notation "'dead[' k ']'" :=
  (⟨Atom.obl_dead k⟩)%F (at level 50, k at level 1, format "dead[ k ]") : formula_scope.
Notation "s '-(' l ')-' '◇' t" :=
  (⟨Atom.obl_link s t l⟩)%F (at level 50, l, t at level 1, format "s  -( l )- ◇  t") : formula_scope.
Notation "'Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_duty p i ds⟩)%F (at level 50, p, i, ds at level 1, format "Duty ( p  ◬  i )  ds") : formula_scope.
Notation "'Duty' ( tid ) ds" :=
  (⟨Atom.obl_duty inlp tid ds⟩)%F (at level 50, tid, ds at level 1, format "Duty ( tid )  ds") : formula_scope.
Notation "'€' ( p ◬ i )" :=
  (⟨Atom.obl_fc p i⟩)%F (format "€ ( p  ◬  i )") : formula_scope.
Notation "'-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_promise p i k l f⟩)%F (at level 50, k, l, p, i at level 1, format "-( p  ◬  i )-[ k ]( l )- ◇  f") : formula_scope.
Notation "'€'" :=
  (⟨Atom.obl_tc⟩)%F : formula_scope.
Notation "'-[' k '](' l ')-' '◇' f" :=
  (⟨Atom.obl_tpromise k l f⟩)%F (at level 50, k, l at level 1, format "-[ k ]( l )- ◇  f") : formula_scope.
Notation "'◇' { ps }( m , a )" :=
  (⟨Atom.obl_pcs ps m a⟩)%F (at level 50, ps, m, a at level 1, format "◇ { ps }( m ,  a )") : formula_scope.
Notation "⦃ '◆' [ k ] & '◇' { ps }( l )⦄" :=
  (⟨Atom.obl_ccs k ps l⟩)%F (at level 50, k, ps, l at level 1, format "⦃ ◆ [ k ]  &  ◇ { ps }( l )⦄") : formula_scope.
Notation "P '-U-(' p ◬ i ')-[' k '](' l ')-' '◇' f" :=
  (syn_until_promise p i k l f P)%F (at level 50, k, l, p, i at level 1, format "P  -U-( p  ◬  i )-[ k ]( l )- ◇  f") : formula_scope.
Notation "P '-U-[' k '](' l ')-' '◇' f" :=
  (syn_until_tpromise k l f P) (at level 50, k, l at level 1, format "P  -U-[ k ]( l )- ◇  f") : formula_scope.

Notation "'●Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_share_duty_b p i ds⟩)%F (at level 50, p, i, ds at level 1, format "●Duty ( p  ◬  i )  ds") : formula_scope.
Notation "'○Duty' ( p ◬ i ) ds" :=
  (⟨Atom.obl_share_duty_w p i ds⟩)%F (at level 50, p, i, ds at level 1, format "○Duty ( p  ◬  i )  ds") : formula_scope.
Notation "'●Duty' ( tid ) ds" :=
  (⟨Atom.obl_share_duty_b inlp tid ds⟩)%F (at level 50, tid, ds at level 1, format "●Duty ( tid )  ds") : formula_scope.
Notation "'○Duty' ( tid ) ds" :=
  (⟨Atom.obl_share_duty_w inlp tid ds⟩)%F (at level 50, tid, ds at level 1, format "○Duty ( tid )  ds") : formula_scope.

(* Auxiliary. *)
Notation "l '@1'" := (List.map fst l) (at level 50, format "l @1") : formula_scope.

(* Triples. *)
Notation "'[@' tid , n , Es '@]' { P } code { v , Q }" :=
  (syn_atomic_triple tid n Es P code (fun v => Q))
    (at level 200, tid, n, Es, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  Es  @] { P }  code  { v ,  Q }") : formula_scope.

Notation "'[@' tid , n , Es '@]' ⧼ P ⧽ code ⧼ v , Q ⧽" :=
  (syn_non_atomic_triple tid n Es P code (fun v => Q))
    (at level 200, tid, n, Es, P, code, v, Q at level 1,
      format "[@  tid ,  n ,  Es  @] ⧼ P ⧽  code  ⧼ v ,  Q ⧽") : formula_scope.
