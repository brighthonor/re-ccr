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



Section SIM.

	Context `{Σ: GRA.t}.

	(* Variable world: Type.
	Variable le: relation world. *)
	(* Variable I: world -> Any.t -> Any.t -> iProp. *)

	(* Variable stb: gname -> option fspec. *)

	(* Variable o: ord. *)

	(* Variable σ: Σ.
	Variable I: iProp.
	
	Check I σ. *)

	Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
	Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
	Variable I: Any.t -> Any.t -> iProp.
  (* Variable Any.t Any.t: Type. *)
  
  (* Print iProp.
  Print URA.t. *)
	(* Print current_iProp. *)

	
	Inductive _hpsim
	(hpsim: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop)
		: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop :=
	| hpsim_ret
			f_src f_tgt st_src st_tgt fmr
			v_src v_tgt
			(RET: (Own fmr ⊢ #=> I st_src st_tgt))
		:
			_hpsim hpsim f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr

	| hpsim_call
			f_src f_tgt st_src st_tgt fmr
			fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
			(K: forall vret st_src0 st_tgt0 fmr0
          (INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
				_hpsim hpsim true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0)				
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

	| hpsim_syscall
			f_src f_tgt st_src st_tgt fmr
			fn varg rvs k_src k_tgt
			(K: forall vret, 
				_hpsim hpsim true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr

	| hpsim_inline_src
			f_src f_tgt st_src st_tgt fmr
			fn f varg k_src i_tgt
			(FUN: alist_find fn fl_src = Some f)
			(K: _hpsim hpsim true f_tgt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt) fmr)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_inline_tgt
			f_src f_tgt st_src st_tgt fmr
			fn f varg i_src k_tgt
		  (FUN: alist_find fn fl_tgt = Some f)
		  (K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr

	| hpsim_tau_src
			f_src f_tgt st_src st_tgt fmr
		  i_src i_tgt
  		(K: _hpsim hpsim true f_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr

	| hpsim_tau_tgt
			f_src f_tgt st_src st_tgt fmr
		  i_src i_tgt
		  (K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr

	| hpsim_choose_src
			f_src f_tgt st_src st_tgt fmr
		  X x k_src i_tgt
		  (K: _hpsim hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
  	:
	  	_hpsim hpsim f_src f_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_choose_tgt
			f_src f_tgt st_src st_tgt fmr
		  X i_src k_tgt
		  (K: forall (x: X), _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr

	| hpsim_take_src
			f_src f_tgt st_src st_tgt fmr
		  X k_src i_tgt
		  (K: forall (x: X), _hpsim hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_take_tgt
			f_src f_tgt st_src st_tgt fmr
		  X x i_src k_tgt
		  (K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr

	| hpsim_supdate_src
			f_src f_tgt st_src st_tgt fmr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
		  (K: _hpsim hpsim true f_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_supdate_tgt
			f_src f_tgt st_src st_tgt fmr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
		  (K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
	  :
		  _hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr

	| hpsim_assume_src
			f_src f_tgt st_src st_tgt fmr
			iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
			(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
			(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

	| hpsim_guarantee_src
			f_src f_tgt st_src st_tgt fmr
			iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
			(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_guarantee_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
			(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr

	| hpsim_progress
  		st_src st_tgt fmr
      i_src i_tgt
  		(SIM: hpsim false false (st_src, i_src) (st_tgt, i_tgt) fmr)
  	:
  		_hpsim hpsim true true (st_src, i_src) (st_tgt, i_tgt) fmr
	.

		Definition hpsim := paco5 _hpsim bot5.

		Lemma _hpsim_mon: monotone5 _hpsim.
		Proof. 
			ii. induction IN;
			try (econs; et; ii; exploit K; i; des; et).
		Qed.
	
		Hint Constructors _hpsim.
		Hint Unfold hpsim.
		Hint Resolve _hpsim_mon: paco.
		Hint Resolve cpn5_wcompat: paco.

		Lemma hpsim_ind
				(P: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop)
		
		(RET: forall
				f_src f_tgt st_src st_tgt fmr
				v_src v_tgt
				(RET: (Own fmr ⊢ #=> I st_src st_tgt) ),
				P f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr)
		(CALL: forall
				f_src f_tgt st_src st_tgt fmr
				fn varg k_src k_tgt FR
				(INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
				(K: forall vret st_src0 st_tgt0 fmr0
						(INV: Own fmr0 ⊢ #=> (I st_src0 st_tgt0 ** FR)),
						<<SIM: hpsim true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0>> /\
						<<IH: P true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0>>),
				P f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr)
		(SYSCALL: forall
				f_src f_tgt st_src st_tgt fmr
				fn varg rvs k_src k_tgt
				(K: forall vret,
						<<SIM: hpsim true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr>> /\ 
						<<IH: P true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr>>),
				P f_src f_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr)
		(INLINESRC: forall
				f_src f_tgt st_src st_tgt fmr
				fn f varg k_src i_tgt
				(FUN: alist_find fn fl_src = Some f)
				(K: hpsim  true f_tgt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt) fmr)
				(IH: P true f_tgt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt) fmr),
				P f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr)
		(INLINETGT: forall
				f_src f_tgt st_src st_tgt fmr
				fn f varg i_src k_tgt
				(FUN: alist_find fn fl_tgt = Some f)
				(K: hpsim f_src true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt) fmr)
				(IH: P f_src true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt) fmr),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr)
		(TAUSRC: forall
				f_src f_tgt st_src st_tgt fmr
				i_src i_tgt
				(K: hpsim true f_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
				(IH: P true f_tgt (st_src, i_src) (st_tgt, i_tgt) fmr),
				P f_src f_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr)
		(TAUTGT: forall
				f_src f_tgt st_src st_tgt fmr
				i_src i_tgt
				(K: hpsim f_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
				(IH: P f_src true (st_src, i_src) (st_tgt, i_tgt) fmr),
				P f_src f_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr)
		(CHOOSESRC: forall
				f_src f_tgt st_src st_tgt fmr
				X x k_src i_tgt
				(K: hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
				(IH: P true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr),
				P f_src f_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr)
		(CHOOSETGT: forall
				f_src f_tgt st_src st_tgt fmr
				X i_src k_tgt
				(K: forall (x: X), 
						<<SIM: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr>> /\
						<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr>>),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr)
		(TAKESRC: forall
				f_src f_tgt st_src st_tgt fmr
				X k_src i_tgt
				(K: forall (x: X), 
						<<SIM: hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr>> /\
						<<IH: P true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr>>),
				P f_src f_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr)
		(TAKETGT: forall
				f_src f_tgt st_src st_tgt fmr
				X x i_src k_tgt
				(K: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
				(IH: P f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr)
		(SUPDATESRC: forall
				f_src f_tgt st_src st_tgt fmr
				X x st_src0 k_src i_tgt
				(run: Any.t -> Any.t * X)
				(RUN: run st_src = (st_src0, x))
				(K: hpsim true f_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
				(IH: P true f_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr),
				P f_src f_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr)
		(SUPDATETGT: forall
				f_src f_tgt st_src st_tgt fmr
				X x st_tgt0 i_src k_tgt
				(run: Any.t -> Any.t * X)
				(RUN: run st_tgt = (st_tgt0, x))
				(K: hpsim f_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
				(IH: P f_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr)
		(ASSUMESRC: forall
				f_src f_tgt st_src st_tgt fmr
				iP k_src i_tgt FMR
				(CUR: Own fmr ⊢ #=> FMR)
				(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(ASSUMETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: Own fmr ⊢ #=> (iP ** FMR))
				(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> FMR),
						<<SIM: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
						<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr)
		(GUARANTEESRC: forall
				f_src f_tgt st_src st_tgt fmr
				iP k_src i_tgt FMR
				(CUR: Own fmr ⊢ #=> (iP ** FMR))
				(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> FMR),
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(GUARANTEETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: Own fmr ⊢ #=> FMR)
				(K: forall fmr0 (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
						<<SIM: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
						<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr)
		(PROGRESS: forall
				st_src st_tgt fmr
				i_src i_tgt
				(SIM: hpsim false false (st_src, i_src) (st_tgt, i_tgt) fmr),
				P true true (st_src, i_src) (st_tgt, i_tgt) fmr)
		:
				forall f_src f_tgt st_src st_tgt fmr
				(SIM: hpsim f_src f_tgt st_src st_tgt fmr),
				P f_src f_tgt st_src st_tgt fmr.
	Proof. 
    i. punfold SIM. induction SIM.
			{ eapply RET; eauto. }
			{ eapply CALL; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply SYSCALL; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply INLINESRC; eauto. }
			{ eapply INLINETGT; eauto. }
			{ eapply TAUSRC; eauto. }
			{ eapply TAUTGT; eauto. }
			{ eapply CHOOSESRC; eauto. }
			{ eapply CHOOSETGT; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply TAKESRC; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply TAKETGT; eauto. }
			{ eapply SUPDATESRC; eauto. }
			{ eapply SUPDATETGT; eauto. }
			{ eapply ASSUMESRC; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply ASSUMETGT; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply GUARANTEESRC; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply GUARANTEETGT; eauto. i. hexploit K; et. i. des. esplits; et. }
			{ eapply PROGRESS; eauto. pclearbot. et. }
	Qed.

	Lemma hpsim_bot_flag_up f_src f_tgt st_src st_tgt fmr
			(SIM: paco5 _hpsim bot5 true true st_src st_tgt fmr)
		:
			paco5 _hpsim bot5 f_src f_tgt st_src st_tgt fmr
	.
	Proof.
		(* ginit. 
		do 2 remember true in SIM at 1.
		clear Heqb Heqb0. 
		revert_until I.
		gcofix CIH.
		i. revert f_src f_tgt.
		pattern b, b0, st_src, st_tgt, fmr.
		match goal with
		| |- ?P b b0 st_src st_tgt fmr => set P
		end.
		revert b b0 st_src st_tgt fmr SIM.
		eapply (@hpsim_ind P); subst P; ss; i; clarify.
		{ gstep. econs; et. }
		{ gstep. econs; et. i. hexploit K; et. i. des. econs. gfinal. left. eapply CIH. et. }
		{ gstep. econs; et. i. hexploit K; et. i. des. econs. gfinal. left. eapply CIH. et. } *)
	Admitted.	

	Lemma current_iProp_sepconj P Q r 
			(SAT: current_iProp r (P ** Q))
		:
			exists rp rq, URA.updatable r (rp ⋅ rq) /\ current_iProp rp P /\ current_iProp rq Q
	.
	Proof.
		destruct SAT. rr in IPROP. uipropall. des. clarify.
		hexploit UPD. i. eapply URA.updatable_wf in H; et. des.
		esplits; et; econs; et; r_solve.
		- eapply URA.wf_mon in H. et.
		- eapply URA.wf_extends in H; et. econs. instantiate (1:= a). r_solve.
	Qed.

	Lemma own_update a b
			(OWN: Own a ⊢ #=> Own b)
		:
			forall ctx, Own (a ⋅ ctx) ⊢ #=> Own (b ⋅ ctx)
	.
	Proof.
		i. iIntros "[H H0]".
		iPoseProof (OWN with "H") as "H".
		iSplitL "H"; et.
	Qed.

	Lemma own_updatable (r r': Σ)
			(UPD: URA.updatable r r')
		:
			Own r ⊢ #=> Own r'
		.
	Proof.
		unfold URA.updatable in *. uipropall.
		i. exists r'.
		esplits; et. { admit. }
		i. apply UPD. revert ctx H0.
		eapply URA.extends_updatable. et.
	Qed.

	Lemma iProp_sepconj P Q r 
			(SAT: Own r ⊢ #=> (P ** Q))
			(WF: URA.wf r)
		:
			exists rp rq, (Own r ⊢ #=> Own (rp ⋅ rq)) /\ 
			(* exists rp rq, (URA.updatable r (rp ⋅ rq)) /\  *)
										(Own rp ⊢ P) /\ 
										(Own rq ⊢ Q)
	.
	Proof.
		uipropall.
		hexploit SAT; et. { admit. }
		i. des.
		esplits; uipropall.
		{
			instantiate (1:= b). instantiate (1:= a).
			unfold URA.updatable. 
			rewrite H in H0. et.
		}
		{
			i. destruct P. ss.
			assert (URA.wf a). { admit. }
			specialize (iProp_mono a r0 WF0 H3 H1). et. 	
		}
		{
			i. 
			i. destruct Q. ss.
			assert (URA.wf b). { admit. }
			specialize (iProp_mono b r0 WF0 H3 H2). et. 
		}

		
	Admitted.
		(* autounfold with iprop in SAT. *)
		(* uipropall.
		hexploit SAT; et. r_solve. 
		i. des.
		esplits.
		{  }
	{ uipropall. i. hexploit SAT; et.
			i. 
		} *)

	Lemma current_iProp_sepconj' P Q r 
			(SAT: current_iProp r (P ** Q))
		:
			exists rp rq, URA.updatable r (rp ⋅ rq) /\ P rp /\ Q rq
	.
	Proof.
		destruct SAT. rr in IPROP. uipropall. des. clarify.
		hexploit UPD. i. eapply URA.updatable_wf in H; et. 
	Qed.

	Lemma current_iProp_sepconj_r P Q r 
			(SAT: current_iProp r (P ** Q))
		:
			exists rp rq, URA.updatable r (rp ⋅ rq) /\ P rp /\ current_iProp rq Q
	.
	Proof.
		destruct SAT. rr in IPROP. uipropall. des. clarify.
		hexploit UPD. i. eapply URA.updatable_wf in H; et. 
		esplits; et; econs; et; r_solve.
		des. eapply URA.wf_extends; et. econs. instantiate (1:= a). r_solve.
	Qed.

	Lemma current_iProp_conj P Q x y
			(IP: current_iProp x P)
			(IQ: current_iProp y Q)
			(WF: URA.wf (x ⋅ y))
	:
			current_iProp (x ⋅ y) (P ** Q)
	.
	Proof. 
		inv IP. inv IQ.
		econs; et.
		{ uipropall. esplits; et. }
		eapply URA.updatable_add; et.
	Qed.


  Lemma current_iPropL_convert fmr P
        (CUR: current_iProp fmr P)
    :
      current_iPropL fmr [("H", P)].
  Proof.
    unfold current_iPropL. ss. unfold from_iPropL.
    eapply current_iProp_entail; eauto.
  Qed.

	(* Move to HoareDef. *)
	Lemma interp_hp_Assume
      iP
      fr
  :
    (interp_hp_tgt (trigger (Assume iP)) fr)
    =
		(* interp_state (handle_hAGE_tgt) (trigger (Assume iP)) fr *)
    ('(fr, _) <- (handle_Assume iP fr);; tau;; Ret (fr, tt))
.
Proof.
	unfold interp_hp_tgt, trigger. rewrite ! interp_state_vis. grind. rewrite u. et.
Qed.

	Lemma interp_hp_Guarantee
      iP
      fr
  :
    (interp_hp_tgt (trigger (Guarantee iP)) fr)
    =
		(* interp_state (handle_hAGE_tgt) (trigger (Assume iP)) fr *)
    ('(fr', _) <- (handle_Guarantee iP fr);; tau;; Ret (fr', tt))
.
Proof.
	unfold interp_hp_tgt, trigger. rewrite ! interp_state_vis. grind. rewrite u. et.
Qed.

  Variant mk_inv  
          (I: Any.t -> Any.t -> iProp)
    : unit -> Any.t * Any.t -> Prop :=
  | mk_inv_intro
      (mr_src mr_tgt: Σ) st_src st_tgt
			(* (MR: URA.extends mr_src mr_tgt) *)
			(* (INV: exists mr, current_iProp mr (I st_src st_tgt)) *)
      (INV: 
						exists mr,
						<<MRS: Own mr_src ⊢ #=> Own (mr ⋅ mr_tgt)>> /\
						<<MR: Own mr ⊢ #=> (I st_src st_tgt)>>)
    :
      mk_inv I tt (Any.pair st_src mr_src↑, Any.pair st_tgt mr_tgt↑)
  .


  Lemma hpsim_adequacy:
    forall
      f_src f_tgt st_src st_tgt (fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) itr_src itr_tgt
			(mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
			(* (FMR: fr_src ⋅ mr_src = fmr ⋅ fr_tgt ⋅ mr_tgt), *)
			(FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (fmr ⋅ fr_tgt ⋅ mr_tgt)),

			@sim_itree unit (mk_inv I) (fun _ _ => True) fl_src0 fl_tgt0 f_src f_tgt tt 
			(Any.pair st_src mr_src↑, (interp_hp_tgt_fun itr_src fr_src) >>= (fun r => Ret (snd r)))
			(Any.pair st_tgt mr_tgt↑, (interp_hp_tgt_fun itr_tgt fr_tgt) >>= (fun r => Ret (snd r))).
  Proof.
		i. 
		(* remember (Any.pair st_src mr_src↑). remember (Any.pair st_tgt mr_tgt↑). *)
		revert_until I.
		ginit. gcofix CIH. i.
		remember (st_src, itr_src). remember (st_tgt, itr_tgt).
		
		(* revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 Heqt Heqt0 CIH. *)
		revert mr_src mr_tgt fr_src fr_tgt FMR st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH.
		(* revert mr_src mr_tgt fr_src fr_tgt FMR st_src st_tgt itr_src itr_tgt Heqp Heqp0 Heqt Heqt0 CIH. *)

		induction SIM using hpsim_ind; i; clarify; unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput.
		- steps.
			force_l. instantiate (1 := (c0 ⋅ c1, ε, fmr ⋅ c)). steps.
			unfold guarantee. force_l.
			{ 
				rewrite FMR. 
				iIntros "H". iMod "H".
				rewrite <- URA.add_assoc. 
				iDestruct "H" as "[H1 H2]".
				iPoseProof (_GUARANTEE with "H2") as "H2".
				iMod "H2".
				iModIntro. r_solve.
				iDestruct "H2" as "[H3 H4]".
				iSplitR "H4"; et.
				iCombine "H3 H1" as "H". et.
			} 
			steps. force_l. 
			{ iIntros "H". et. } 
			(* rr. uipropall. }  *)
			steps. econs; esplits; et.
			+ econs. esplits; et. 
			+ admit.
		- hexploit INV. i.
			eapply iProp_sepconj in H; et. 2: { admit. }
			des.
			rename rq into fr. rename rp into mr.
			steps.
			unfold handle_Guarantee, mget, mput. steps_safe.
			force_l.
			instantiate (1:= (c0, fr ⋅ c1, mr ⋅ c)).
			steps_safe.
			unfold guarantee. force_l.
			{ 
				iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
				rewrite <- URA.add_assoc.
				iDestruct "H" as "[H H0]". 
				iPoseProof (H with "H") as "H".
				replace (c0 ⋅ (fr ⋅ c1) ⋅ (mr ⋅ c)) with (mr ⋅ fr ⋅ (c0 ⋅ c1 ⋅ c)). 2: { r_solve. }
				iPoseProof (_GUARANTEE with "H0") as "H0".
				iSplitL "H"; et.
			}
			steps_safe. force_l.
			{ et. }
			steps_safe.
			{ econs. esplits; et. admit. }
			inv WF. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput, guarantee in K.
			hexploit K. 
			{ 
				instantiate (1:= st_tgt). instantiate (1:= st_src).
				iIntros "[H1 H2]".
				iPoseProof (H1 with "H1") as "H1". 
				iPoseProof (MR with "H2") as "H2".
				iSplitL "H2"; et.
			}
			i. des.
			gstep. econs. gfinal. left. 
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply CIH; et.
			{ eapply hpsim_bot_flag_up. et. }
			{ 
				iIntros "[H H0]".
				iPoseProof (MRS with "H0") as "H0".
				replace (fr ⋅ mr0 ⋅ c1 ⋅ mr_tgt0) with (fr ⋅ c1 ⋅ (mr0 ⋅ mr_tgt0)). 2: { r_solve. }  
				iSplitL "H"; et.
			}
		- steps. hexploit K; et. i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
		- admit. (* need to clarify the relation between fl_src ~ fl_src0 *)
		- admit. 
		- steps. unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
		- steps. unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
		- steps. force_l. steps. unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
		- steps. hexploit K; et. i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
		- steps. hexploit K; et. i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
		- steps. force_r. steps. unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *. et.
		- steps. rewrite ! Any.pair_split. rewrite RUN. s.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			exploit IHSIM; et.
		- steps. rewrite ! Any.pair_split. rewrite RUN. s.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			exploit IHSIM; et.
		- steps. rewrite interp_hp_Assume. unfold handle_Assume, mget, mput. steps.  
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			hexploit K; et.
			{ 
				instantiate (1:= x ⋅ fmr).
				iIntros "[H H0]". 
				iPoseProof (_ASSUME0 with "H") as "H".
				iPoseProof (CUR with "H0") as "H0".
				iMod "H0". iModIntro. iFrame. 
			}
			i. des. eapply IH; et.
			rewrite <- ! URA.add_assoc.
			{
				iIntros "[H H0]".
				iSplitL "H"; et.
				iPoseProof (FMR0 with "H0") as "H".
				rewrite URA.add_assoc. et.
			}
		-	steps. rewrite interp_hp_Assume. 
			hexploit CUR. i.
			apply iProp_sepconj in H. 2: { admit. }
			des. rename rq into fmr0.
			unfold handle_Assume, mget, mput, assume. steps.
			force_r.
			instantiate (1:= rp).
			steps. force_r.
			{ 
				clear -H FMR0.
				assert (URA.wf (fmr ⋅ fr_tgt ⋅ mr_tgt)). { admit. }
				assert (URA.wf (fmr ⋅ fr_tgt ⋅ mr_tgt ⋅ ε)). { admit. }
				eapply own_update with (ctx := (fr_tgt ⋅ mr_tgt)) in H.
				uipropall.
				eapply H in H0. 2: { admit. }
				des.
				eapply URA.wf_extends in H0. admit.
				specialize (H2 ε H1).
				admit.
			}

			steps. force_r; et. 
			steps.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			hexploit K; et. 
			{
				iIntros "H". iPoseProof (H1 with "H") as "H". et.
			}
			i. des. 
			eapply IH; et.
			{
				iIntros "H". 
				iPoseProof (FMR0 with "H") as "H". iMod "H". rewrite <- ! URA.add_assoc.
				iDestruct "H" as "[H H0]".
				replace (fmr0 ⋅ (rp ⋅ (fr_tgt ⋅ mr_tgt))) with ((rp ⋅ fmr0) ⋅ (fr_tgt ⋅ mr_tgt)). 2: { r_solve. }
				iPoseProof (H with "H") as "H". iMod "H".
				iSplitL "H"; et.
			} 
		- steps. rewrite interp_hp_Guarantee.
			unfold handle_Guarantee, mget, mput, guarantee. steps.
			hexploit CUR. i.
			apply iProp_sepconj in H.  2: { admit. }
			des. rename rq into fmr0.
			force_l.
			instantiate (1:= (rp, fr_tgt, fmr0 ⋅ mr_tgt)).
			steps. force_l.
			{
				iIntros "H". 
				iPoseProof (FMR0 with "H") as "H". iMod "H".
				rewrite <- URA.add_assoc.
				iDestruct "H" as "[H H0]". 
				iPoseProof (H with "H") as "H". iMod "H".
				replace (rp ⋅ fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (rp ⋅ fmr0 ⋅ (fr_tgt ⋅ mr_tgt)). 2: { r_solve. }
				iSplitL "H"; et.
			}
			steps. force_l; et.
			steps.
			hexploit K; et. i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
			{
				replace (fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve.
				et.
			}
		- steps. rewrite interp_hp_Guarantee. unfold handle_Guarantee, mget, mput, guarantee. steps. 
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.			
			hexploit K; et.
			{ 
				instantiate (1:= (c0 ⋅ fmr)).
				iIntros "[H H0]".
				iPoseProof (x0 with "H") as "H".
				iPoseProof (CUR with "H0") as "H0".
				iSplitL "H"; et. 	
			} 
			i. des.
			eapply IH; et.
			{
				iIntros "H".
				iPoseProof (FMR0 with "H") as "H". iMod "H".
				rewrite <- URA.add_assoc. 
				iDestruct "H" as "[H H0]".
				iPoseProof (x with "H0") as "H0". iMod "H0".
				replace (c0 ⋅ fmr ⋅ c1 ⋅ c) with (fmr ⋅ (c0 ⋅ c1 ⋅ c)). 2: { r_solve. }
				iSplitL "H"; et.
			}
		- gstep. econs. gfinal. left. eapply CIH; et. 
		
			(* (fr_src ⋅ mr_src) -> fmr in 'SIM' *)
	Admitted.








	(* Variable fl_src: alist gname (Any.t -> itree hAGEs Any.t).
	Variable fl_tgt: alist gname (Any.t -> itree hAGEs Any.t).
	Variable I: Any.t -> Any.t -> iProp.
  Variable Any.t Any.t: Type.
  Variable Q: Any.t -> Any.t -> Any.t -> Any.t -> iProp.
  (* Variable Q: Any.t -> Any.t -> Prop. *)
  
  (* Print iProp.
  Print URA.t. *)
	(* Print current_iProp. *)

	Inductive _hpsim
	(hpsim: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop)
		: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop :=
	| hpsim_ret *)

	(****** ******)

	(* Inductive _hpsim
	(hpsim: bool -> bool -> (Any.t * Σ) * itree hAGEs Any.t -> (Any.t * Σ) * itree hAGEs Any.t -> Σ -> Prop)
		: bool -> bool -> (Any.t * Σ) * itree hAGEs Any.t -> (Any.t * Σ) * itree hAGEs Any.t -> Σ -> Prop :=
	| hpsim_ret
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			v_src v_tgt
      (INV: current_iProp mr_src (Own mr_tgt ** I st_src st_tgt))
			(RET: current_iProp fr (Q st_src st_tgt v_src v_tgt))
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), Ret v_src) ((st_tgt, mr_tgt), Ret v_tgt) fr

	| hpsim_call
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			fn varg k_src k_tgt
      (INV: current_iProp mr_src (Own mr_tgt ** I st_src st_tgt))
			(K: forall vret st_src0 st_tgt0 mr_src0 mr_tgt0 mr0
          (MR: mr_src0 = mr_tgt0 ⋅ mr0)
          (INV: current_iProp mr0 (I st_src0 st_tgt0)),
				_hpsim hpsim true true ((st_src0, mr_src0), k_src vret) ((st_tgt0, mr_tgt0), k_tgt vret) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Call fn varg) >>= k_src) ((st_tgt, mr_tgt), trigger (Call fn varg) >>= k_tgt) fr

	| hpsim_syscall
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			fn varg rvs k_src k_tgt
			(K: forall vret, 
				_hpsim hpsim true true ((st_src, mr_src), k_src vret) ((st_tgt, mr_tgt), k_tgt vret) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Syscall fn varg rvs) >>= k_src) ((st_tgt, mr_tgt), trigger (Syscall fn varg rvs) >>= k_tgt) fr

	| hpsim_inline_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			fn f varg k_src i_tgt
			(FUN: alist_find fn fl_src = Some f)
			(K: _hpsim hpsim true f_tgt ((st_src, mr_src), (f varg) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Call fn varg) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_inline_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			fn f varg i_src k_tgt
		  (FUN: alist_find fn fl_tgt = Some f)
		  (K: _hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), (f varg) >>= k_tgt) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Call fn varg) >>= k_tgt) fr

	| hpsim_tau_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  i_src i_tgt
  		(K: _hpsim hpsim true f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), tau;; i_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_tau_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  i_src i_tgt
		  (K: _hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), tau;; i_tgt) fr

	| hpsim_choose_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  X x k_src i_tgt
		  (K: _hpsim hpsim true f_tgt ((st_src, mr_src), k_src x) ((st_tgt, mr_tgt), i_tgt) fr)
  	:
	  	_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Choose X) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_choose_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  X i_src k_tgt
		  (K: forall (x: X), _hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt x) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Choose X) >>= k_tgt) fr

	| hpsim_take_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  X k_src i_tgt
		  (K: forall (x: X), _hpsim hpsim true f_tgt ((st_src, mr_src), k_src x) ((st_tgt, mr_tgt), i_tgt) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Take X) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_take_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
		  X x i_src k_tgt
		  (K: _hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt x) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Take X) >>= k_tgt) fr

	| hpsim_supdate_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
      X x st_src0 k_src i_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_src = (st_src0, x))
		  (K: _hpsim hpsim true f_tgt ((st_src0, mr_src), k_src x) ((st_tgt, mr_tgt), i_tgt) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (SUpdate run) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_supdate_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
      X x st_tgt0 i_src k_tgt
      (run: Any.t -> Any.t * X)
      (RUN: run st_tgt = (st_tgt0, x))
		  (K: _hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt0, mr_tgt), k_tgt x) fr)
	  :
		  _hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (SUpdate run) >>= k_tgt) fr

	| hpsim_assume_src
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			iP k_src i_tgt r 
      (ASM: current_iProp r iP)
			(K: _hpsim hpsim true f_tgt ((st_src, mr_src), k_src tt) ((st_tgt, mr_tgt), i_tgt) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Assume iP) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			f_src f_tgt st_src st_tgt i_src k_tgt
			(K: (iP ** (_hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt tt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Assume iP) >>= k_tgt) fr

	| hpsim_guarantee_src
			iP fr
			f_src f_tgt st_src st_tgt k_src i_tgt
			(K: (iP ** (_hpsim hpsim true f_tgt ((st_src, mr_src), k_src tt) ((st_tgt, mr_tgt), i_tgt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Guarantee iP) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_guarantee_tgt
			iP fr
			f_src f_tgt st_src st_tgt i_src k_tgt
			(K: (iP -* (_hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt tt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Guarantee iP) >>= k_tgt) fr

	| hpsim_progress
		fr
		f_src f_tgt st_src st_tgt i_src i_tgt
		(SRC: f_src = true)
		(TGT: f_tgt = true)
		(SIM: hpsim _ _ false false ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr)
	:
		_hpsim hpsim true true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr
	. *)