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
			(EQ: v_src = v_tgt)
		:
			_hpsim hpsim f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr

	| hpsim_call
			f_src f_tgt st_src st_tgt fmr
			fn varg k_src k_tgt FR
      (INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
			(K: forall vret st_src0 st_tgt0 fmr0 
					(WF: URA.wf fmr0)
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
			(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
			(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

	| hpsim_guarantee_src
			f_src f_tgt st_src st_tgt fmr
			iP k_src i_tgt FMR
      (CUR: Own fmr ⊢ #=> (iP ** FMR))
			(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_guarantee_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: Own fmr ⊢ #=> FMR)
			(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
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
				(RET: (Own fmr ⊢ #=> I st_src st_tgt) )
				(EQ: v_src = v_tgt),
				P f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr)
		(CALL: forall
				f_src f_tgt st_src st_tgt fmr
				fn varg k_src k_tgt FR
				(INV: Own fmr ⊢ #=> (I st_src st_tgt ** FR))
				(K: forall vret st_src0 st_tgt0 fmr0
						(WF: URA.wf fmr0) 
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
				(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)) ,
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(ASSUMETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: Own fmr ⊢ #=> (iP ** FMR))
				(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
						<<SIM: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
						<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr)
		(GUARANTEESRC: forall
				f_src f_tgt st_src st_tgt fmr
				iP k_src i_tgt FMR
				(CUR: Own fmr ⊢ #=> (iP ** FMR))
				(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> FMR),
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(GUARANTEETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: Own fmr ⊢ #=> FMR)
				(K: forall fmr0 (WF: URA.wf fmr0) (NEW: Own fmr0 ⊢ #=> (iP ** FMR)),
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

	Lemma own_ctx a b
			(OWN: Own a ⊢ #=> Own b)
		:
			forall ctx, Own (ctx ⋅ a) ⊢ #=> Own (ctx ⋅ b)
	.
	Proof.
		i. iIntros "[H H0]".
		iPoseProof (OWN with "H0") as "H0".
		iSplitL "H"; et.
	Qed.

	Lemma own_wf (r r': Σ)
			(OWN: Own r ⊢ #=> Own r')
			(WF: URA.wf r)
		:
			URA.wf r'
	.
	Proof. 
		uipropall. hexploit OWN; et. refl.
		esplits; et. des.
		eapply URA.wf_extends; et.
		specialize (H0 ε). rewrite ! URA.unit_id in H0.
		et.
	Qed.



	Lemma not_wf_sat (r: Σ) (ILL: ¬ URA.wf r) P: Own r ⊢ P.
	Proof.
		rr. uipropall. i.
		eapply URA.wf_extends in WF; et.
		clarify.
	Qed.

	Lemma iProp_sepconj_aux P Q r 
			(SAT: Own r ⊢ #=> (P ** Q))
		:
			exists rp rq, (URA.updatable r (rp ⋅ rq)) /\ 
										(Own rp ⊢ P) /\ 
										(Own rq ⊢ Q)
	.
	Proof.
		destruct (classic (URA.wf r)); cycle 1.
		{
			exists r, r. esplits; eauto using not_wf_sat.
			rr. i. eapply URA.wf_mon in H0. clarify. 
		}

		uipropall.
		hexploit SAT; et. { r_solve. }
		i. des.
		esplits; et; uipropall.
		{
			instantiate (1:= b). instantiate (1:=a).
			unfold URA.updatable. subst. et. 
		}
		{
			i. destruct P. ss.
			hexploit H4. i.
			eapply URA.wf_extends in H4; et.
		}
		{
			i. destruct Q. ss.
			hexploit H4. i.
			eapply URA.wf_extends in H4; et.
		}
	Qed.

	Lemma iProp_sepconj P Q r 
			(SAT: Own r ⊢ #=> (P ** Q))
		:
			exists rp rq, (Own r ⊢ #=> Own (rp ⋅ rq)) /\ 
										(Own rp ⊢ P) /\ 
										(Own rq ⊢ Q)
	.
	Proof.
		eapply iProp_sepconj_aux in SAT; et. des.
		eapply Own_Upd in SAT.
		esplits; et. 	
	Qed.	

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

	(* Which fr to put in interp_hp_tgt & What to return *)
	Definition interp_hp_fun (hp: Any.t -> itree hAGEs Any.t): Any.t -> itree Es Any.t :=
		fun arg => interp_hp_tgt_fun (hp arg) ε >>= (fun '(_, x) => Ret x).



  Variant mk_inv  
          (I: Any.t -> Any.t -> iProp)
    : Σ -> Any.t * Any.t -> Prop :=
  | mk_inv_intro
      (ctx mr_src mr_tgt: Σ) st_src st_tgt
      (INV: exists mr,
						<<WF: URA.wf (ctx ⋅ mr_src)>> /\
						<<MRS: Own mr_src ⊢ #=> Own (mr ⋅ mr_tgt)>> /\
						<<MR: Own mr ⊢ #=> (I st_src st_tgt)>>)
    :
      mk_inv I ctx (Any.pair st_src mr_src↑, Any.pair st_tgt mr_tgt↑)
  .

  (* Lemma hpsim_adequacy:
    forall
      f_src f_tgt st_src st_tgt (fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) itr_src itr_tgt
			(ctx mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt) fmr)
			(FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (fmr ⋅ fr_tgt ⋅ mr_tgt))
			(WF: URA.wf (ctx ⋅ fr_src ⋅ mr_src)),
			@sim_itree Σ (mk_inv I) (fun _ _ => True) fl_src0 fl_tgt0 f_src f_tgt ctx
			(Any.pair st_src mr_src↑, (interp_hp_tgt_fun itr_src fr_src) >>= (fun r => Ret (snd r)))
			(Any.pair st_tgt mr_tgt↑, (interp_hp_tgt_fun itr_tgt fr_tgt) >>= (fun r => Ret (snd r)))
		.
  Proof.
		i. 
		revert_until I.
		ginit. gcofix CIH. i.
		remember (st_src, itr_src). remember (st_tgt, itr_tgt).
		
		revert mr_src mr_tgt fr_src fr_tgt FMR st_src st_tgt itr_src itr_tgt Heqp Heqp0 CIH WF.

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
			steps. econs; esplits; et. econs. esplits; et.  *)


	Inductive hpsim_adeq_rel : Σ -> Σ -> (itree hAGEs Any.t)-> (stateT Σ (itree Es) Any.t) ->  Σ -> Σ -> (itree hAGEs Any.t)-> (stateT Σ (itree Es) Any.t) -> Prop :=
	| hpsim_adeq_base (fr mr fr' mr': Σ) st st'
		: hpsim_adeq_rel fr mr (Ret st) (fun fr0 => '(fr1, _) <- (handle_Guarantee (True%I:iProp) fr0);; Ret (fr1, st))
										 fr' mr' (Ret st') (fun fr0 => '(fr1, _) <- (handle_Guarantee (True%I:iProp) fr0);; Ret (fr1, st'))

	| hpsim_adeq_seq itrH0 itrH1 itrL0 itrL1 itrH0' itrH1' itrL0' itrL1' (fr mr fr1 fr' mr' fr1': Σ)
			(ITR0: itrL0 = @interp_hp_tgt_fun Σ Any.t itrH0)
			(ITR0': itrL0' = @interp_hp_tgt_fun Σ Any.t itrH0')
			(ADEQ: forall st st' (mr1 mr1': Σ), hpsim_adeq_rel fr1 mr1 (itrH1 st) (itrL1 st) 
																												fr1' mr1' (itrH1' st') (itrL1' st'))
		: hpsim_adeq_rel fr mr (st0 <- itrH0;; itrH1 st0) (fun fr0 => '(_, st1) <- (itrL0 fr0);; (itrL1 st1 fr1))
										fr' mr' (st0 <- itrH0';; itrH1' st0) (fun fr0 => '(_, st1) <- (itrL0' fr0);; (itrL1' st1 fr1'))
	.


  Lemma hpsim_adequacy
			(fl_src0 fl_tgt0: alist string (Any.t -> itree Es Any.t)) 
			(FLS: fl_src0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_src)
			(FLT: fl_tgt0 = List.map (fun '(s, f) => (s, interp_hp_fun f)) fl_tgt)
			f_src f_tgt st_src st_tgt itrH_src itrH_tgt itrL_src itrL_tgt
			(ctx mr_src mr_tgt fr_src fr_tgt fmr: Σ)
      (SIM: hpsim f_src f_tgt (st_src, itrH_src) (st_tgt, itrH_tgt) fmr)
			(WF: URA.wf (ctx ⋅ fr_src ⋅ mr_src))
			(FMR: Own (fr_src ⋅ mr_src) ⊢ #=> Own (fmr ⋅ fr_tgt ⋅ mr_tgt))
			(REL: hpsim_adeq_rel fr_src mr_src itrH_src itrL_src fr_tgt mr_tgt itrH_tgt itrL_tgt)
		:

			@sim_itree Σ (mk_inv I) eq fl_src0 fl_tgt0 f_src f_tgt ctx 
			(Any.pair st_src mr_src↑, (itrL_src fr_src) >>= (fun r => Ret (snd r)))
			(Any.pair st_tgt mr_tgt↑, (itrL_tgt fr_tgt) >>= (fun r => Ret (snd r))).
  Proof.
		revert_until FLT.
		ginit. gcofix CIH. i.
		move REL before CIH. revert_until REL. induction REL.
		{ i. punfold SIM. inv SIM; (try rewrite ! bind_trigger in H3); (try rewrite ! bind_trigger in H5); clarify.
			- steps. unfold handle_Guarantee, mput, mget, guarantee. steps.
				force_l. instantiate (1:= (c0 ⋅ c1, ε, fmr ⋅ c)).
				steps. force_l.
				{  
					rewrite FMR. 
					iIntros "H". iMod "H".
					rewrite <- URA.add_assoc. 
					iDestruct "H" as "[H H0]".
					iPoseProof (x with "H0") as "H0". iMod "H0". 
					iModIntro. r_solve.
					replace (c0 ⋅ c1 ⋅ fmr ⋅ c) with (c0 ⋅ c1 ⋅ c ⋅ fmr); r_solve.
					iSplitR "H"; et.
				}
				steps. force_l; et.
				steps.
				econs; esplits; et. econs; esplits; et.
				{  
					eapply own_ctx in FMR. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
					rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
					eapply own_ctx, own_wf in x; et.
					replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
					eapply URA.wf_mon; et.
				}
			- pclearbot. punfold SIM0. inv SIM0; (try rewrite ! bind_trigger in H3); (try rewrite ! bind_trigger in H5); clarify.
				steps. unfold handle_Guarantee, mput, mget, guarantee. steps.
				force_l. instantiate (1:= (c0 ⋅ c1, ε, fmr ⋅ c)).
				steps. force_l.
				{  
					rewrite FMR. 
					iIntros "H". iMod "H".
					rewrite <- URA.add_assoc. 
					iDestruct "H" as "[H H0]".
					iPoseProof (x with "H0") as "H0". iMod "H0". 
					iModIntro. r_solve.
					replace (c0 ⋅ c1 ⋅ fmr ⋅ c) with (c0 ⋅ c1 ⋅ c ⋅ fmr); r_solve.
					iSplitR "H"; et.
				}
				steps. force_l; et.
				steps.
				econs; esplits; et. econs; esplits; et.
				{  
					eapply own_ctx in FMR. rewrite URA.add_assoc in FMR. eapply own_wf in FMR; et.
					rewrite <- URA.add_assoc in FMR. rewrite URA.add_assoc in FMR.
					eapply own_ctx, own_wf in x; et.
					replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ fmr ⋅ c ⋅ (c0 ⋅ c1)) in x; r_solve.
					eapply URA.wf_mon; et.
				}
		}
		
		remember (st_src, itrH_src) as sti_src. remember (st_tgt, itrH_tgt) as sti_tgt.
		move SIM before CIH. revert_until SIM.
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
			steps. econs; esplits; et.
			+ econs. esplits; et.
				eapply own_ctx with (ctx:= ctx ⋅ fmr) in _GUARANTEE.
				eapply own_ctx with (ctx:= ctx) in FMR.
				rewrite <- URA.add_assoc in WF. eapply own_wf in FMR; et.
				rewrite ! URA.add_assoc in FMR.
				rewrite URA.add_assoc in _GUARANTEE.
				eapply own_wf in _GUARANTEE; et.
				replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (ctx ⋅ (fmr ⋅ c) ⋅ c0 ⋅ c1) in _GUARANTEE. 2: { r_solve. }
				do 2 eapply URA.wf_mon; et.
		- hexploit INV. i.
			eapply iProp_sepconj in H. et.
			des.
			rename rq into fr. rename rp into mr.
			steps.
			unfold handle_Guarantee, mget, mput. steps_safe.
			force_l.
			instantiate (1:= (c0, fr ⋅ c1, mr ⋅ c)).
			rename c1 into fr_tgt'. rename c into mr_tgt'.
			steps_safe.
			unfold guarantee. force_l.
			{ 
				iIntros "H". iPoseProof (FMR with "H") as "H". iMod "H".
				rewrite <- URA.add_assoc.
				iDestruct "H" as "[H H0]". 
				iPoseProof (H with "H") as "H".
				replace (c0 ⋅ (fr ⋅ fr_tgt') ⋅ (mr ⋅ mr_tgt')) with (mr ⋅ fr ⋅ (c0 ⋅ fr_tgt' ⋅ mr_tgt')). 2: { r_solve. }
				iPoseProof (_GUARANTEE with "H0") as "H0".
				iSplitL "H"; et.
			}
			steps_safe. force_l.
			{ et. }
			steps_safe. eapply safe_sim_sim; econs; i.
			exists (fr ⋅ ctx). esplits.
			{ 
				econs. esplits; et.
				{
					eapply own_ctx with (ctx:= ctx ⋅ fmr) in _GUARANTEE.
					eapply own_ctx with (ctx:= ctx) in FMR.
					rewrite <- URA.add_assoc in WF. eapply own_wf in FMR; et.
					rewrite ! URA.add_assoc in FMR.
					rewrite URA.add_assoc in _GUARANTEE.
					eapply own_wf in _GUARANTEE; et.
					rewrite URA.add_comm in _GUARANTEE. rewrite URA.add_assoc in _GUARANTEE.
					eapply own_ctx in H. eapply own_wf in H; et.
					replace (c0 ⋅ fr_tgt' ⋅ mr_tgt' ⋅ ctx ⋅ (mr ⋅ fr)) with (fr ⋅ ctx ⋅ mr ⋅ mr_tgt' ⋅ (c0 ⋅ fr_tgt')) in H; r_solve.
					eapply URA.wf_mon; et.
				} 
				iIntros "H". iPoseProof (H0 with "H") as "H". et.
			}
			i. inv WF0. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput, guarantee in K.
			hexploit K; swap 1 2.
			{ 
				iIntros "[H1 H2]".
				iPoseProof (H1 with "H1") as "H1". 
				iPoseProof (MR with "H2") as "H2".
				iSplitL "H2"; et.
			}
			{
				eapply own_ctx in MRS. eapply own_wf in MRS; et.
				replace (fr ⋅ ctx ⋅ (mr0 ⋅ mr_tgt0)) with (fr ⋅ mr0 ⋅ (ctx ⋅ mr_tgt0)) in MRS; r_solve.
				eapply URA.wf_mon; et.				
			}
			i. des.
			steps. 
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
			{ 
				iIntros "[H H0]".
				iPoseProof (MRS with "H0") as "H0".
				replace (fr ⋅ mr0 ⋅ fr_tgt' ⋅ mr_tgt0) with (fr ⋅ fr_tgt' ⋅ (mr0 ⋅ mr_tgt0)). 2: { r_solve. }  
				iSplitL "H"; et.
			}
			{
				clear IH.

				admit.	
			}
		- steps. hexploit K; et. i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
		- steps. unfold handle_Guarantee, mget, mput, guarantee. steps.
			force_l.
			instantiate (1:= (ε, ε, fr_src ⋅ mr_src)).
			steps. force_l. { r_solve. et. }
			steps. force_l; et. 
			steps. 
			{ 
				instantiate (1:= interp_hp_fun f).
				rewrite alist_find_map. rewrite FUN. et.
			}
			unfold interp_hp_fun, interp_hp_tgt_fun. steps.
			do 3 rewrite <- bind_bind in *.
			(* set (` x : Σ * Any.t <- interp_hp_tgt (f varg) ε;; (let '(_, x0) := x in Ret x0)) as itr. *)
			(* assert () *)
			set ((` x : Σ * Any.t <- (` x : Any.t <- (` x : Σ * Any.t <- interp_hp_tgt (f varg) ε;; (let '(_, x0) := x in Ret x0));; (tau;; Ret (fr_src, x)));;
			interp_hp_tgt (k_src x.2) x.1)) as itr0.
			set (interp_hp_tgt (` x : Any.t <- (f varg);; k_src x) fr_src) as itr1.
			assert (itr0 = itr1 ). {
				unfold itr0, itr1. grind. rewrite interp_hp_bind.	
			admit. }
			rewrite H. unfold itr1.
			(* assert (itr_src = interp_hp_tgt (` x : Any.t <- (f varg);; ` x : Σ * Any.t <- (k_src x)) fr_src).
			{ unfold itr_src. grind. }
			rewrite <- interp_hp_bind. *)
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IHSIM; et.
	
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
			eapply IHSIM; et.
		- steps. rewrite ! Any.pair_split. rewrite RUN. s.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IHSIM; et.
		- steps. rewrite interp_hp_Assume. unfold handle_Assume, mget, mput. steps.  
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			(* hexploit K. *)
			hexploit (K (x ⋅ fmr)). et.
			{ 
				eapply own_ctx in FMR0. eapply own_wf in FMR0; cycle 1.
				{ rewrite URA.add_assoc; et.  }
				{ rewrite ! URA.add_assoc in FMR0. do 2 eapply URA.wf_mon; et.  }
			}
			et.
			{
				iIntros "[H H0]". 
				iPoseProof (_ASSUME0 with "H") as "H".
				iPoseProof (CUR with "H0") as "H0".
				iMod "H0". iModIntro. iFrame. 
			}
			i. des. eapply IH; et.
			{
				rewrite <- ! URA.add_assoc.
				iIntros "[H H0]".
				iSplitL "H"; et.
				iPoseProof (FMR0 with "H0") as "H".
				rewrite URA.add_assoc. et.
			}
			{
				clear IH. admit.
			}
		-	steps. rewrite interp_hp_Assume. 
			hexploit CUR. i.
			apply iProp_sepconj in H.
			des. rename rq into fmr0.
			unfold handle_Assume, mget, mput, assume. steps.
			force_r.
			instantiate (1:= rp).
			steps. force_r.
			{ 
				eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
				replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
				eapply own_ctx in H. eapply own_wf in H; et.
				replace (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ (rp ⋅ fmr0)) with (rp ⋅ fr_tgt ⋅ mr_tgt ⋅ (ctx ⋅ fmr0)) in H; r_solve.
				eapply URA.wf_mon; et.	
			}
			steps. force_r; et. 
			steps.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			hexploit (K fmr0).
			{
				eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0; et. eapply own_wf in FMR0; et.
				replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt )) with (fmr ⋅ (ctx ⋅ fr_tgt ⋅ mr_tgt)) in FMR0; r_solve.
				eapply URA.wf_mon in FMR0. eapply own_wf in H; et.
				rewrite URA.add_comm in H. eapply URA.wf_mon; et.
			}
			{ 
				iIntros "H". iPoseProof (H1 with "H") as "H". et.
			}
			i. des.
			eapply IH; et.
			{
				clear IH.
				iIntros "H". iPoseProof (FMR0 with "H") as "H".
				rewrite <- URA.add_assoc. iMod "H". iDestruct "H" as "[H H0]".
				r_solve. rewrite <- URA.add_assoc. iSplitL "H"; et.
				iPoseProof (H with "H") as "H". iMod "H".
				iDestruct "H" as "[H H0]". iSplitL "H0"; et.  				
			}
		- steps. rewrite interp_hp_Guarantee.
			unfold handle_Guarantee, mget, mput, guarantee. steps.
			hexploit CUR. i.
			apply iProp_sepconj in H.
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
			hexploit (K fmr0); et.
			{
				eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
				replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
				eapply own_ctx, own_wf in H; et.
				rewrite URA.add_assoc in H.
				eapply URA.wf_mon. rewrite URA.add_comm. et.
			}
			{
				iIntros "H". iPoseProof (H1 with "H") as "H". et.	
			}
			i. des.
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.
			eapply IH; et.
			{
				replace (fr_tgt ⋅ (fmr0 ⋅ mr_tgt)) with (fmr0 ⋅ fr_tgt ⋅ mr_tgt); r_solve.
				et.
			}
			{
				clear IH. 
				eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
				replace (ctx ⋅ (fmr ⋅ fr_tgt ⋅ mr_tgt)) with (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ fmr) in FMR0; r_solve.
				eapply own_ctx, own_wf in H; et.
				replace (ctx ⋅ fr_tgt ⋅ mr_tgt ⋅ (rp ⋅ fmr0)) with (ctx ⋅ fr_tgt ⋅ fmr0 ⋅ mr_tgt ⋅ rp) in H; r_solve.
				eapply URA.wf_mon; et.
			}
		- steps. rewrite interp_hp_Guarantee. unfold handle_Guarantee, mget, mput, guarantee. steps. 
			unfold interp_hp_tgt_fun, handle_Guarantee, mget, mput in *. rewrite <- ! bind_bind in *.			
			hexploit (K (c0 ⋅ fmr)). 
			{
				eapply own_ctx in FMR0. rewrite URA.add_assoc in FMR0. eapply own_wf in FMR0; et.
				rewrite <- URA.add_assoc in FMR0. rewrite URA.add_assoc in FMR0.
				eapply own_ctx, own_wf in x; et.
				replace (ctx ⋅ fmr ⋅ (c0 ⋅ c1 ⋅ c)) with (c0 ⋅ fmr ⋅ (ctx ⋅ c1 ⋅ c)) in x; r_solve.
				eapply URA.wf_mon; et.
			}
			{ 
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