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
			(RET: current_iProp fmr (I st_src st_tgt))
		:
			_hpsim hpsim f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr

	| hpsim_call
			f_src f_tgt st_src st_tgt fmr
			fn varg k_src k_tgt FR
      (INV: current_iProp fmr (I st_src st_tgt ** FR))
			(K: forall vret st_src0 st_tgt0 fmr0
          (INV: current_iProp fmr0 (I st_src0 st_tgt0 ** FR)),
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
      (CUR: current_iProp fmr FMR)
			(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: current_iProp fmr (iP ** FMR))
			(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr

	| hpsim_guarantee_src
			f_src f_tgt st_src st_tgt fmr
			iP k_src i_tgt FMR
      (CUR: current_iProp fmr (iP ** FMR))
			(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_guarantee_tgt
			f_src f_tgt st_src st_tgt fmr
			iP i_src k_tgt FMR
      (CUR: current_iProp fmr FMR)
			(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
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

	Lemma _hpsim_ind2
				(hpsim: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop)
				(P: bool -> bool -> Any.t * itree hAGEs Any.t -> Any.t * itree hAGEs Any.t -> Σ -> Prop)
				(RET: forall
						f_src f_tgt st_src st_tgt fmr
						v_src v_tgt
						(RET: current_iProp fmr (I st_src st_tgt)),
						P f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr)
				(CALL: forall
						f_src f_tgt st_src st_tgt fmr
						fn varg k_src k_tgt FR
						(INV: current_iProp fmr (I st_src st_tgt ** FR))
						(K: forall vret st_src0 st_tgt0 fmr0
								(INV: current_iProp fmr0 (I st_src0 st_tgt0 ** FR)),
								<<SIM: _hpsim hpsim true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0>> /\
								<<IH: P true true (st_src0, k_src vret) (st_tgt0, k_tgt vret) fmr0>>),
						P f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr)
				(SYSCALL: forall
						f_src f_tgt st_src st_tgt fmr
						fn varg rvs k_src k_tgt
						(K: forall vret,
								<<SIM: _hpsim hpsim true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr>> /\
								<<IH: P true true (st_src, k_src vret) (st_tgt, k_tgt vret) fmr>>),
						P f_src f_tgt (st_src, trigger (Syscall fn varg rvs) >>= k_src) (st_tgt, trigger (Syscall fn varg rvs) >>= k_tgt) fmr)
				(INLINESRC: forall
						f_src f_tgt st_src st_tgt fmr
						fn f varg k_src i_tgt
						(FUN: alist_find fn fl_src = Some f)
						(K: _hpsim hpsim true f_tgt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt) fmr)
						(IH: P true f_tgt (st_src, (f varg) >>= k_src) (st_tgt, i_tgt) fmr),
						P f_src f_tgt (st_src, trigger (Call fn varg) >>= k_src) (st_tgt, i_tgt) fmr)
				(INLINETGT: forall
						f_src f_tgt st_src st_tgt fmr
						fn f varg i_src k_tgt
						(FUN: alist_find fn fl_tgt = Some f)
						(K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt) fmr)
						(IH: P f_src true (st_src, i_src) (st_tgt, (f varg) >>= k_tgt) fmr),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Call fn varg) >>= k_tgt) fmr)
				(TAUSRC: forall
						f_src f_tgt st_src st_tgt fmr
						i_src i_tgt
						(K: _hpsim hpsim true f_tgt (st_src, i_src) (st_tgt, i_tgt) fmr)
						(IH: P true f_tgt (st_src, i_src) (st_tgt, i_tgt) fmr),
						P f_src f_tgt (st_src, tau;; i_src) (st_tgt, i_tgt) fmr)
				(TAUTGT: forall
						f_src f_tgt st_src st_tgt fmr
						i_src i_tgt
						(K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, i_tgt) fmr)
						(IH: P f_src true (st_src, i_src) (st_tgt, i_tgt) fmr),
						P f_src f_tgt (st_src, i_src) (st_tgt, tau;; i_tgt) fmr)
				(CHOOSESRC: forall
						f_src f_tgt st_src st_tgt fmr
						X x k_src i_tgt
						(K: _hpsim hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr)
						(IH: P true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr),
						P f_src f_tgt (st_src, trigger (Choose X) >>= k_src) (st_tgt, i_tgt) fmr)
				(CHOOSETGT: forall
						f_src f_tgt st_src st_tgt fmr
						X i_src k_tgt
						(K: forall (x: X), 
								<<SIM: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr>> /\
								<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr>>),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Choose X) >>= k_tgt) fmr)
				(TAKESRC: forall
						f_src f_tgt st_src st_tgt fmr
						X k_src i_tgt
						(K: forall (x: X), 
								<<SIM: _hpsim hpsim true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr>> /\ 
								<<IH: P true f_tgt (st_src, k_src x) (st_tgt, i_tgt) fmr>>),
						P f_src f_tgt (st_src, trigger (Take X) >>= k_src) (st_tgt, i_tgt) fmr)
				(TAKETGT: forall
						f_src f_tgt st_src st_tgt fmr
						X x i_src k_tgt
						(K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr)
						(IH: P f_src true (st_src, i_src) (st_tgt, k_tgt x) fmr),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Take X) >>= k_tgt) fmr)
				(SUPDATESRC: forall
						f_src f_tgt st_src st_tgt fmr
						X x st_src0 k_src i_tgt
						(run: Any.t -> Any.t * X)
						(RUN: run st_src = (st_src0, x))
						(K: _hpsim hpsim true f_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr)
						(IH: P true f_tgt (st_src0, k_src x) (st_tgt, i_tgt) fmr),
						P f_src f_tgt (st_src, trigger (SUpdate run) >>= k_src) (st_tgt, i_tgt) fmr)
				(SUPDATETGT: forall
						f_src f_tgt st_src st_tgt fmr
						X x st_tgt0 i_src k_tgt
						(run: Any.t -> Any.t * X)
						(RUN: run st_tgt = (st_tgt0, x))
						(K: _hpsim hpsim f_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr)
						(IH: P f_src true (st_src, i_src) (st_tgt0, k_tgt x) fmr),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (SUpdate run) >>= k_tgt) fmr)
				(ASSUMESRC: forall
						f_src f_tgt st_src st_tgt fmr
						iP k_src i_tgt FMR
						(CUR: current_iProp fmr FMR)
						(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
								<<SIM: _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
								<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
						P f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr)
				(ASSUMETGT: forall
						f_src f_tgt st_src st_tgt fmr
						iP i_src k_tgt FMR
						(CUR: current_iProp fmr (iP ** FMR))
						(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
								<<SIM: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
								<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr)
				(GUARANTEESRC: forall
						f_src f_tgt st_src st_tgt fmr
						iP k_src i_tgt FMR
						(CUR: current_iProp fmr (iP ** FMR))
						(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
								<<SIM: _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
								<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
						P f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr)
				(GUARANTEETGT: forall
						f_src f_tgt st_src st_tgt fmr
						iP i_src k_tgt FMR
						(CUR: current_iProp fmr FMR)
						(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
								<<SIM: _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
								<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
						P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Guarantee iP) >>= k_tgt) fmr)
				(PROGRESS: forall
						st_src st_tgt fmr
						i_src i_tgt
						(SIM: hpsim false false (st_src, i_src) (st_tgt, i_tgt) fmr),
						P true true (st_src, i_src) (st_tgt, i_tgt) fmr)
		:		
		forall f_src f_tgt st_src st_tgt fmr
		(SIM: @_hpsim hpsim f_src f_tgt st_src st_tgt fmr),
		P f_src f_tgt st_src st_tgt fmr.
		Proof.
			i. induction SIM.
		{ eapply RET; eauto. }
		{ eapply CALL; esplits; et. }
		{ eapply SYSCALL; eauto. }
		{ eapply INLINESRC; eauto. }
		{ eapply INLINETGT; eauto. }
		{ eapply TAUSRC; eauto. }
		{ eapply TAUTGT; eauto. }
		{ eapply CHOOSESRC; eauto. }
		{ eapply CHOOSETGT; eauto. }
		{ eapply TAKESRC; eauto. }
		{ eapply TAKETGT; eauto. }
		{ eapply SUPDATESRC; eauto. }
		{ eapply SUPDATETGT; eauto. }
		{ eapply ASSUMESRC; esplits; et. }
		{ eapply ASSUMETGT; esplits; et. }
		{ eapply GUARANTEESRC; esplits; et. }
		{ eapply GUARANTEETGT; esplits; et. }
		{ eapply PROGRESS; eauto. }
		Qed.

		Definition hpsim := paco5 _hpsim bot5.


		Lemma _hpsim_mon: monotone5 _hpsim.
		Proof. 
			ii. induction IN using _hpsim_ind2;
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
				(RET: current_iProp fmr (I st_src st_tgt)),
				P f_src f_tgt (st_src, Ret v_src) (st_tgt, Ret v_tgt) fmr)
		(CALL: forall
				f_src f_tgt st_src st_tgt fmr
				fn varg k_src k_tgt FR
				(INV: current_iProp fmr (I st_src st_tgt ** FR))
				(K: forall vret st_src0 st_tgt0 fmr0
						(INV: current_iProp fmr0 (I st_src0 st_tgt0 ** FR)),
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
				(CUR: current_iProp fmr FMR)
				(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Assume iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(ASSUMETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: current_iProp fmr (iP ** FMR))
				(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
						<<SIM: hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>> /\
						<<IH: P f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0>>),
				P f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume iP) >>= k_tgt) fmr)
		(GUARANTEESRC: forall
				f_src f_tgt st_src st_tgt fmr
				iP k_src i_tgt FMR
				(CUR: current_iProp fmr (iP ** FMR))
				(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
						<<SIM: hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>> /\
						<<IH: P true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0>>),
				P f_src f_tgt (st_src, trigger (Guarantee iP) >>= k_src) (st_tgt, i_tgt) fmr)
		(GUARANTEETGT: forall
				f_src f_tgt st_src st_tgt fmr
				iP i_src k_tgt FMR
				(CUR: current_iProp fmr FMR)
				(K: forall fmr0 (NEW: current_iProp fmr0 (iP ** FMR)),
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
    i. punfold SIM. induction SIM using _hpsim_ind2.
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

  Variant mk_inv  
          (I: Any.t -> Any.t -> iProp)
    : unit -> Any.t * Any.t -> Prop :=
  | mk_inv_intro
      mr_src st_src mr_tgt st_tgt
      (INV: 
						(* forall (WF: URA.wf mr_src),  *)
						exists MR_tgt,
						<<MRS: current_iProp mr_src (I st_src st_tgt ** MR_tgt)>> /\
						<<MRT: current_iProp mr_tgt MR_tgt>>)
    :
      mk_inv I tt (Any.pair st_src mr_src↑, Any.pair st_tgt mr_tgt↑)
  .

	(* Check _sim_itree. *)


  Lemma hpsim_adequacy:
    forall
      f_src f_tgt st_src st_tgt fl_src fl_tgt itr_src itr_tgt
			(mr_src mr_tgt fr_src fr_tgt: Σ) FR FR_tgt
      (SIM: hpsim f_src f_tgt (st_src, itr_src) (st_tgt, itr_tgt) (fr_src ⋅ mr_src))
			(FRS: current_iProp fr_src (FR ** FR_tgt))
			(FRT: current_iProp fr_tgt FR_tgt),

			@sim_itree unit (mk_inv I) (fun _ _ => True) fl_src fl_tgt f_src f_tgt tt 
			(Any.pair st_src mr_src↑, (interp_hp_tgt itr_src fr_src) >>= (fun r => Ret (snd r)))
			(Any.pair st_tgt mr_tgt↑, (interp_hp_tgt itr_tgt fr_tgt) >>= (fun r => Ret (snd r))).
  Proof.
		i. 
		remember (Any.pair st_src mr_src↑). remember (Any.pair st_tgt mr_tgt↑).
		revert_until I.
		ginit. gcofix CIH. i.
		remember (st_src, itr_src). remember (st_tgt, itr_tgt).
		
		revert st_src st_tgt itr_src itr_tgt Heqp Heqp0 Heqt Heqt0 CIH.
		induction SIM using hpsim_ind; i; clarify.
		- steps. econs; esplits; et. admit. admit.
		- steps. { admit. } hexploit K; et. i. des. eapply IH.
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