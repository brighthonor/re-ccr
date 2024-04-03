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
  Variable R_src R_tgt: Type.
  Variable Q: Any.t -> Any.t -> R_src -> R_tgt -> iProp.
  (* Variable Q: R_src -> R_tgt -> Prop. *)
  
  (* Print iProp.
  Print URA.t. *)
	(* Print current_iProp. *)

	Inductive _hpsim
	(hpsim: bool -> bool -> Any.t * itree hAGEs R_src -> Any.t * itree hAGEs R_tgt -> Σ -> Prop)
		: bool -> bool -> Any.t * itree hAGEs R_src -> Any.t * itree hAGEs R_tgt -> Σ -> Prop :=
	| hpsim_ret
			f_src f_tgt st_src st_tgt fmr
			v_src v_tgt
			(RET: current_iProp fmr (I st_src st_tgt ** Q st_src st_tgt v_src v_tgt))
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
			P k_src i_tgt FMR
      (CUR: current_iProp fmr FMR)
			(K: forall fmr0 (NEW: current_iProp fmr0 (P ** FMR)),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Assume P) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt fmr
			P i_src k_tgt FMR
      (CUR: current_iProp fmr (P ** FMR))
			(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Assume P) >>= k_tgt) fmr

	| hpsim_guarantee_src
			f_src f_tgt st_src st_tgt fmr
			P k_src i_tgt FMR
      (CUR: current_iProp fmr (P ** FMR))
			(K: forall fmr0 (NEW: current_iProp fmr0 FMR),
          _hpsim hpsim true f_tgt (st_src, k_src tt) (st_tgt, i_tgt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, trigger (Guarantee P) >>= k_src) (st_tgt, i_tgt) fmr

	| hpsim_guarantee_tgt
			f_src f_tgt st_src st_tgt fmr
			P i_src k_tgt FMR
      (CUR: current_iProp fmr FMR)
			(K: forall fmr0 (NEW: current_iProp fmr0 (P ** FMR)),
          _hpsim hpsim f_src true (st_src, i_src) (st_tgt, k_tgt tt) fmr0)
		:
			_hpsim hpsim f_src f_tgt (st_src, i_src) (st_tgt, trigger (Guarantee P) >>= k_tgt) fmr

	| hpsim_progress
  		st_src st_tgt fmr
      i_src i_tgt
  		(SIM: hpsim false false (st_src, i_src) (st_tgt, i_tgt) fmr)
  	:
  		_hpsim hpsim true true (st_src, i_src) (st_tgt, i_tgt) fmr
	.


	Definition hp_sim := paco5 _hpsim bot5.





	(****** ******)

	(* Inductive _hpsim
	(hpsim: bool -> bool -> (Any.t * Σ) * itree hAGEs R_src -> (Any.t * Σ) * itree hAGEs R_tgt -> Σ -> Prop)
		: bool -> bool -> (Any.t * Σ) * itree hAGEs R_src -> (Any.t * Σ) * itree hAGEs R_tgt -> Σ -> Prop :=
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
			P k_src i_tgt r 
      (ASM: current_iProp r P)
			(K: _hpsim hpsim true f_tgt ((st_src, mr_src), k_src tt) ((st_tgt, mr_tgt), i_tgt) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Assume P) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_assume_tgt
			f_src f_tgt st_src st_tgt mr_src mr_tgt fr
			f_src f_tgt st_src st_tgt i_src k_tgt
			(K: (P ** (_hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt tt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Assume P) >>= k_tgt) fr

	| hpsim_guarantee_src
			P fr
			f_src f_tgt st_src st_tgt k_src i_tgt
			(K: (P ** (_hpsim hpsim true f_tgt ((st_src, mr_src), k_src tt) ((st_tgt, mr_tgt), i_tgt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), trigger (Guarantee P) >>= k_src) ((st_tgt, mr_tgt), i_tgt) fr

	| hpsim_guarantee_tgt
			P fr
			f_src f_tgt st_src st_tgt i_src k_tgt
			(K: (P -* (_hpsim hpsim f_src true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), k_tgt tt))) fr)
		:
			_hpsim hpsim f_src f_tgt ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), trigger (Guarantee P) >>= k_tgt) fr

	| hpsim_progress
		fr
		f_src f_tgt st_src st_tgt i_src i_tgt
		(SRC: f_src = true)
		(TGT: f_tgt = true)
		(SIM: hpsim _ _ false false ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr)
	:
		_hpsim hpsim true true ((st_src, mr_src), i_src) ((st_tgt, mr_tgt), i_tgt) fr
	. *)