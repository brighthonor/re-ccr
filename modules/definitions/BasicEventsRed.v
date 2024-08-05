
Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import BasicEvents.
Require Import Red IRed.

Section RED.
  (* itree reduction lemmas *)
  Section ES.
    Lemma interp_Es_bind
          A B
          (itr: itree Es A) (ktr: A -> itree Es B)
          (prog: callE ~> itree Es)
          st0
      :
        interp_Es prog (v <- itr ;; ktr v) st0 =
        '(st1, v) <- interp_Es prog (itr) st0 ;; interp_Es prog (ktr v) st1.

    Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

    Lemma interp_Es_tau
          (prog: callE ~> itree Es)
          A
          (itr: itree Es A)
          st0
      :
        interp_Es prog (tau;; itr) st0 = tau;; interp_Es prog itr st0.
    Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

    Lemma interp_Es_ret
          T
          prog st0 (v: T)
      :
        interp_Es prog (Ret v: itree Es _) st0 = Ret (st0, v).
    Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

    Lemma interp_Es_callE
          p st0 T
          (* (e: Es Σ) *)
          (e: callE T)
      :
        interp_Es p (trigger e) st0 = tau;; (interp_Es p (p _ e) st0).
    Proof. unfold interp_Es, interp_sE. des_ifs. grind. Qed.

    Lemma interp_Es_sE
          p st0
          (* (e: Es Σ) *)
          T
          (e: sE T)
      :
        interp_Es p (trigger e) st0 =
        '(st1, r) <- handle_sE e st0;;
        tau;; tau;;
        Ret (st1, r).
    Proof.
      unfold interp_Es, interp_sE. grind.
    Qed.

    Lemma interp_Es_eventE
          p st0
          T
          (e: eventE T)
      :
        interp_Es p (trigger e) st0 = r <- trigger e;; tau;; tau;; Ret (st0, r).
    Proof.
      unfold interp_Es, interp_sE. grind.
      unfold pure_state. grind.
    Qed.

    Lemma interp_Es_triggerUB
          (prog: callE ~> itree Es)
          st0
          A
      :
        (interp_Es prog (triggerUB) st0: itree eventE (_ * A)) = triggerUB.
    Proof.
      unfold interp_Es, interp_sE, pure_state, triggerUB. grind.
    Qed.

    Lemma interp_Es_triggerNB
          (prog: callE ~> itree Es)
          st0
          A
      :
        (interp_Es prog (triggerNB) st0: itree eventE (_ * A)) = triggerNB.
    Proof.
      unfold interp_Es, interp_sE, pure_state, triggerNB. grind.
    Qed. 
    
    Lemma interp_Es_unwrapU
          prog R st0 (r: option R)
      :
        interp_Es prog (unwrapU r) st0 = r <- unwrapU r;; Ret (st0, r).
    Proof.
      unfold unwrapU. des_ifs.
      - rewrite interp_Es_ret. grind.
      - rewrite interp_Es_triggerUB. unfold triggerUB. grind.
    Qed.

    Lemma interp_Es_unwrapN
          prog R st0 (r: option R)
      :
        interp_Es prog (unwrapN r) st0 = r <- unwrapN r;; Ret (st0, r).
    Proof.
      unfold unwrapN. des_ifs.
      - rewrite interp_Es_ret. grind.
      - rewrite interp_Es_triggerNB. unfold triggerNB. grind.
    Qed.

    Lemma interp_Es_assume
          prog st0 (P: Prop)
      :
        interp_Es prog (assume P) st0 = assume P;;; tau;; tau;; Ret (st0, tt).
    Proof.
      unfold assume.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
      rewrite interp_Es_eventE.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
      rewrite interp_Es_ret.
      refl.
    Qed.

    Lemma interp_Es_guarantee
          prog st0 (P: Prop)
      :
        interp_Es prog (guarantee P) st0 = guarantee P;;; tau;; tau;; Ret (st0, tt).
    Proof.
      unfold guarantee.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
      rewrite interp_Es_eventE.
      repeat (try rewrite interp_Es_bind; try rewrite bind_bind). grind.
      rewrite interp_Es_ret.
      refl.
    Qed.    

    Lemma interp_Es_ext
          prog R (itr0 itr1: itree _ R) st0
      : 
        itr0 = itr1 -> interp_Es prog itr0 st0 = interp_Es prog itr1 st0.
    Proof. i; subst; refl. Qed.    

    Global Program Instance interp_Es_rdb: red_database (mk_box (@interp_Es)) :=
      mk_rdb
        1
        (mk_box interp_Es_bind)
        (mk_box interp_Es_tau)
        (mk_box interp_Es_ret)
        (mk_box interp_Es_sE)
        (mk_box interp_Es_sE)
        (mk_box interp_Es_callE)
        (mk_box interp_Es_eventE)
        (mk_box interp_Es_triggerUB)
        (mk_box interp_Es_triggerNB)
        (mk_box interp_Es_unwrapU)
        (mk_box interp_Es_unwrapN)
        (mk_box interp_Es_assume)
        (mk_box interp_Es_guarantee)
        (mk_box interp_Es_ext).
        
  End ES.

  Section TAKE.

    Lemma interp_takeE_bind
          A B
          (itr: itree takeE A) (ktr: A -> itree takeE B)
      :
        interp_takeE (v <- itr ;; ktr v) = 
        v <- interp_takeE itr;; interp_takeE (ktr v).
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_ret
          T (v: T)
      :
        interp_takeE (Ret v: itree takeE _) = Ret v.
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_tau
          T (itr: itree takeE T)
      :
        interp_takeE (tau;; itr) = tau;; interp_takeE itr.
    Proof. 
      unfold interp_takeE. grind. 
    Qed.

    Lemma interp_takeE_take
          X (e: takeE X)
      :
        interp_takeE (trigger e) = (handle_takeE e) >>= (fun r => tau;; Ret r).
    Proof.
      unfold interp_takeE. rewrite interp_trigger. grind.
    Qed.

  End TAKE.
End RED.

