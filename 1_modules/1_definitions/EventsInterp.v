Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Import Events.

Set Implicit Arguments.

Section EVENTS.
  Section INTERP.
    Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).
    
    Definition handle_sE {E}: sE ~> stateT Any.t (itree E) := 
      fun _ e glob =>
        match e with
        | SUpdate run => Ret (run glob)
        end.
    Definition interp_sE {E}: itree (sE +' E) ~> stateT Any.t (itree E) := 
      State.interp_state (case_ handle_sE pure_state).

    Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: Any.t): itree eventE (Any.t * _)%type :=
      '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;; Ret (st1, v).

    (* LEMMAS *)
    Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
      interp_state h t s = _interp_state h (observe t) s.
    Proof. i. f. apply unfold_interp_state. Qed.


  End INTERP.

End EVENTS.
