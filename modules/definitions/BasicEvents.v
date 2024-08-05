Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.

Set Implicit Arguments.

Notation gname := string (only parsing). (*** convention: not capitalized ***)

Section EVENTS.

  Variant eventE: Type -> Type :=
  | Choose (X: Type): eventE X
  | Take X: eventE X
  | Syscall (fn: gname) (args: Any.t) (rvs: Any.t -> Prop): eventE Any.t.
 (* rvs: return value spec. TODO: Define operation semantics for rvs if required*)

  Inductive callE: Type -> Type :=
  | Call (fn: gname) (args: Any.t) : callE Any.t.

  Variant sE (V: Type): Type :=
  | SUpdate (run : Any.t -> Any.t * V) : sE V.

  Definition sPut x : sE unit := SUpdate (fun _ => (x, tt)).
  Definition sGet : sE (Any.t) := SUpdate (fun x => (x, x)).

  Definition Es: Type -> Type := (callE +' sE +' eventE).

  (* take-only event type to define the simplest initial_st of modules *)
  Variant takeE: Type -> Type :=
  | take X: takeE X.

  Definition pure_state {S E}: E ~> stateT S (itree E) := fun _ e s => x <- trigger e;; Ret (s, x).

  Lemma unfold_interp_state: forall {E F} {S R} (h: E ~> stateT S (itree F)) (t: itree E R) (s: S),
    interp_state h t s = _interp_state h (observe t) s.
  Proof. i. f. apply unfold_interp_state. Qed.  

  Definition handle_sE {E}: sE ~> stateT Any.t (itree E) := 
    fun _ e glob =>
      match e with
      | SUpdate run => Ret (run glob)
      end.
      
 Definition interp_sE {E}: itree (sE +' E) ~> stateT Any.t (itree E) :=
    (* State.interp_state (case_ ((fun _ e s0 => resum_itr (handle_pE e s0)): _ ~> stateT _ _) State.pure_state). *)
    State.interp_state (case_ handle_sE pure_state).

  Definition interp_Es A (prog: callE ~> itree Es) (itr0: itree Es A) (st0: Any.t): itree eventE (Any.t * _)%type :=
    '(st1, v) <- interp_sE (interp_mrec prog itr0) st0;;
    Ret (st1, v).

  Definition handle_takeE: takeE ~> itree eventE :=
    fun _ '(take X) => trigger (Take X). 

  Definition interp_takeE: itree takeE ~> itree eventE :=
    interp handle_takeE.

  Section WRAP.
    Definition assume {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Take P) ;;; Ret tt.
    Definition guarantee {E} `{eventE -< E} (P: Prop): itree E unit := trigger (Choose P) ;;; Ret tt.

    Definition triggerUB {E A} `{eventE -< E}: itree E A := v <- trigger (Take void);; match v: void with end.
    Definition triggerNB {E A} `{eventE -< E}: itree E A := v <- trigger (Choose void);; match v: void with end.

    Definition unwrapU {E X} `{eventE -< E} (x: option X): itree E X :=
      match x with
      | Some x => Ret x
      | None => triggerUB
      end.

    Definition unwrapN {E X} `{eventE -< E} (x: option X): itree E X :=
      match x with
      | Some x => Ret x
      | None => triggerNB
      end.

    Definition unleftU {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
      match xy with
      | inl x => Ret x
      | inr y => triggerUB
      end.

    Definition unleftN {E X Y} `{eventE -< E} (xy: X + Y): itree E X :=
      match xy with
      | inl x => Ret x
      | inr y => triggerNB
      end.

    Definition unrightU {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
      match xy with
      | inl x => triggerUB
      | inr y => Ret y
      end.

    Definition unrightN {E X Y} `{eventE -< E} (xy: X + Y): itree E Y :=
      match xy with
      | inl x => triggerNB
      | inr y => Ret y
      end.
  End WRAP.



End EVENTS.

Notation "f '?'" := (unwrapU f) (at level 9, only parsing).
Notation "f 'ǃ'" := (unwrapN f) (at level 9, only parsing).
Notation "(?)" := (unwrapU) (only parsing).
Notation "(ǃ)" := (unwrapN) (only parsing).


Section EVENTSCOMMON.
(*** casting call, fun ***)
  Context `{HasCallE: callE -< E}.
  Context `{HasEventE: eventE -< E}.

  Definition ccallN {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));; 
    vret <- vret↓ǃ;; Ret vret
    .
  Definition ccallU {X Y} (fn: gname) (varg: X): itree E Y := 
    vret <- trigger (Call fn (varg↑));;
    vret <- vret↓?;; Ret vret
    .

  Definition cfunN {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓ǃ;; vret <- body varg;; Ret vret↑.
  Definition cfunU {X Y} (body: X -> itree E Y): Any.t -> itree E Any.t :=
    fun varg => varg <- varg↓?;; vret <- body varg;; Ret vret↑. 

End EVENTSCOMMON.

Opaque interp_Es interp_takeE.
