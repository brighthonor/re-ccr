From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Import Coqlib PCM PCMAux IProp IPM.

Local Notation level := nat.

Module PF.
  
  Class t: Type := {
    shp: Type;
    deg: shp -> forall (Prev:Type), Type;
   }.

End PF.

Coercion PF.shp: PF.t >-> Sortclass.

Module GPF.
  
  Class t: Type := __GATOM: nat -> PF.t.

  Class inG (F: PF.t) (GF: t) : Type := {
    inG_id: nat;
    inG_prf: F = GF inG_id;
  }.

End GPF.

Module SRFMSynG.
  
  Class t: Type := __GATM: GPF.t.

End SRFMSynG.

Module SRFSyn.

  Section SYNTAX.

  Context `{α: SRFMSynG.t}.

  Inductive cons {Prev: Type} : Type :=
  | lift (p: Prev) : cons
  | _cur i (s: α i) (c: PF.deg s Prev -> cons)
  .

  Fixpoint _t (n : level) : Type :=
    match n with
    | O => Empty_set
    | S m => cons (Prev:=_t m) 
    end.

  Definition t (n : level) : Type := _t (S n).

  Fixpoint liftn n {m} (p: t m) : t (n+m) :=
    match n return t (n+m) with
    | 0 => p
    | S n' => lift (liftn n' p)
    end.
  
  End SYNTAX.

End SRFSyn.

Module SRFDom.

  Class t : Type := {
      dom: Type;
      void: dom;
    }.

End SRFDom.

Module SRFMSem.

  Section SEM.

  Context `{Δ: SRFDom.t}.
  Context `{α: SRFMSynG.t}.
  Context `{A: PF.t}.

  Class t : Type := 
    sem: forall n (s: A) (p: PF.deg s (SRFSyn._t n) -> SRFSyn.t n) (P: PF.deg s (SRFSyn._t n) -> SRFDom.dom), SRFDom.dom
  .

  End SEM.
  
End SRFMSem.

Module SRFMSemG.

  Section GSEM.

  Context `{Δ: SRFDom.t}.
    
  Class t `{α: SRFMSynG.t}: Type := msem : forall i, SRFMSem.t (A:= α i).

  Class inG (A: PF.t) (α: SRFMSynG.t) (B: @SRFMSem.t _ α A) (β: t) : Type := {
    inG_id: nat;
    inG_prf: existT A B = existT (α inG_id) (β inG_id);
  }.
  
  End GSEM.

End SRFMSemG.

Module SRFSem.

  Section SEM.

  Context `{β: @SRFMSemG.t Δ α}.

  Fixpoint _t n : SRFSyn._t n -> SRFDom.dom :=
    match n with
    | O => fun _ => SRFDom.void
    | S m => fix _t_aux (syn : SRFSyn._t (S m)) : SRFDom.dom :=
      match syn with
      | SRFSyn.lift p => _t m p
      | SRFSyn._cur i s c => β i m s c (_t_aux ∘ c)
      end
    end.

  Definition t n : SRFSyn.t n -> SRFDom.dom := _t (S n).

  Program Definition cur `{IN: @SRFMSemG.inG _ A α B β} {n} (c: {s: A & (PF.deg s (SRFSyn._t n) -> SRFSyn.t n)}) : SRFSyn.t n.
    destruct c as [s c]. destruct IN. inv inG_prf.
    exact (SRFSyn._cur inG_id s c).
  Defined.
  
  End SEM.
  
End SRFSem.

Module SRFRed.
  
  Section RED.

  Context `{β: @SRFMSemG.t Δ α}.

  Lemma cur `{IN: @SRFMSemG.inG _ A α B β} n s c :
    SRFSem.t n (SRFSem.cur (existT s c)) = B _ s c (SRFSem.t n ∘ c).
  Proof.
    destruct IN eqn: EQ. subst. depdes inG_prf. ss.
  Qed.

  Lemma lift_0 c :
    SRFSem.t 0 (SRFSyn.lift c) = SRFDom.void.
  Proof. reflexivity. Qed.

  Lemma lift n c :
    SRFSem.t (S n) (SRFSyn.lift c) = SRFSem.t n c.
  Proof. reflexivity. Qed.

  End RED.

End SRFRed.  

Global Opaque SRFSem.cur.
Global Opaque SRFSem.t.

(** Notations *)

Declare Scope SRF_scope.
Delimit Scope SRF_scope with SRF.
Bind Scope SRF_scope with SRFSyn.t.

Local Open Scope SRF_scope.

Notation "'⟨' A '⟩'" := (SRFSem.cur A) : SRF_scope.
Notation "⤉ P" := (SRFSyn.lift P) (at level 20) : SRF_scope.
(* Simple reduction tactics. *)

Ltac SRF_red := (try rewrite ! @SRFRed.cur;
                 try rewrite ! @SRFRed.lift_0;
                 try rewrite ! @SRFRed.lift
                ).

Ltac SRF_red_all := (try rewrite ! @SRFRed.cur in *;
                     try rewrite ! @SRFRed.lift_0 in *;
                     try rewrite ! @SRFRed.lift in *
                    ).
