From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Import PCM IProp IPM RobustIndexedInvariants.

Local Notation level := nat.

Module sAtom.

  Section SATOM.

  Context `{Σ : GRA.t}.
  
  Class t: Type := mk {
    car:> forall (sProp: Type), Type;
    interp: forall {sProp} (itp: sProp -> iProp), car sProp -> iProp;
  }.

  Instance empty: t := {
      car sProp := sProp;
      interp sProp itp := itp;
    }.

  Instance pointwise {D} (M: D -> t): t := {
      car sProp := { d & (M d).(car) sProp };
      interp sProp itp p := (M (projT1 p)).(interp) itp (projT2 p);
    }.

  End SATOM.
  
End sAtom.

Coercion sAtom.car: Sortclass >-> Sortclass.

Module GAtom.

  Section GATOM.
  
  Context `{Σ : GRA.t}.
  
  Class t: Type := __GATOM_INTERNAL : (nat -> sAtom.t).
  
  Class inG (PB: sAtom.t) (α: t) := InG {
    inG_id: nat;
    inG_prf: PB = α inG_id;
  }
  .
  
  Class subG (α0 α1: t) := SubG i : { j | α0 i = α1 j }.

  Definition of_list (RAs: list sAtom.t): t := fun n => List.nth n RAs (sAtom.empty).

  Definition to_sAtom (α: t): sAtom.t := sAtom.pointwise α.

  Coercion to_sAtom: t >-> sAtom.t.

  Let cast_pb {A B: sAtom.t} (EQ: A = B) {sProp} (a: A.(sAtom.car) sProp): B.(sAtom.car) sProp :=
    eq_rect_r (λ A0, A0.(sAtom.car) sProp → B.(sAtom.car) sProp) id EQ a.

  Definition embed {A α} `{@inG A α} {sProp} (a: A.(sAtom.car) sProp): α.(sAtom.car) sProp :=
    existT inG_id (cast_pb inG_prf a).

  Lemma embed_interp
        A α
        `{@inG A α}
        sProp itp (a: A.(sAtom.car) sProp)
    :
    α.(sAtom.interp) itp (embed a) = A.(sAtom.interp) itp a.
  Proof.
    destruct H. subst. eauto.
  Qed.

  End GATOM.

End GAtom.
  
Coercion GAtom.to_sAtom: GAtom.t >-> sAtom.t.
Coercion GAtom.embed: sAtom.car >-> sAtom.car.

Global Opaque GAtom.to_sAtom.

Module sType.

  Class t : Type := mk {
    car:> Type;
    interp: car -> forall sProp: Type, Type                        
  }.

End sType.

Coercion sType.car: sType.t >-> Sortclass.

Module sProp.

  Section SPROP.

  Context `{τ: sType.t}.
  Context `{α: GAtom.t}.

  Inductive t {sProp : Type} : Type :=
  | atom (a : α.(sAtom.car) sProp) : t
  | lift (p : sProp) : t
  | pure (P : Prop) : t
  | and (p q : t) : t
  | or  (p q : t) : t
  | impl (p q : t) : t
  | univ (ty : τ) (p: τ.(sType.interp) ty sProp -> t) : t
  | ex   (ty : τ) (p: τ.(sType.interp) ty sProp -> t) : t
  | empty : t
  | sepconj (p q : t) : t
  | wand (p q : t) : t
  | persistently (p : t) : t
  | plainly (p : t) : t
  | upd (p : t) : t
  .

  Fixpoint _sProp (n : level) : Type :=
    match n with
    | O => Empty_set
    | S m => @t (_sProp m)
    end.

  Definition sProp (n : level) : Type := _sProp (S n).

  Definition affinely {n} (p : sProp n) : sProp n :=
    and empty p.
  
  Fixpoint _interp n : _sProp n -> iProp :=
    match n with
    | O => fun _ => ⌜False⌝%I
    | S m => fix _interp_sProp_aux (syn : t) : iProp :=
      match syn with
      | atom a => α.(sAtom.interp) (_interp m) a
      | lift p => _interp m p
      | pure P => Pure P
      | and p q => And (_interp_sProp_aux p) (_interp_sProp_aux q)
      | or p q => Or (_interp_sProp_aux p) (_interp_sProp_aux q)
      | impl p q => Impl (_interp_sProp_aux p) (_interp_sProp_aux q)
      | univ ty p => Univ (fun (x : τ.(sType.interp) ty (_sProp m)) => _interp_sProp_aux (p x))
      | ex ty p => Ex (fun (x : τ.(sType.interp) ty (_sProp m)) => _interp_sProp_aux (p x))
      | empty => Emp
      | sepconj p q => Sepconj (_interp_sProp_aux p) (_interp_sProp_aux q)
      | wand p q => Wand (_interp_sProp_aux p) (_interp_sProp_aux q)
      | persistently p => Persistently (_interp_sProp_aux p)
      | plainly p => IProp.Plainly (_interp_sProp_aux p)
      | upd p => Upd (_interp_sProp_aux p)
      end
    end.

    Definition interp n : sProp n -> iProp := _interp (S n).

  End SPROP.

End sProp.

Section RED.

  Context `{τ: sType.t}.
  Context `{α: GAtom.t}.

  Import sProp.

  Lemma red_sem_atom n a :
    interp n (atom a) = α.(sAtom.interp) (_interp n) a.
  Proof. ss. Qed.

  Lemma red_sem_lift_0 p :
    interp 0 (lift p) = ⌜False⌝%I.
  Proof. ss. Qed.

  Lemma red_sem_lift n p :
    interp (S n) (lift p) = interp n p.
  Proof. ss. Qed.

  Lemma red_sem_pure n P :
    interp n (pure P) = ⌜P⌝%I.
  Proof. ss. Qed.

  Lemma red_sem_and n p q :
    interp n (and p q) = (interp n p ∧ interp n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_or n p q :
    interp n (or p q) = (interp n p ∨ interp n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_impl n p q :
    interp n (impl p q) = (interp n p → interp n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_univ n ty p :
    interp n (univ ty p) = (∀ (x : τ.(sType.interp) ty (_sProp n)), interp n (p x))%I.
  Proof. ss. Qed.

  Lemma red_sem_ex n ty p :
    interp n (ex ty p) = (∃ (x : τ.(sType.interp) ty (_sProp n)), interp n (p x))%I.
  Proof. ss. Qed.

  Lemma red_sem_empty n :
    interp n empty = emp%I.
  Proof. ss. Qed.
  
  Lemma red_sem_sepconj n p q :
    interp n (sepconj p q) = (interp n p ∗ interp n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_wand n p q :
    interp n (wand p q) = (interp n p -∗ interp n q)%I.
  Proof. ss. Qed.

  Lemma red_sem_persistently n p :
    interp n (persistently p) = (<pers> interp n p)%I.
  Proof. ss. Qed.

  Lemma red_sem_plainly n p :
    interp n (plainly p) = (IProp.Plainly (interp n p))%I.
  Proof. ss. Qed.

  Lemma red_sem_upd n p :
    interp n (upd p) = (#=> interp n p)%I.
  Proof. ss. Qed.

  Lemma red_sem_affinely n p :
    interp n (affinely p) = (<affine> interp n p)%I.
  Proof. ss. Qed.

  Lemma red_sem_intuitionistically n p :
    interp n (affinely (persistently p)) = (□ interp n p)%I.
  Proof. ss. Qed.

End RED.

Global Opaque sProp.interp.

(** Simple sProp reduction tactics. *)
Ltac red_sem_binary_once := (try rewrite ! @red_sem_sepconj;
                             try rewrite ! @red_sem_and;
                             try rewrite ! @red_sem_or;
                             try rewrite ! @red_sem_impl;
                             try rewrite ! @red_sem_wand
                            ).

Ltac red_sem_unary_once := (try rewrite ! @red_sem_atom;
                            try rewrite ! @red_sem_lift;
                            try rewrite ! @red_sem_pure;
                            try rewrite ! @red_sem_univ;
                            try rewrite ! @red_sem_ex;
                            try rewrite ! @red_sem_empty;
                            try rewrite ! @red_sem_persistently;
                            try rewrite ! @red_sem_plainly;
                            try rewrite ! @red_sem_upd;
                            try rewrite ! @red_sem_affinely;
                            try rewrite ! @red_sem_intuitionistically
                           ).

Ltac red_sem_binary := repeat red_sem_binary_once.
Ltac red_sem_unary := repeat red_sem_unary_once.
Ltac red_sem := repeat (red_sem_binary; red_sem_unary).

Ltac red_sem_binary_once_every := (try rewrite ! @red_sem_sepconj in *;
                                   try rewrite ! @red_sem_and in *;
                                   try rewrite ! @red_sem_or in *;
                                   try rewrite ! @red_sem_impl in *;
                                   try rewrite ! @red_sem_wand in *
                                  ).

Ltac red_sem_unary_once_every := (try rewrite ! @red_sem_atom in *;
                                  try rewrite ! @red_sem_lift in *;
                                  try rewrite ! @red_sem_pure in *;
                                  try rewrite ! @red_sem_univ in *;
                                  try rewrite ! @red_sem_ex in *;
                                  try rewrite ! @red_sem_empty in *;
                                  try rewrite ! @red_sem_persistently in *;
                                  try rewrite ! @red_sem_plainly in *;
                                  try rewrite ! @red_sem_upd in *;
                                  try rewrite ! @red_sem_affinely in *;
                                  try rewrite ! @red_sem_intuitionistically in *
                                 ).

Ltac red_sem_binary_every := repeat red_sem_binary_once.
Ltac red_sem_unary_every := repeat red_sem_unary_once.
Ltac red_sem_every := repeat (red_sem_binary_every; red_sem_unary_every).

(** Notations *)

Declare Scope sProp_scope.
Delimit Scope sProp_scope with F.
Bind Scope sProp_scope with sProp.sProp.

Local Open Scope sProp_scope.

Notation "'⌜' P '⌝'" := (sProp.pure P) : sProp_scope.
Notation "'⊤'" := ⌜True⌝ : sProp_scope.
Notation "'⊥'" := ⌜False⌝ : sProp_scope.

Notation "'⟨' A '⟩'" := (sProp.atom A) : sProp_scope.
Notation "⤉ P" := (sProp.lift P) (at level 20) : sProp_scope.

Notation "'<pers>' P" := (sProp.persistently P) : sProp_scope.
Notation "'<affine>' P" := (sProp.affinely P) : sProp_scope.
Notation "□ P" := (<affine> <pers> P) : sProp_scope.
Notation "■ P" := (sProp.plainly P) : sProp_scope.
Notation "|==> P" := (sProp.upd P) : sProp_scope.
Infix "∧" := (sProp.and) : sProp_scope.
Infix "∨" := (sProp.or) : sProp_scope.
Infix "→" := (sProp.impl) : sProp_scope.
Notation "¬ P" := (P → False) : sProp_scope.
Infix "∗" := (sProp.sepconj) : sProp_scope.
Infix "-∗" := (sProp.wand) : sProp_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : sProp_scope.
Notation f_forall A := (sProp.univ A).
Notation "∀'" := (f_forall _) (only parsing) : sProp_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%F)) ..)) : sProp_scope.
Notation f_exist A := (sProp.ex A).
Notation "∃'" := (f_exist _) (only parsing) : sProp_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%F)) ..)) : sProp_scope.
Notation "'emp'" := (sProp.empty) : sProp_scope.

