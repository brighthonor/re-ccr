From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.
From Coq Require Import Program Arith.
Require Import Coqlib PCM PCMAux IProp IPM SRF.

Module HRA.

  Section HRA.
  
  Class t := __HRA : GRA.t.

  Class subG (Γ: t) (Σ: GRA.t) : Type := {
    subG_map: nat -> nat;
    subG_prf: forall i, Σ (subG_map i) = Γ i;
  }.

  Coercion subG_map: subG >-> Funclass.

  Context `{sub: @subG Γ Σ}.
  
  Global Program Instance embed (i:nat) : @GRA.inG (Γ i) Σ := {
      inG_id := sub i;
    }.
  Next Obligation. i. symmetry. apply HRA.subG_prf. Qed.
  
  Global Program Instance in_subG `{M: URA.t} `{emb: @GRA.inG M Γ} : @GRA.inG M Σ := {
      inG_id := sub.(subG_map) emb.(GRA.inG_id);
      }.
  Next Obligation.
    i. destruct emb. subst. destruct sub. ss.
  Qed.

  End HRA.
  
End HRA.

Coercion HRA.subG_map: HRA.subG >-> Funclass.

Module gTyp.

  Class t: Type := __GTYP : GPF.t.

End gTyp.

Module SL.

  Section SL.

  Context `{sub: @HRA.subG Γ Σ}.
  Context `{τ: gTyp.t}.
    
  Global Instance domain : SRFDom.t := {
    dom := iProp;
    void := False%I;
  }.
    
  Variant shape : Type :=
    | _ownm i (r : Γ i)
    | _pure (P : Prop)
    | _and
    | _or
    | _impl
    | _univ i (ty : τ i)
    | _ex   i (ty : τ i)
    | _empty
    | _sepconj
    | _wand
    | _persistently
    | _plainly
    | _upd
  .
  
  Definition degree (s: shape) (Prev: Type) : Type :=
    match s with
    | _ownm i r => fin 0
    | _pure P => fin 0
    | _and => fin 2
    | _or => fin 2
    | _impl => fin 2
    | _univ i ty => PF.deg ty Prev
    | _ex   i ty => PF.deg ty Prev
    | _empty => fin 0
    | _sepconj => fin 2
    | _wand => fin 2
    | _persistently => fin 1
    | _plainly => fin 1
    | _upd => fin 1
    end.

  Global Instance syntax: PF.t := {
      shp := shape;
      deg := degree;
    }.

  Context `{α: @SRFMSynG.t}.
  
  Definition interp n (s: shape) : (degree s (SRFSyn._t n) -> SRFSyn.t n) -> (degree s (SRFSyn._t n) -> iProp) -> iProp :=
    match s with
    | _ownm i r => fun _ _ => OwnM r
    | _pure P => fun _ _ => Pure P
    | _and => fun _ P => And (P 0%fin) (P 1%fin)
    | _or => fun _ P => Or (P 0%fin) (P 1%fin)
    | _impl => fun _ P => Impl (P 0%fin) (P 1%fin)
    | _univ i ty => fun _ P => Univ P
    | _ex   i ty => fun _ P => Ex P
    | _empty => fun _ _ => Emp
    | _sepconj => fun _ P => Sepconj (P 0%fin) (P 1%fin)
    | _wand => fun _ P => Wand (P 0%fin) (P 1%fin)
    | _persistently => fun _ P => Persistently (P 0%fin)
    | _plainly => fun _ P => IProp.Plainly (P 0%fin)
    | _upd => fun _ P => Upd (P 0%fin)
    end.

  Global Instance t: SRFMSem.t := interp.

  Context `{@SRFMSemG.inG _ _ _ t β}.
  
  Definition ownm `{IN: @GRA.inG M Γ} {n} (r: M) : SRFSyn.t n.
    destruct IN. subst.
    refine ⟨ existT (_ownm _ r) _ ⟩%SRF.
    i. inv X.
  Defined.

  Definition pure {n} (P: Prop) : SRFSyn.t n.
    refine ⟨ existT (_pure P) _ ⟩%SRF.
    i. inv X.
  Defined.

  Definition and {n} (p1 p2: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_and) _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition or {n} (p1 p2: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_or) _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition impl {n} (p1 p2: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_impl) _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.
  
  Definition univ `{IN: @GPF.inG T τ} {n} (ty:T) (p: PF.deg ty (SRFSyn._t n) -> SRFSyn.t n) : SRFSyn.t n.
    destruct IN. subst.
    exact (⟨ existT (_univ _ ty : syntax.(PF.shp)) p ⟩)%SRF.
  Defined.

  Definition ex `{IN: @GPF.inG T τ} {n} (ty: T) (p: PF.deg ty (SRFSyn._t n) -> SRFSyn.t n) : SRFSyn.t n.
    destruct IN. subst.
    exact (⟨ existT (_ex _ ty : syntax.(PF.shp)) p ⟩)%SRF.
  Defined.

  Definition empty {n} : SRFSyn.t n.
    refine ⟨ existT (_empty) _ ⟩%SRF.
    i. inv X.
  Defined.
  
  Definition sepconj {n} (p1 p2: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_sepconj) _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.

  Definition wand {n} (p1 p2: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_wand) _ ⟩%SRF.
    i. destruct X.
    - exact p1.
    - exact p2.
  Defined.
  
  Definition persistently {n} (p: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_persistently) _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition plainly {n} (p: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_plainly) _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition upd {n} (p: SRFSyn.t n) : SRFSyn.t n.
    refine ⟨ existT (_upd) _ ⟩%SRF.
    i. inv X; [|inv H1].
    exact p.
  Defined.

  Definition affinely {n} (p : SRFSyn.t n) : SRFSyn.t n :=
    and empty p.

  End SL.

End SL.

Module SLRed.

  Section RED.

  Context `{τ: gTyp.t}.
  Context `{@HRA.subG Γ Σ}.
  Context `{@SRFMSemG.inG _ _ α SL.t β}.
  
  Lemma ownm `{@GRA.inG M Γ} n (r: M) :
    SRFSem.t n (SL.ownm r) = OwnM r.
  Proof.
    depdes H1. subst. unfold SL.ownm, eq_rect_r. ss.
    rewrite @SRFRed.cur. ss.
    f_equal. unfold HRA.in_subG, HRA.embed. ss.
    erewrite (UIP _ _ _ _). reflexivity.
  Qed.
  
  Lemma pure n P :
    SRFSem.t n (SL.pure P) = ⌜P⌝%I.
  Proof. unfold SL.pure. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma and n p q :
    SRFSem.t n (SL.and p q) = (SRFSem.t n p ∧ SRFSem.t n q)%I.
  Proof. unfold SL.and. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma or n p q :
    SRFSem.t n (SL.or p q) = (SRFSem.t n p ∨ SRFSem.t n q)%I.
  Proof. unfold SL.or. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma impl n p q :
    SRFSem.t n (SL.impl p q) = (SRFSem.t n p → SRFSem.t n q)%I.
  Proof. unfold SL.impl. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma univ `{@GPF.inG T τ} n ty p :
    SRFSem.t n (SL.univ ty p) = (∀ x, SRFSem.t n (p x))%I.
  Proof.
    destruct H1 eqn: EQ. subst.
    unfold SL.univ, eq_rect_r. ss.
    rewrite @SRFRed.cur. reflexivity.
  Qed.
  
  Lemma ex `{@GPF.inG T τ} n ty p :
    SRFSem.t n (SL.ex ty p) = (∃ x, SRFSem.t n (p x))%I.
  Proof.
    destruct H1 eqn: EQ. subst.
    unfold SL.ex, eq_rect_r. ss.
    rewrite @SRFRed.cur. reflexivity.
  Qed.
  
  Lemma empty n :
    SRFSem.t n SL.empty = emp%I.
  Proof. unfold SL.empty. rewrite @SRFRed.cur. reflexivity. Qed.
  
  Lemma sepconj n p q :
    SRFSem.t n (SL.sepconj p q) = (SRFSem.t n p ∗ SRFSem.t n q)%I.
  Proof. unfold SL.sepconj. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma wand n p q :
    SRFSem.t n (SL.wand p q) = (SRFSem.t n p -∗ SRFSem.t n q)%I.
  Proof. unfold SL.wand. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma persistently n p :
    SRFSem.t n (SL.persistently p) = (<pers> SRFSem.t n p)%I.
  Proof. unfold SL.persistently. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma plainly n p :
    SRFSem.t n (SL.plainly p) = (IProp.Plainly (SRFSem.t n p))%I.
  Proof. unfold SL.plainly. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma upd n p :
    SRFSem.t n (SL.upd p) = (#=> SRFSem.t n p)%I.
  Proof. unfold SL.upd. rewrite @SRFRed.cur. reflexivity. Qed.

  Lemma affinely n p :
    SRFSem.t n (SL.affinely p) = (<affine> SRFSem.t n p)%I.
  Proof. unfold SL.affinely. rewrite ->and, empty. reflexivity. Qed.

  Lemma intuitionistically n p :
    SRFSem.t n (SL.affinely (SL.persistently p)) = (□ SRFSem.t n p)%I.
  Proof. rewrite ->affinely, persistently. reflexivity. Qed.

  End RED.
End SLRed.

Global Opaque SL.ownm.
Global Opaque SL.pure.
Global Opaque SL.and.
Global Opaque SL.or.
Global Opaque SL.impl.
Global Opaque SL.univ.
Global Opaque SL.ex.
Global Opaque SL.empty.
Global Opaque SL.sepconj.
Global Opaque SL.wand.
Global Opaque SL.persistently.
Global Opaque SL.plainly.
Global Opaque SL.upd.
  
Global Opaque SRFSem.t.

(** Notations *)

Local Open Scope SRF_scope.

Notation "'⌜' P '⌝'" := (SL.pure P) : SRF_scope.
Notation "'⊤'" := ⌜True⌝ : SRF_scope.
Notation "'⊥'" := ⌜False⌝ : SRF_scope.

Notation "'<ownm>' r" := (SL.ownm r) (at level 20) : SRF_scope.
Notation "'<pers>' P" := (SL.persistently P) : SRF_scope.
Notation "'<affine>' P" := (SL.affinely P) : SRF_scope.
Notation "□ P" := (<affine> <pers> P) : SRF_scope.
Notation "■ P" := (SL.plainly P) : SRF_scope.
Notation "|==> P" := (SL.upd P) : SRF_scope.
Infix "∧" := (SL.and) : SRF_scope.
Infix "∨" := (SL.or) : SRF_scope.
Infix "→" := (SL.impl) : SRF_scope.
Notation "¬ P" := (P → False) : SRF_scope.
Infix "∗" := (SL.sepconj) : SRF_scope.
Infix "-∗" := (SL.wand) : SRF_scope.
Notation "P ==∗ Q" := (P -∗ |==> Q) : SRF_scope.
Notation f_forall A := (SL.univ A).
Notation "∀'" := (f_forall _) (only parsing) : SRF_scope.
Notation "∀ a .. z , P" := (f_forall _ (λ a, .. (f_forall _ (λ z, P%SRF)) ..)) : SRF_scope.
Notation f_exist A := (SL.ex A).
Notation "∃'" := (f_exist _) (only parsing) : SRF_scope.
Notation "∃ a .. z , P" := (f_exist _ (λ a, .. (f_exist _ (λ z, P%SRF)) ..)) : SRF_scope.
Notation "'emp'" := (SL.empty) : SRF_scope.

(* Simple sProp reduction tactics. *)
Ltac SL_red_binary := (try rewrite ! @SLRed.sepconj;
                       try rewrite ! @SLRed.and;
                       try rewrite ! @SLRed.or;
                       try rewrite ! @SLRed.impl;
                       try rewrite ! @SLRed.wand
                       ).

Ltac SL_red_unary := (try rewrite ! @SLRed.ownm;
                      try rewrite ! @SLRed.pure;
                      try rewrite ! @SLRed.univ;
                      try rewrite ! @SLRed.ex;
                      try rewrite ! @SLRed.empty;
                      try rewrite ! @SLRed.persistently;
                      try rewrite ! @SLRed.plainly;
                      try rewrite ! @SLRed.upd;
                      try rewrite ! @SLRed.affinely;
                      try rewrite ! @SLRed.intuitionistically
                      ).

Ltac SL_red := repeat (SL_red_binary; SL_red_unary).

Ltac SL_red_binary_all := (try rewrite ! @SLRed.sepconj in *;
                           try rewrite ! @SLRed.and in *;
                           try rewrite ! @SLRed.or in *;
                           try rewrite ! @SLRed.impl in *;
                           try rewrite ! @SLRed.wand in *
                           ).

Ltac SL_red_unary_all := (try rewrite ! @SLRed.ownm in *;
                         try rewrite ! @SLRed.pure in *;
                         try rewrite ! @SLRed.univ in *;
                         try rewrite ! @SLRed.ex in *;
                         try rewrite ! @SLRed.empty in *;
                         try rewrite ! @SLRed.persistently in *;
                         try rewrite ! @SLRed.plainly in *;
                         try rewrite ! @SLRed.upd in *;
                         try rewrite ! @SLRed.affinely in *;
                         try rewrite ! @SLRed.intuitionistically in *
                         ).

Ltac SL_red_all := repeat (SL_red_binary_all; SL_red_unary_all).

(* Module TestLock. *)
  
(* Section TESTLOCK. *)

(*   Context `{τ: sType.t}. *)
(*   Context `{Σ : GRA.t}. *)
  
(*   Variant atm {sProp : Type} : Type := *)
(*     | lock (p: sProp) : atm *)
(*     | unlock (p: sProp) : atm *)
(*   . *)
  
(*   Instance t : SAtom.t := { *)
(*     car sProp := @atm sProp; *)
(*     interp α n itp p := *)
(*         match p with *)
(*         | lock q => itp q -∗ itp q *)
(*         | unlock q => itp q ∗ itp q *)
(*         end%I *)
(*   }. *)
  
(* End TESTLOCK. *)

(* End TestLock. *)

(* Require Import RobustIndexedInvariants. *)

(* Module TestOwnI. *)
  
(* Section TestOwnI. *)

(*   Context `{τ: sType.t}. *)
(*   Context `{Σ: GRA.t}. *)
(*   Context `{@GRA.inG OwnEsRA Σ}. *)
(*   Context `{@GRA.inG (OwnIsRA sProp.sProp) Σ}. *)

(*   Definition xxx (u: positive) (n: nat) (i: positive) : sProp.sProp 0 := *)
(*     (⟨∃ p: iProp, p -∗ OwnI u n i ⟨OwnE u n ∅⟩⟩)%F. *)

(*   Check (sPropSem.interp 0 (xxx 1 0 1)). *)
(*   Check (OwnI 1 0 1 ⟨OwnE 1 0 ∅⟩). *)

(*   Check (∃ p: iProp, p -∗ False)%I. *)
  
(*   Lemma foo: sPropSem.interp 0 (xxx 1 0 1) = OwnI 1 0 1 ⟨OwnE 1 0 ∅⟩. *)
(*     reflexivity. *)
(*   Qed.   *)
  
  
(*   (* Context `{α: GAtom.t}. *) *)
   
(*   (* Variant atom {sProp : Type} : Type := *) *)
(*   (* | owni (u: positive) (i : positive) (p : sProp.t (sProp:=sProp)) *) *)
(*   (* . *) *)

(*   (* Context `{@GRA.inG (OwnIsRA sProp) Σ}. *) *)
  
(*   (* Program Instance t : SAtom.t := { *) *)
(*   (*   car sProp := @atom sProp; *) *)
(*   (* }. *) *)
(*   (* Next Obligation. *) *)
(*   (*   intros. destruct X. *) *)
(*   (*   Set Printing All. *) *)
(*   (*   exact (@OwnI _ sProp.sProp _ u n i p). *) *)
  
(*   (*   interp α n itp p := *) *)
(*   (*     match p with *) *)
(*   (*     | owni u i p => @OwnI _ sProp.sProp _ u _ i p *) *)
(*   (*     end *) *)
(*   (* }. *) *)

(* End TestOwnI. *)

(* End TestOwnI. *)

  
  (* Definition embed `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r: Σ) : Γ := *)
  (*   fun i => eq_rect _ (@URA.car) (r (m i)) _ (m.(subG_prf) i). *)

  (* Lemma embed_wf `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r: Σ) *)
  (*     (WF: URA.wf r): *)
  (*   URA.wf (embed r). *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   revert WF. unfold URA.wf, embed. unseal "ra". ss. *)
  (*   i. specialize (WF (m k)). revert WF. *)
  (*   rewrite <-(m.(subG_prf) k). ss. *)
  (* Qed. *)

  (* Lemma embed_extends `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (r0 r1: Σ) *)
  (*     (EXT: URA.extends r0 r1): *)
  (*   URA.extends (embed r0) (embed r1). *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   rr in EXT. des. subst. exists (embed ctx). extensionality k. *)
  (*   unfold embed, URA.add. unseal "ra". simpl. *)
  (*   rewrite <-(m.(subG_prf) k). ss. *)
  (* Qed. *)
  
  (* Program Definition lift `{Γ: GRA.t} `{Σ: GRA.t} `{m: @subG Γ Σ} (P: @iProp Γ): @iProp Σ := *)
  (*   iProp_intro (fun r => P (embed r)) _. *)
  (* Next Obligation. *)
  (*   i. ss. eapply iProp_mono; eauto using embed_wf, embed_extends. *)
  (* Qed. *)

  (* Lemma iprop_extensionality `{Σ: GRA.t} (P Q: iProp) *)
  (*     (EQ: iProp_pred P = iProp_pred Q): *)
  (*   P = Q. *)
  (* Proof. *)
  (*   destruct P eqn: EQP. subst. *)
  (*   destruct Q eqn: EQQ. subst. *)
  (*   ss. subst. f_equal. eapply proof_irrelevance. *)
  (* Qed. *)
  
  (* Lemma lift_ownM `{Γ: GRA.t} `{Σ: GRA.t} `{sub: @subG Γ Σ} {M: URA.t} {emb: @GRA.inG M Γ} (m: M): *)
  (*   lift (@OwnM Γ M emb m) = @OwnM Σ M (in_subG sub emb) m. *)
  (* Proof. *)
  (*   Local Transparent GRA.to_URA. *)
  (*   apply iprop_extensionality. ss. *)
  (*   extensionality i. unfold OwnM, embed, Own, URA.extends. uiprop. *)
  (*   destruct emb, sub. subst. *)
  (*   rename i into r. apply propositional_extensionality. split; i; des. *)
  (*   - exists (fun k => *)
  (*               match Nat.eq_dec (subG_map0 inG_id) k with *)
  (*               | left H => *)
  (*                   eq_rect _ (fun k => @URA.car (Σ k)) *)
  (*                   (eq_rect_r (@URA.car) (ctx inG_id) (subG_prf0 inG_id)) _ H *)
  (*               | _ => r k *)
  (*               end). *)
  (*     extensionality k. ss. *)
  (*     assert (EQ:= equal_f_dep H inG_id). clear H. *)
  (*     unfold URA.add in *. unseal "ra". ss. *)
  (*     unfold GRA.embed in *. ss. des_ifs; r_solve. ss. *)
  (*     unfold URA.add in *. unseal "ra". unfold PCM.GRA.cast_ra. clear Heq. *)
  (*     revert EQ. rewrite (UIP_refl _ _ e). ss. clear e. *)
  (*     rewrite (UIP_refl _ _ e0). ss. clear e0. *)
  (*     generalize (in_subG_obligation_1 Γ Σ (Γ inG_id)  *)
  (*         {| subG_map := subG_map0; subG_prf := subG_prf0 |} *)
  (*         {| GRA.inG_id := inG_id; GRA.inG_prf := eq_refl |}). *)
  (*     generalize (subG_prf0 inG_id). ss. *)
  (*     unfold eq_rect_r. i. rewrite (UIP _ _ _ (eq_sym e) e0). *)
  (*     revert_until r. generalize (subG_map0 inG_id) as j. *)
  (*     intros j. generalize (r j) as r'. clear r. *)
  (*     generalize (Σ j) as A. clear j. clear Σ subG_prf0 subG_map0. *)
  (*     i. subst. rewrite (UIP_refl _ _ e0). ss. *)
  (*   - ss.       *)
  (*     exists (fun k => *)
  (*               match Nat.eq_dec inG_id k with *)
  (*               | left H => eq_rect _ (@URA.car) (ctx (subG_map0 k)) _ (subG_prf0 k)  *)
  (*               | _ => eq_rect _ (@URA.car) (r (subG_map0 k)) _ (subG_prf0 k) *)
  (*               end). *)
  (*     extensionality k. *)
  (*     assert (EQ:= equal_f_dep H (subG_map0 inG_id)). clear H. *)
  (*     unfold URA.add in *. unseal "ra". ss. *)
  (*     unfold GRA.embed in *. ss. des_ifs; r_solve. ss. *)
  (*     unfold URA.add in *. unseal "ra". clear Heq e. *)
  (*     revert EQ. unfold PCM.GRA.cast_ra. *)
  (*     rewrite (UIP_refl _ _ e0). ss. clear e0. *)
  (*     generalize (in_subG_obligation_1 Γ Σ (Γ k) *)
  (*         {| subG_map := subG_map0; subG_prf := subG_prf0 |} *)
  (*         {| GRA.inG_id := k; GRA.inG_prf := eq_refl |}). ss. *)
  (*     generalize (subG_prf0 k). generalize (subG_map0 k). *)
  (*     intros j. generalize (r j) as r'. clear r. revert m. *)
  (*     generalize (ctx j). clear ctx. *)
  (*     generalize (Σ j) as A. clear j. i. subst. *)
  (*     rewrite (UIP_refl _ _ e0). ss. *)
  (* Qed. *)
