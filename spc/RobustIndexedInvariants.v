From stdpp Require Import coPset gmap namespaces.
From sflib Require Import sflib.
From iris Require Import bi.big_op.
From iris Require base_logic.lib.invariants.

Require Import Coqlib PCM IProp IPM.

Require Import Coq.Logic.ClassicalEpsilon.
Require Import Coq.Logic.IndefiniteDescription.

(* Require ClassicalFacts. *)
(* Require FunctionalExtensionality. *)
(* Require ChoiceFacts. *)
(* Require Coq.Logic.Epsilon. *)
(* Require Classical_Prop. *)
(* Require Logic.Classical_Pred_Type. *)
(* Require Import Coq.Logic.ProofIrrelevance. *)
(* Require Import Coq.Logic.ClassicalEpsilon. *)




Lemma dependent_functional_choice (A : Type) (B : A -> Type) :
  forall R : forall x : A, B x -> Prop,
    (forall x : A, exists y : B x, R x y) ->
    (exists f : (forall x : A, B x), forall x : A, R x (f x)).
Proof.
  eapply ChoiceFacts.non_dep_dep_functional_choice.
  clear. exact functional_choice.
Qed.  



Section POINTWISE.

  Lemma unfold_pointwise_add X (M: URA.t) (f0 f1: (X ==> M)%ra)
    :
    f0 ⋅ f1 = (fun x => f0 x ⋅ f1 x).
  Proof.
    ur. ur. auto.
  Qed.

  Lemma updatable_set_impl (M: URA.t)
        (P0 P1: M -> Prop)
        (IMPL: forall r, URA.wf r -> P0 r -> P1 r)
        (m: M)
        (UPD: URA.updatable_set m P0)
    :
    URA.updatable_set m P1.
  Proof.
    ii. eapply UPD in WF; eauto. des.
    esplits; eauto. eapply IMPL; auto.
    eapply URA.wf_mon. eauto.
  Qed.

  Lemma pointwise_extends A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.extends (f0 a) (f1 a))
    :
    URA.extends f0 f1.
  Proof.
    hexploit (choice (fun a ctx => f1 a = ((f0 a) ⋅ ctx))).
    { i. specialize (UPD x). r in UPD. des. eauto. }
    i. des. exists f.
    rewrite (@unfold_pointwise_add A M). extensionality a. auto.
  Qed.

  Lemma pointwise_updatable A (M: URA.t)
        (f0 f1: (A ==> M)%ra)
        (UPD: forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_updatable_set A (M: URA.t)
        (f: (A ==> M)%ra)
        (P: A -> M -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii. hexploit (choice (fun a m => P a m /\ URA.wf (m ⋅ ctx a))).
    { i. eapply (UPD x). ur in WF. auto. }
    i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Definition maps_to_res {A} {M: URA.t}
             a m: (A ==> M)%ra :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else URA.unit.

  Lemma maps_to_res_add A (M: URA.t)
        (a: A) (m0 m1: M)
    :
    maps_to_res a m0 ⋅ maps_to_res a m1
    =
      maps_to_res a (m0 ⋅ m1).
  Proof.
    extensionality a'. unfold maps_to_res. ur. des_ifs.
    { ur. auto. }
    { r_solve. }
  Qed.

  Lemma maps_to_updatable A (M: URA.t)
        (a: A) (m0 m1: M)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (maps_to_res a m0) (maps_to_res a m1).
  Proof.
    eapply pointwise_updatable. i.
    unfold maps_to_res. des_ifs.
  Qed.

  Lemma maps_to_updatable_set A (M: URA.t)
        (a: A) (m: M) (P: M -> Prop)
        (UPD: URA.updatable_set m P)
    :
    URA.updatable_set
      (maps_to_res a m)
      (fun f => exists (m1: M), f = maps_to_res a m1 /\ P m1).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionality a'. unfold maps_to_res. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Definition map_update {A} {M: URA.t}
             (f: (A ==> M)%ra) a m :=
    fun a' => if excluded_middle_informative (a' = a)
              then m
              else f a'.

End POINTWISE.

Global Opaque URA.unit.

Section UNIT.

  Program Instance Unit : URA.t := {| URA.unit := tt; URA._add := fun _ _ => tt; URA._wf := fun _ => True; URA.core := fun _ => tt; |}.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. destruct a. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. unseal "ra". ss. Qed.
  Next Obligation. unseal "ra". i. ss. Qed.
  Next Obligation. unseal "ra". i. destruct a. ss. Qed.
  Next Obligation. ss. Qed.
  Next Obligation. unseal "ra". i. exists tt. ss. Qed.

  Lemma Unit_wf : forall x, @URA.wf Unit x.
  Proof. unfold URA.wf. unseal "ra". ss. Qed.

End UNIT.
Global Opaque Unit.


Section URA_PROD.

  Lemma unfold_prod_add (M0 M1 : URA.t) : @URA.add (URA.prod M0 M1) = fun '(a0, a1) '(b0, b1) => (a0 ⋅ b0, a1 ⋅ b1).
  Proof. rewrite URA.unfold_add. extensionalities r0 r1. destruct r0, r1. ss. Qed.

  Lemma unfold_prod_wf (M0 M1 : URA.t) : @URA.wf (URA.prod M0 M1) = fun r => URA.wf (fst r) /\ URA.wf (snd r).
  Proof. rewrite URA.unfold_wf. extensionalities r. destruct r. ss. Qed.

End URA_PROD.

Section PWDEP.

  Lemma pointwise_dep_updatable
        A (Ms : A -> URA.t)
        (f0 f1 : @URA.pointwise_dep A Ms)
        (UPD : forall a, URA.updatable (f0 a) (f1 a))
    :
    URA.updatable f0 f1.
  Proof.
    ii. ur. i. ur in H. specialize (H k).
    eapply (UPD k); eauto.
  Qed.

  Lemma pointwise_dep_updatable_set
        A (Ms : A -> URA.t)
        (f : @URA.pointwise_dep A Ms)
        (P : forall (a : A), (Ms a) -> Prop)
        (UPD: forall a, URA.updatable_set (f a) (P a))
    :
    URA.updatable_set f (fun f' => forall a, P a (f' a)).
  Proof.
    ii.
    set (R := fun (a : A) => (fun (m : Ms a) => P a m /\ URA.wf (m ⋅ ctx a))).
    hexploit (dependent_functional_choice _ _ R).
    { subst R. ss. i. eapply (UPD x). ur in WF. auto. }
    subst R. ss. i. des. exists f0. splits; auto.
    { i. specialize (H a). des. auto. }
    { ur. i. specialize (H k). des. auto. }
  Qed.

  Program Definition maps_to_res_dep {A : Type} {Ms : A -> URA.t} (a : A) (m : Ms a)
    : @URA.pointwise_dep A Ms.
  Proof.
    ii. destruct (excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact ε.
  Defined.

  Lemma maps_to_res_dep_eq
        A (Ms : A -> URA.t)
        (a : A)
        (m : Ms a)
    :
    (@maps_to_res_dep A Ms a m) a = m.
  Proof.
    unfold maps_to_res_dep. des_ifs. unfold eq_rect_r.
    rewrite <- Eqdep.EqdepTheory.eq_rect_eq. auto.
  Qed.

  Lemma maps_to_res_dep_neq
        A (Ms : A -> URA.t)
        (a b : A)
        (m : Ms a)
    :
    a <> b -> (@maps_to_res_dep A Ms a m) b = ε.
  Proof.
    i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_add
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
    :
    @maps_to_res_dep _ Ms a m0 ⋅ @maps_to_res_dep _ Ms a m1 = @maps_to_res_dep _ Ms a (m0 ⋅ m1).
  Proof.
    extensionalities a'. unfold URA.add at 1. unseal "ra". ss.
    destruct (excluded_middle_informative (a' = a)).
    - subst a'. rewrite ! @maps_to_res_dep_eq. auto.
    - rewrite ! @maps_to_res_dep_neq; auto. apply URA.unit_id.
  Qed.

  Lemma maps_to_res_dep_updatable
        A (Ms : A -> URA.t)
        (a : A)
        (m0 m1 : Ms a)
        (UPD: URA.updatable m0 m1)
    :
    URA.updatable (@maps_to_res_dep A Ms a m0) (@maps_to_res_dep A Ms a m1).
  Proof.
    eapply pointwise_dep_updatable. i. unfold maps_to_res_dep. des_ifs.
  Qed.

  Lemma maps_to_res_dep_updatable_set
        A (Ms : A -> URA.t)
        (a : A)
        (m : Ms a)
        (P : forall (a' : A), Ms a' -> Prop)
        (UPD: URA.updatable_set m (P a))
    :
    URA.updatable_set
      (@maps_to_res_dep A Ms a m)
      (fun f => exists (m1 : Ms a), f = @maps_to_res_dep A Ms a m1 /\ (P a m1)).
  Proof.
    eapply updatable_set_impl; cycle 1.
    { eapply pointwise_dep_updatable_set.
      instantiate (1:= fun a' m' => (a' = a -> P a' m') /\ (a' <> a -> m' = URA.unit)).
      ii. unfold maps_to_res_dep in WF. des_ifs.
      { exploit UPD; eauto. i. des. esplits; eauto. ss. }
      { exists URA.unit. splits; ss. }
    }
    { i. ss. exists (r a). splits; auto.
      { extensionalities a'. unfold maps_to_res_dep. des_ifs.
        specialize (H0 a'). des. auto.
      }
      { specialize (H0 a). des. auto. }
    }
  Qed.

  Program Definition maps_to_res_dep_update {A} {Ms: A -> URA.t}
          (f: @URA.pointwise_dep A Ms) a (m : Ms a) : @URA.pointwise_dep A Ms.
  Proof.
    ii. destruct (excluded_middle_informative (k = a)).
    - subst k. exact m.
    - exact (f k).
  Qed.

End PWDEP.



Tactic Notation "unfold_prod" :=
  try rewrite ! unfold_prod_add;
  rewrite unfold_prod_wf;
  simpl.

Tactic Notation "unfold_prod" hyp(H) :=
  try rewrite ! unfold_prod_add in H;
  rewrite unfold_prod_wf in H;
  simpl in H;
  let H1 := fresh H in
  destruct H as [H H1].

From iris.bi Require Import derived_connectives updates.
From iris.prelude Require Import options.

Section PWAUX.

  Context {K: Type} `{M: URA.t}.
  Let RA := URA.pointwise K M.

  Lemma pw_extends (f0 f1: K -> M) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; eauto. Qed.

  Lemma pw_wf: forall (f: K -> M) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pw_add_disj_wf
        (f g: K -> M)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. specialize (DISJ k). des; rewrite DISJ.
    - rewrite URA.unit_idl; eauto.
    - rewrite URA.unit_id; eauto.
  Qed.

  Lemma pw_insert_wf: forall `{EqDecision K} (f: K -> M) k v (WF: URA.wf (f: @URA.car RA)) (WFV: URA.wf v),
      <<WF: URA.wf (<[k:=v]> f: @URA.car RA)>>.
  Proof.
    i. unfold insert, functions.fn_insert. ur. ii. des_ifs. ur in WF. eapply WF.
  Qed.

  Lemma pw_lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

End PWAUX.

Section PWDAUX.

  Context {K: Type} `{M: K -> URA.t}.
  Let RA := @URA.pointwise_dep K M.

  Lemma pwd_extends (f0 f1: forall (k : K), M k) (EXT: @URA.extends RA f0 f1): <<EXT: forall k, URA.extends (f0 k) (f1 k)>>.
  Proof. ii. r in EXT. des. subst. ur. ss. eexists; eauto. Qed.

  Lemma pwd_wf: forall (f: forall (k : K), M k) (WF: URA.wf (f: @URA.car RA)), <<WF: forall k, URA.wf (f k)>>.
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

  Lemma pwd_add_disj_wf
        (f g: forall (k : K), M k)
        (WF0: URA.wf (f: @URA.car RA))
        (WF1: URA.wf (g: @URA.car RA))
        (DISJ: forall k, <<DISJ: f k = ε \/ g k = ε>>)
    :
      <<WF: URA.wf ((f: RA) ⋅ g)>>
  .
  Proof.
    ii; ss. ur. i. ur in WF0. ur in WF1. specialize (DISJ k). des; rewrite DISJ.
    - rewrite URA.unit_idl; eauto.
    - rewrite URA.unit_id; eauto.
  Qed.

  Lemma pwd_lookup_wf: forall (f: @URA.car RA) k (WF: URA.wf f), URA.wf (f k).
  Proof. ii; ss. rewrite URA.unfold_wf in WF. ss. Qed.

End PWDAUX.

Module Gset.
  Import gmap.

  Definition add (x y : option (gset positive)) : option (gset positive) :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : URA.t :=
    {|
      URA.car := option (gset positive);
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    unfold add. intros [] []; des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". ss. intros []; des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. des_ifs.
    { f_equal. set_solver. }
    set_solver.
  Qed.

End Gset.


Module CoPset.

  Definition add (x y : option coPset) : option coPset :=
    match x, y with
    | Some x, Some y => if decide (x ## y) then Some (x ∪ y) else None
    | _, _ => None
    end.

  Program Instance t : URA.t :=
    {|
      URA.car := option coPset;
      URA.unit := Some ∅;
      URA._wf := fun x => match x with Some _ => True | None => False end;
      URA._add := add;
      URA.core := fun x => Some ∅;
    |}.
  Next Obligation.
    intros [] []; ss. des_ifs. f_equal. set_solver.
  Qed.
  Next Obligation.
    unfold add. intros [] [] []; des_ifs.
    { f_equal. set_solver. }
    all: set_solver.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    unseal "ra". ss.
  Qed.
  Next Obligation.
    unseal "ra". intros [] []; ss.
  Qed.
  Next Obligation.
    unseal "ra". unfold add. intros []; des_ifs.
    - f_equal. set_solver.
    - set_solver.
  Qed.
  Next Obligation.
    intros []; ss.
  Qed.
  Next Obligation.
    unseal "ra". i. exists (Some ∅). ss. f_equal. set_solver.
  Qed.

End CoPset.

Local Notation index := nat.

Section INDEXED_INVARIANT_SET.

  Context `{Σ : GRA.t}.

  Class IInvSet (Vars : index -> Type) :=
    { prop : forall (i : index), (Vars i) -> iProp }.

  (* Class IInvIn {Vars : index -> Type} `{IInvSet Vars} (n : index) (P : iProp) := *)
  (*   { inhabitant : Vars n *)
  (*   ; inhabitant_eq : prop _ inhabitant = P *)
  (*   }. *)

  Definition InvSetRA (Vars : index -> Type) (n : index) : URA.t :=
    (Auth.t (positive ==> URA.agree (Vars n)))%ra.

  Definition IInvSetRA (Vars : index -> Type) : URA.t :=
    @URA.pointwise_dep index (InvSetRA Vars).

  Definition OwnEsRA : URA.t := URA.pointwise index CoPset.t.
  Definition OwnDsRA : URA.t := URA.pointwise index (Auth.t Gset.t).

End INDEXED_INVARIANT_SET.

Section PCM_OWN.

  Context `{Σ : GRA.t}.

  Definition OwnE `{@GRA.inG OwnEsRA Σ} (n : index) (E : coPset) :=
    OwnM (@maps_to_res index CoPset.t n (Some E)).

  Definition OwnD `{@GRA.inG OwnDsRA Σ} (n : index) (D : gset positive) :=
    OwnM (@maps_to_res index (Auth.t Gset.t) n (Auth.white (Some D : Gset.t))).

  Definition OwnD_auth `{@GRA.inG OwnDsRA Σ} (n : index) :=
    (∃ D, OwnM (@maps_to_res index (Auth.t Gset.t) n (Auth.black (Some D : Gset.t))))%I.

  Definition OwnI_white {Vars} (n : index) (i : positive) (p : Vars n) : IInvSetRA Vars :=
    @maps_to_res_dep index (@InvSetRA Vars)
                     n
                     (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p)))).

  Definition OwnI {Vars} `{@GRA.inG (IInvSetRA Vars) Σ} (n : index) (i : positive) (p : Vars n) :=
    OwnM (OwnI_white n i p).

  Lemma OwnE_index_diff `{@GRA.inG OwnEsRA Σ} n1 n2 (E : coPset) :
    (E <> ∅) -> OwnE n1 E ∗ OwnE n2 E ⊢ ⌜n1 <> n2⌝.
  Proof.
    intros NEMP.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. unfold maps_to_res in WF. rewrite /URA.wf /URA.add in WF. unseal "ra".
    ss. intros EQ. subst n2. specialize (WF n1). des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss. des_ifs. set_solver.
  Qed.

  Lemma OwnE_exploit `{@GRA.inG OwnEsRA Σ} n (E1 E2 : coPset) :
    OwnE n E1 ∗ OwnE n E2 ⊢ ⌜E1 ## E2⌝.
  Proof.
    iIntros "[H1 H2]". iCombine "H1 H2" as "H". iPoseProof (OwnM_valid with "H") as "%WF".
    iPureIntro. rewrite /URA.wf /URA.add in WF. unseal "ra". ss.
    specialize (WF n). unfold maps_to_res in WF. des_ifs.
    rewrite /URA.wf /URA.add in WF. unseal "ra". ss; des_ifs.
  Qed.

  Lemma OwnE_union `{@GRA.inG OwnEsRA Σ} n (E1 E2 : coPset) :
    OwnE n E1 ∗ OwnE n E2 ⊢ OwnE n (E1 ∪ E2).
  Proof.
    iIntros "H". iPoseProof (OwnE_exploit with "H") as "%D".
    iRevert "H". iApply from_sep. eapply from_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. ss. extensionalities k. unseal "ra".
    des_ifs; ss.
    - unfold URA.add. unseal "ra". ss. des_ifs.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_disjoint `{@GRA.inG OwnEsRA Σ} n (E1 E2 : coPset) :
    E1 ## E2 -> OwnE n (E1 ∪ E2) ⊢ OwnE n E1 ∗ OwnE n E2.
  Proof.
    i. unfold OwnE.
    iApply into_sep. eapply into_sep_ownM.
    unfold IsOp, maps_to_res, URA.add. unseal "ra". ss.
    extensionalities k. des_ifs.
    - unfold URA.add. unseal "ra". ss. des_ifs.
    - rewrite URA.unit_id. auto.
  Qed.

  Lemma OwnE_subset `{@GRA.inG OwnEsRA Σ} n (E1 E2 : coPset) :
    E1 ⊆ E2 -> OwnE n E2 ⊢ OwnE n E1 ∗ (OwnE n E1 -∗ OwnE n E2).
  Proof.
    iIntros (SUB) "E".
    assert (E2 = E1 ∪ E2 ∖ E1) as EQ.
    { eapply leibniz_equiv. eapply union_difference. ss. }
    rewrite EQ.
    iPoseProof (OwnE_disjoint with "E") as "[E1 E2]"; [set_solver|].
    iFrame. iIntros "E1".
    iApply OwnE_union. iFrame.
  Qed.

  Global Instance OwnI_persistent {Vars} `{@GRA.inG (IInvSetRA Vars) Σ}
    n i p : Persistent (OwnI n i p).
  Proof.
    unfold OwnI, OwnI_white.
    remember (@maps_to_res_dep index (InvSetRA Vars) n (Auth.white (@maps_to_res positive (URA.agree (Vars n)) i (Some (Some p))))) as r.
    unfold Persistent. iIntros "H".
    iPoseProof (@OwnM_persistently _ _ H _ with "H") as "#HP". iModIntro.
    replace r with (URA.core r) at 2; auto.
    subst. unfold maps_to_res_dep, maps_to_res. ss. extensionalities k. des_ifs.
  Qed.

End PCM_OWN.

Section WORLD_SATISFACTION.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Variable n : index.
  Local Notation Var := (Vars n).

  Definition inv_auth_black (I : gmap positive Var) : IInvSetRA Vars :=
    @maps_to_res_dep index _
                     n (@Auth.black (positive ==> URA.agree Var)%ra
                                    (fun (i : positive) => Some <$> (I !! i))).

  Definition inv_auth (I : gmap positive Var) := OwnM (inv_auth_black I).

  Definition inv_satall (I : gmap positive Var) :=
    ([∗ map] i ↦ p ∈ I, (prop n p) ∗ OwnD n {[i]} ∨ OwnE n {[i]})%I.

  Definition wsat : iProp := (OwnD_auth n ∗ ∃ I, inv_auth I ∗ inv_satall I)%I.


  Lemma alloc_name φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnD_auth n ⊢ |==> OwnD_auth n ∗ ∃ i, ⌜φ i⌝ ∧ OwnD n {[i]}.
  Proof.
    iIntros "[% DA]". specialize (INF (fun _ => Some D) n). ss. des.
    assert (@URA.updatable
              OwnDsRA
              (maps_to_res n (Auth.black (Some D : Gset.t)))
              ((maps_to_res n (Auth.black (Some (D ∪ {[i]}) : Gset.t)))
                 ⋅
                 (maps_to_res n (Auth.white (Some {[i]} : Gset.t))))) as UPD.
    { rewrite maps_to_res_add. apply maps_to_updatable.
      ii. ur in H3. des_ifs. des. rewrite URA.unit_idl in H3.
      unfold URA.extends in H3. des. ur in H3.
      ur. rewrite URA.unit_idl. split.
      { exists ctx. ur. des_ifs; ss.
        2:{ des_ifs. set_solver. }
        des_ifs.
        2:{ set_solver. }
        f_equal. set_solver.
      }
      { ur. ss. }
    }
    iMod (OwnM_Upd UPD with "DA") as "[DA D]".
    iModIntro. iSplitL "DA".
    { iExists _. iFrame. }
    { iExists i. iFrame. auto. }
  Qed.

  Lemma wsat_OwnI_alloc_gen p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsat ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsat).
  Proof.
    iIntros "[DA [% [AUTH SAT]]]".
    iMod (alloc_name (fun i => i ∉ dom I /\ φ i) with "DA") as "[DA [% [[%iI %iφ] D]]]".
    { i.
      set (uni := fun n => match E n with
                        | None => None
                        | Some G => Some (G ∪ dom I)
                        end).
      specialize (INF uni n0). subst uni. ss. des_ifs.
      des. eapply not_elem_of_union in INF. des. esplits; eauto. }
    pose (<[i:=p]> I) as I'.

    assert (URA.updatable
              (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I !! i))) : IInvSetRA Vars)
              ((maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun i => Some <$> (I' !! i))) : IInvSetRA Vars)
                 ⋅
                 (maps_to_res_dep n (Auth.white (@maps_to_res _ (URA.agree Var) i (Some (Some p)))) : IInvSetRA Vars))).
    { setoid_rewrite maps_to_res_dep_add. apply maps_to_res_dep_updatable.
      apply Auth.auth_alloc. ii. des. rewrite URA.unit_idl in FRAME. subst. split.
      { rr; unseal "ra". ss. intro. rr; unseal "ra". destruct (I' !! k); ss. }
      rr. subst I'.
      unfold URA.add. unseal "ra". ss.
      extensionalities j. unfold maps_to_res. des_ifs.
      - rewrite lookup_insert. rewrite not_elem_of_dom_1; ss.
        unfold URA.add. unseal "ra". ss.
      - rewrite URA.unit_idl. rewrite lookup_insert_ne; eauto.
    }
    unfold inv_auth, inv_satall.
    iMod (OwnM_Upd H3 with "AUTH") as "[AUTH NEW]". iModIntro.

    iSplit.
    - iExists i. iFrame. ss.
    - iIntros "P". unfold wsat. iFrame. iExists I'. iFrame.
      unfold inv_satall. subst I'.
      iApply big_sepM_insert.
      { apply not_elem_of_dom_1; ss. }
      iSplitL "P D"; ss. iLeft. iFrame.
  Qed.

  Lemma wsat_OwnI_alloc p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsat ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsat.
  Proof.
    iIntros "[W P]".
    iMod (wsat_OwnI_alloc_gen with "W") as "[I W]"; eauto.
    iFrame. iModIntro. iApply "W". iFrame.
  Qed.

  Lemma wsat_OwnI_open i p :
    OwnI n i p ∗ wsat ∗ OwnE n {[i]} ⊢ |==> prop n p ∗ wsat ∗ OwnD n {[i]}.
  Proof.
    iIntros "(I & [DA [% [AUTH SAT]]] & EN)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF. apply (pwd_lookup_wf _ n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    2: { iCombine "EN H1" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
         exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
         specialize (WF n). des_ifs. unfold URA.wf, URA.add in WF. unseal "ra".
         ss. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame.
  Qed.

  Lemma wsat_OwnI_close i p :
    OwnI n i p ∗ wsat ∗ prop n p ∗ OwnD n {[i]} ⊢ |==> wsat ∗ OwnE n {[i]}.
  Proof.
    iIntros "(I & [DA [% [AUTH SAT]]] & P & DIS)". iModIntro.
    unfold OwnI, inv_auth, inv_satall.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    assert (Hip : I !! i = Some p).
    { unfold inv_auth_black, OwnI_white in WF. setoid_rewrite maps_to_res_dep_add in WF.
      unfold maps_to_res_dep, maps_to_res in WF. apply (pwd_lookup_wf _ n) in WF. ss. des_ifs.
      unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
      apply Auth.auth_included in WF. rename WF into EXTENDS.
      apply pw_extends in EXTENDS. specialize (EXTENDS i).
      des_ifs. clear e e0.
      rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
      destruct (I !! i) eqn: E.
      - destruct ctx; ss; des_ifs.
      - destruct ctx; ss; des_ifs.
    }
    clear WF.
    iDestruct "AUTH" as "[AUTH I]".
    iPoseProof (big_sepM_delete _ _ _ _ Hip with "SAT") as "[[[H1 H2]|H1] SAT]".
    { iCombine "DIS H2" as "F". iPoseProof (OwnM_valid with "F") as "%WF".
      exfalso. unfold maps_to_res, URA.wf, URA.add in WF. unseal "ra". ss.
      specialize (WF n). des_ifs.
      unfold URA.wf, URA.add in WF. unseal "ra". ss.
      ur in WF. des_ifs. set_solver.
    }
    iFrame. unfold wsat. iExists I. iFrame. unfold inv_satall.
    iApply (big_sepM_delete _ _ _ _ Hip). iFrame. iLeft. iFrame.
  Qed.

  Lemma wsat_init :
    OwnM (maps_to_res n (Auth.black (Some ∅ : Gset.t)) : OwnDsRA)
         ∗
         OwnM (maps_to_res_dep n (@Auth.black (positive ==> URA.agree Var)%ra (fun (i : positive) => None)) : IInvSetRA _)
         ⊢ wsat.
  Proof.
    iIntros "[H1 H2]". iSplitL "H1".
    { iExists ∅. iFrame. }
    { iExists ∅. iFrame. unfold inv_satall. iApply big_sepM_empty. ss. }
  Qed.

End WORLD_SATISFACTION.

Section WSATS.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{@IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Definition OwnDs_auth_black (x : index) : OwnDsRA :=
    (fun n => if (lt_dec n x)
           then ε
           else Auth.black (Some ∅ : Gset.t)).

  Definition OwnDs_auth (x : index) := OwnM (OwnDs_auth_black x).

  Definition wsat_auth_black (x : index) : IInvSetRA Vars :=
    (fun n => if (lt_dec n x)
           then ε
           else @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)).

  Definition wsat_auth (x : index) := OwnM (wsat_auth_black x).

  (* wsat n for all n < x *)
  Definition wsats (x : index) := ([∗ list] n ∈ (seq 0 x), wsat n)%I.

  Lemma unfold_wsats x :
    wsats (S x) ⊢ (wsats x ∗ wsat x)%I.
  Proof.
    iIntros "A". unfold wsats. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
    2:{ rewrite seq_S. ss. }
    iPoseProof (big_sepL_app with "A") as "[A [B C]]". ss. iFrame.
  Qed.

  Lemma fold_wsats x :
    (wsats x ∗ wsat x)%I ⊢ wsats (S x).
  Proof.
    iIntros "A". unfold wsats. replace (seq 0 (S x)) with (seq 0 x ++ [x]).
    2:{ rewrite seq_S. ss. }
    iApply big_sepL_app. ss. iDestruct "A" as "[A B]". iFrame.
  Qed.



  Lemma wsats_init_zero :
    OwnM ((fun n => @Auth.black (positive ==> URA.agree (Vars n))%ra (fun _ => None)) : IInvSetRA Vars)
         ⊢ wsat_auth 0 ∗ wsats 0.
  Proof.
    iIntros "H". iFrame. unfold wsats. ss.
  Qed.

  Lemma wsat_auth_nin (x n : index) (NIN : x < n)
    : OwnDs_auth x ∗ wsat_auth x
                 ⊢ OwnDs_auth n ∗ wsat_auth n ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m).
  Proof.
    induction NIN.
    - iIntros "[DA AUTH]". rename x into n. remember (S n) as x.
      assert ((wsat_auth_black n) =
                ((wsat_auth_black x)
                   ⋅
                   (maps_to_res_dep n (@Auth.black (positive ==> URA.agree (Vars n))%ra (fun (i : positive) => None))))).
      { subst. extensionalities a. unfold wsat_auth_black, maps_to_res_dep.
        unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = n)).
        - subst a. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec a (S n)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      assert ((OwnDs_auth_black n) =
                ((OwnDs_auth_black x)
                   ⋅
                   (maps_to_res n (Auth.black (Some ∅ : Gset.t))))).
      { subst. extensionalities a. unfold OwnDs_auth_black, maps_to_res.
        unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = n)).
        - subst a. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec a (S n)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      unfold wsat_auth. rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      unfold OwnDs_auth. rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW"; iFrame.
      subst x. iFrame.
      replace (S n - n) with 1 by lia. ss. iFrame.
    - iIntros "[DA AUTH]". iPoseProof (IHNIN with "[DA AUTH]") as "[DA [AUTH SAT]]"; iFrame.
      clear IHNIN. remember (S m) as y.
      assert ((wsat_auth_black m) =
                ((wsat_auth_black y)
                   ⋅
                   (maps_to_res_dep m (@Auth.black (positive ==> URA.agree (Vars m))%ra (fun (i : positive) => None))))).
      { subst. extensionalities a. unfold wsat_auth_black, maps_to_res_dep.
        unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = m)).
        - subst a. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec a (S m)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      assert ((OwnDs_auth_black m) =
                ((OwnDs_auth_black y)
                   ⋅
                   (maps_to_res m (Auth.black (Some ∅ : Gset.t))))).
      { subst. extensionalities a. unfold OwnDs_auth_black, maps_to_res.
        unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = m)).
        - subst a. des_ifs; try lia.
          unfold eq_rect_r. ss. rewrite URA.unit_idl. reflexivity.
        - destruct (le_dec a (S m)).
          { des_ifs; try lia.
            - rewrite URA.unit_idl. reflexivity.
            - rewrite URA.unit_id. reflexivity.
          }
          { des_ifs; try lia.
            rewrite URA.unit_id. reflexivity.
          }
      }
      unfold wsat_auth. rewrite H3. iDestruct "AUTH" as "[AUTH NEW]".
      unfold OwnDs_auth. rewrite H4. iDestruct "DA" as "[DA NEWD]".
      iPoseProof (wsat_init with "[NEWD NEW]") as "NEW"; iFrame.
      subst y. iFrame.
      replace (S m - x) with ((m - x) + 1) by lia. rewrite seq_app.
      iApply big_sepL_app. iFrame.
      replace (x + (m - x)) with m by lia. ss. iFrame.
  Qed.

  Lemma wsats_nin (x n : index) (NIN : x < n)
    : wsats x ∗ ([∗ list] m ∈ (seq x (n - x)), wsat m) ⊢ wsats n.
  Proof.
    iIntros "[SALL WSAT]". unfold wsats.
    replace n with (x + (n - x)) by lia. rewrite seq_app; iFrame.
    replace (x + (n - x) - x) with (n - x) by lia. iFrame.
  Qed.

  Lemma wsats_in (x0 x1 : index) :
    x0 < x1 -> wsats x1 ⊢ wsats x0 ∗ ([∗ list] n ∈ (seq x0 (x1 - x0)), wsat n).
  Proof.
    iIntros (LT) "SAT". unfold wsats.
    replace x1 with (x0 + (x1 - x0)) by lia. rewrite (seq_app _ _ 0).
    iPoseProof (big_sepL_app with "SAT") as "[SAT K]". iFrame.
    ss. replace (x0 + (x1 - x0) - x0) with (x1 - x0) by lia. iFrame.
  Qed.

  Lemma wsats_allocs x1 x2 :
    x1 < x2 ->
    OwnDs_auth x1 ∗ wsat_auth x1 ∗ wsats x1 ⊢ (OwnDs_auth x2 ∗ wsat_auth x2 ∗ wsats x2).
  Proof.
    iIntros (LT) "(DA & AUTH & SAT)".
    iPoseProof ((wsat_auth_nin _ _ LT) with "[DA AUTH]") as "(DA & AUTH & NEW)"; iFrame.
    iPoseProof ((wsats_nin _ _ LT) with "[SAT NEW]") as "SAT"; iFrame.
  Qed.


  Lemma wsats_OwnI_alloc_lt_gen x n (LT : n < x) p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats x ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ (prop n p -∗ wsats x).
  Proof.
    iIntros "SALL".
    iPoseProof (big_sepL_lookup_acc with "SALL") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iPoseProof (wsat_OwnI_alloc_gen with "WSAT") as ">[RES WSAT]".
    { apply INF. }
    iFrame. iModIntro. iIntros "P". iFrame. iPoseProof ("WSAT" with "P") as "WSAT".
    iPoseProof ("K" with "WSAT") as "SALL". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_lt x n (LT : n < x) p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : wsats x ∗ prop n p ⊢ |==> (∃ i, ⌜φ i⌝ ∧ OwnI n i p) ∗ wsats x.
  Proof.
    iIntros "[W P]". iMod (wsats_OwnI_alloc_lt_gen with "W") as "[I W]". 1,2: eauto.
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge_gen x n (GE : x <= n) p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnDs_auth x ∗ wsat_auth x ∗ wsats x ⊢
                 |==> ((∃ i, ⌜φ i⌝ ∧ OwnI n i p)
                         ∗ OwnDs_auth (S n) ∗ wsat_auth (S n) ∗ (prop n p -∗ wsats (S n))).
  Proof.
    iIntros "(DA & AUTH & WSAT)".
    iPoseProof ((wsats_allocs x (S n)) with "[DA AUTH WSAT]") as "[DA [AUTH WSAT]]".
    { lia. }
    { iFrame. }
    iMod ((wsats_OwnI_alloc_lt_gen (S n) n) with "WSAT") as "[RES WSAT]"; eauto.
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_alloc_ge x n (GE : x <= n) p φ
        (INF : forall (E : index -> option (gset positive)) n,
            match E n with
            | None => True
            | Some G => (exists i, i ∉ G /\ φ i)
            end)
    : OwnDs_auth x ∗ wsat_auth x ∗ wsats x ∗ prop n p
                 ⊢ |==> ((∃ i, ⌜φ i⌝ ∧ OwnI n i p)
                           ∗ OwnDs_auth (S n) ∗ wsat_auth (S n) ∗ wsats (S n)).
  Proof.
    iIntros "(D & A & W & P)". iMod (wsats_OwnI_alloc_ge_gen with "[D A W]") as "(I & D & A & W)".
    1,2: eauto.
    { iFrame. }
    iModIntro. iFrame. iApply "W". iFrame.
  Qed.

  Lemma wsat_auth_OwnI_le x n i p :
    OwnI n i p ∗ wsat_auth x ⊢ ⌜n < x⌝.
  Proof.
    iIntros "(I & AUTH)".
    unfold OwnI, wsat_auth.
    iCombine "AUTH I" as "AUTH".
    iPoseProof (OwnM_valid with "AUTH") as "%WF".
    unfold wsat_auth_black, OwnI_white, maps_to_res_dep in WF.
    unfold URA.add in WF. unseal "ra". ss.
    apply (pwd_lookup_wf _ n) in WF. ss. des_ifs.
    exfalso. unfold eq_rect_r in WF. rewrite <- Eqdep.EqdepTheory.eq_rect_eq in WF.
    unfold maps_to_res in WF. apply Auth.auth_included in WF. rename WF into EXTENDS.
    apply pw_extends in EXTENDS. specialize (EXTENDS i). des_ifs.
    clear e e0. rr in EXTENDS. des. unfold URA.add in EXTENDS; unseal "ra".
    ss. des_ifs.
  Qed.

  Lemma wsats_OwnI_open x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ OwnE n {[i]} ⊢ |==> prop n p ∗ wsats x ∗ OwnD n {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & EN)".
    unfold OwnI, wsats.
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    ss. iMod (wsat_OwnI_open with "[I WSAT EN]") as "[P [WSAT DN]]". { iFrame. }
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

  Lemma wsats_OwnI_close x n i p :
    n < x -> OwnI n i p ∗ wsats x ∗ prop n p ∗ OwnD n {[i]} ⊢ |==> wsats x ∗ OwnE n {[i]}.
  Proof.
    iIntros (LT) "(I & SAT & P & DIS)".
    iPoseProof (big_sepL_lookup_acc with "SAT") as "[WSAT K]".
    { apply lookup_seq_lt; eauto. }
    iMod (wsat_OwnI_close with "[I WSAT P DIS]") as "[WSAT EN]". { iFrame. }
    iPoseProof ("K" with "WSAT") as "SAT".
    iModIntro. iFrame.
  Qed.

End WSATS.

Notation coPsets := (gmap index coPset).

Section OWNES.

  Context `{Σ : GRA.t}.
  Context `{@GRA.inG OwnEsRA Σ}.

  Definition OwnE_auth_black (Es : coPsets) : (index ==> CoPset.t)%ra :=
    fun n => match Es !! n with
          | Some _ => ε
          | None => (Some ⊤)
          end.

  Definition OwnE_auth (Es : coPsets) := OwnM (OwnE_auth_black Es).

  Definition OwnE_satall (Es : coPsets) := ([∗ map] n ↦ E ∈ Es, OwnE n E)%I.

  Definition OwnEs (Es : coPsets) := (OwnE_auth Es ∗ OwnE_satall Es)%I.

  Definition OwnEs_top (Es : coPsets) : Prop := map_Forall (fun _ E => ⊤ ⊆ E) Es.
  (* Definition OwnEs_top (Es : coPsets) : Prop := map_Forall (fun _ E => E = ⊤) Es. *)

  Lemma OwnEs_init_wf :
    URA.wf (OwnE_auth_black ∅).
  Proof.
    ur. i. ur. des_ifs.
  Qed.

  Lemma OwnEs_init :
    OwnM (OwnE_auth_black ∅) ⊢ OwnEs ∅.
  Proof.
    iIntros. unfold OwnEs. iFrame. unfold OwnE_satall. ss.
  Qed.

  Lemma OwnEs_has Es n E :
    (Es !! n = Some E) -> OwnEs Es ⊢ OwnEs (<[n:=E]>Es).
  Proof.
    iIntros (IN) "ES". rewrite insert_id; auto.
  Qed.

  Lemma OwnEs_alloc Es n (NIN : Es !! n = None) :
    OwnEs Es ⊢ |==> OwnEs (<[n := ⊤]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnE_auth, OwnE_satall.
    remember (<[n := ⊤]> Es) as Es'.
    assert (URA.updatable
              (OwnE_auth_black Es)
              ((OwnE_auth_black Es')
                 ⋅
                 (maps_to_res n (Some ⊤)))).
    { apply pointwise_updatable. i.
      unfold OwnE_auth_black, maps_to_res. unfold URA.add. unseal "ra". ss. subst.
      destruct (excluded_middle_informative (a = n)).
      - subst a. des_ifs.
        2:{ exfalso. setoid_rewrite lookup_insert in Heq0. inv Heq0. }
        rewrite URA.unit_idl. reflexivity.
      - rewrite lookup_insert_ne; auto. rewrite URA.unit_id. reflexivity.
    }
    iMod (OwnM_Upd H0 with "AUTH") as "[AUTH NEW]". clear H0.
    iModIntro. iFrame. unfold OwnE_satall. subst. iApply big_sepM_insert; auto. iFrame.
  Qed.

  Lemma OwnEs_acc_in Es n E (IN : Es !! n = Some E) :
    OwnEs Es ⊢ OwnE n E ∗ OwnEs (<[n := ∅]>Es).
  Proof.
    iIntros "[AUTH SAT]". unfold OwnE_satall.
    iAssert (OwnE n E ∗ ([∗ map] n0↦E0 ∈ delete n Es, OwnE n0 E0))%I with "[SAT]" as "[EN SAT]".
    { iApply big_sepM_delete; auto. }
    iPoseProof (OwnM_persistently with "EN") as "#EN2". ss.
    iAssert ([∗ map] n0↦E0 ∈ <[n := ∅]>Es, OwnE n0 E0)%I with "[SAT]" as "SAT".
    { iApply big_sepM_insert_delete. iFrame. iApply (OwnM_extends with "EN2").
      unfold maps_to_res. clear. exists ε. rewrite URA.unit_id. extensionalities a. des_ifs.
    }
    iFrame. iClear "EN2".
    iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id. extensionalities a.
    unfold OwnE_auth_black. destruct (Nat.eqb_spec a n).
    - subst. rewrite lookup_insert. rewrite IN. auto.
    - rewrite lookup_insert_ne; auto.
  Qed.

  Lemma OwnEs_acc_new Es n (NIN : Es !! n = None) :
    OwnEs Es ⊢ |==> OwnE n ⊤ ∗ OwnEs (<[n := ∅]>Es).
  Proof.
    iIntros "ENS". iMod (OwnEs_alloc with "ENS") as "ENS"; eauto.
    iModIntro.
    assert (<[n:=∅]> Es = <[n:=∅]> (<[n:=⊤]> Es)).
    { rewrite insert_insert. auto. }
    rewrite H0. iApply OwnEs_acc_in.
    - rewrite lookup_insert. auto.
    - iFrame.
  Qed.

  Lemma OwnEs_union Es n E1 E2 :
    OwnEs (<[n:=E1]> Es) ∗ OwnE n E2 ⊢ OwnEs (<[n:=E1 ∪ E2]> Es).
  Proof.
    iIntros "[[AUTH SAT] EN]". unfold OwnEs. iSplitL "AUTH".
    { iApply (OwnM_extends with "AUTH"). exists ε. rewrite URA.unit_id. extensionalities a.
      unfold OwnE_auth_black. destruct (Nat.eqb_spec a n).
      - subst. rewrite ! lookup_insert. auto.
      - rewrite ! lookup_insert_ne; auto.
    }
    iApply big_sepM_insert_delete.
    iAssert (OwnE n E1 ∗ (OwnE_satall (delete n (<[n:=E1]> Es))))%I with "[SAT]" as "[EN' SAT]".
    { iApply big_sepM_delete.
      - apply lookup_insert.
      - iFrame.
    }
    assert ((delete n (<[n:=E1]> Es)) = delete n Es).
    { rewrite delete_insert_delete. auto. }
    rewrite H0. iFrame. iApply OwnE_union. iFrame.
  Qed.

  Lemma OwnEs_free Es n :
    Es !! n = None -> OwnEs (<[n:=⊤]>Es) ⊢ |==> OwnEs Es.
  Proof.
    iIntros (NIN) "ENS". iPoseProof (OwnEs_acc_in with "ENS") as "[EN ENS]".
    { apply lookup_insert. }
    rewrite insert_insert. unfold OwnEs. iDestruct "ENS" as "[AUTH SAT]".
    iSplitL "EN AUTH".
    - unfold OwnE_auth, OwnE. iCombine "EN AUTH" as "AUTH".
      assert (URA.updatable
                ((@maps_to_res index CoPset.t n (Some ⊤))
                   ⋅
                   OwnE_auth_black (<[n:=∅]> Es))
                (OwnE_auth_black Es)).
      { apply pointwise_updatable. i.
        unfold OwnE_auth_black, maps_to_res. unfold URA.add. unseal "ra". ss.
        destruct (excluded_middle_informative (a = n)).
        - subst a. rewrite lookup_insert. rewrite NIN.
          rewrite URA.unit_id. reflexivity.
        - rewrite lookup_insert_ne; auto. rewrite URA.unit_idl. reflexivity.
      }
      iMod (OwnM_Upd H0 with "AUTH") as "AUTH". iModIntro. iFrame.
    - unfold OwnE_satall. iModIntro.
      iPoseProof (big_sepM_insert with "SAT") as "[_ SAT]"; auto.
  Qed.

  Lemma OwnEs_update_one Es n E1 E2 :
    OwnEs (<[n:=E1]>Es) ⊢ (OwnE n E1 -∗ OwnE n E2) -∗ OwnEs (<[n:=E2]>Es).
  Proof.
    iIntros "E IMPL". iPoseProof (OwnEs_acc_in with "E") as "[E K]".
    { apply lookup_insert. }
    iPoseProof ("IMPL" with "E") as "E".
    iEval (rewrite insert_insert) in "K".
    iPoseProof (OwnEs_union with "[E K]") as "E". { iFrame. }
    replace (∅ ∪ E2) with E2 by set_solver.
    iFrame.
  Qed.

  Lemma OwnEs_subset Es n E1 E2 :
    (E1 ⊆ E2) -> OwnEs (<[n:=E2]>Es) ⊢ OwnEs (<[n:=E1]>Es).
  Proof.
    iIntros (SUB) "ES". iApply (OwnEs_update_one with "ES").
    iIntros "E". iPoseProof (OwnE_subset with "E") as "[E1 _]"; eauto.
  Qed.

  Lemma OwnEs_disjoint Es n E1 E2 :
    E1 ## E2 -> OwnEs (<[n:=E1 ∪ E2]>Es) ⊢ OwnEs (<[n:=E1]>Es) ∗ OwnE n E2.
  Proof.
    iIntros (HE) "ENS". iPoseProof (OwnEs_acc_in with "ENS") as "[EN ENS]".
    { apply lookup_insert. }
    iPoseProof ((OwnE_disjoint _ _ _ HE) with "EN") as "[EN1 EN2]".
    iFrame. rewrite insert_insert.
    iApply (OwnEs_update_one with "ENS"). iIntros. iFrame.
  Qed.

  Lemma OwnEs_free_all Es :
    OwnEs_top Es -> OwnEs Es ⊢ |==> OwnEs ∅.
  Proof.
    pattern Es. revert Es. apply map_ind.
    { iIntros (TOP) "ES". ss. }
    iIntros (? ? ? NONE IND TOP) "ES".
    iMod (OwnEs_free with "[ES]") as "ES"; eauto.
    { eapply map_Forall_lookup_1 in TOP. 2: apply lookup_insert. iApply OwnEs_subset; eauto. }
    iApply IND. 2: iFrame.
    eapply map_Forall_insert_1_2; eauto.
  Qed.


  Definition lookup_def (Es : coPsets) (n : nat) : coPset := default ⊤ (Es !! n).

  Definition subseteq_def (Es : coPsets) (n : nat) (E : coPset) : Prop :=
    match Es !! n with | Some E' => E ⊆ E' | None => True end.

  Definition insert_def (Es : coPsets) (n : nat) : coPsets :=
    match Es !! n with | Some E => Es | None => <[n:=⊤]> Es end.

  Lemma OwnEs_lookup_def Es n :
    OwnEs Es ⊢ |==> OwnEs (<[n := lookup_def Es n]>Es).
  Proof.
    iIntros "ENS". unfold lookup_def, default. des_ifs; ss.
    - rewrite insert_id; auto.
    - iMod (OwnEs_alloc with "ENS") as "ENS"; eauto.
  Qed.

  Lemma lookup_subseteq_def Es n E :
    E ⊆ (lookup_def Es n) -> subseteq_def Es n E.
  Proof.
    unfold lookup_def,default, subseteq_def. i. des_ifs.
  Qed.

End OWNES.

Notation "M '!?' k" := (lookup_def M k) (at level 20).
Notation "E '⪿' '(' Es ',' n ')'" := (subseteq_def Es n E) (at level 70).

Section FANCY_UPDATE.

  Context `{Σ : GRA.t}.
  Context `{Vars : index -> Type}.
  Context `{Invs : @IInvSet Σ Vars}.
  Context `{@GRA.inG OwnEsRA Σ}.
  Context `{@GRA.inG OwnDsRA Σ}.
  Context `{@GRA.inG (IInvSetRA Vars) Σ}.

  Definition inv (n : index) (N : namespace) p :=
    (∃ i, ⌜i ∈ (↑N : coPset)⌝ ∧ OwnI n i p)%I.

  Definition FUpd x (A : iProp) (Es1 Es2 : coPsets) (P : iProp) : iProp :=
    A ∗ wsats x ∗ OwnEs Es1 -∗ #=> (A ∗ wsats x ∗ OwnEs Es2 ∗ P).


  Lemma FUpd_mono x0 x1 A Es1 Es2 P :
    (x0 < x1) -> FUpd x0 A Es1 Es2 P ⊢ FUpd x1 A Es1 Es2 P.
  Proof.
    iIntros (LT) "FUPD (A & SAT & EN)".
    iPoseProof ((wsats_in _ _ LT) with "SAT") as "[SAT K]".
    iMod ("FUPD" with "[A SAT EN]") as "(A & SAT & EN & P)". { iFrame. }
    iModIntro. iFrame. iApply wsats_nin; [apply LT | iFrame].
  Qed.

  Lemma wsats_inv_gen x A Es n N p :
    n < x ->
    ⊢ A ∗ wsats x ∗ OwnEs Es -∗ #=> (A ∗ (prop n p -∗ wsats x) ∗ OwnEs Es ∗ (inv n N p)).
  Proof.
    iIntros (LT) "(A & WSAT & EN)".
    iMod (wsats_OwnI_alloc_lt_gen _ _ LT p (fun i => i ∈ ↑N) with "WSAT") as "[I WSAT]".
    - i. des_ifs. apply iris.base_logic.lib.invariants.fresh_inv_name.
    - iFrame. auto.
  Qed.

  Lemma FUpd_alloc_gen x A Es n N p :
    n < x -> (inv n N p -∗ prop n p) ⊢ FUpd x A Es Es (inv n N p).
  Proof.
    iIntros (LT) "P (A & WSAT & EN)".
    iMod (wsats_inv_gen with "[A WSAT EN]") as "(A & W & EN & #INV)". { eauto. }
    { iSplitL "A".  { iApply "A". }  iFrame. }
    iPoseProof ("P" with "INV") as "P". iPoseProof ("W" with "P") as "W". iModIntro. iFrame. auto.
  Qed.

  Lemma FUpd_alloc x A Es n N p :
    n < x -> prop n p ⊢ FUpd x A Es Es (inv n N p).
  Proof.
    iIntros (LT) "P". iApply FUpd_alloc_gen; eauto.
  Qed.

  Lemma FUpd_open_aux x A Es n N E (LT : n < x) (INE : Es !! n = Some E) (IN : ↑N ⊆ E) p :
    inv n N p ⊢
        FUpd x A Es (<[n := E∖↑N]> Es)
        ((prop n p) ∗ ((prop n p) -∗ FUpd x A (<[n := E∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & ENS)".
    iPoseProof ((OwnEs_acc_in _ _ _ INE) with "ENS") as "[EN ENS]".
    iAssert (OwnE n (E ∖ ↑N) ∗ OwnE n (↑N ∖ {[i]}) ∗ OwnE n {[i]})%I with "[EN]" as "(EN1 & EN2 & EN3)".
    { iApply bi.sep_mono_r.
      { apply OwnE_disjoint. set_solver. }
      iApply OwnE_disjoint.
      { set_solver. }
      replace (E ∖ ↑N ∪ (↑N ∖ {[i]} ∪ {[i]})) with E.
      - iFrame.
      - transitivity ({[i]} ∪ ↑N ∖ {[i]} ∪ E ∖ ↑N).
        + rewrite <- union_difference_singleton_L; ss. eapply union_difference_L; ss.
        + rewrite union_comm_L. f_equal. rewrite union_comm_L. ss.
    }
    iMod (wsats_OwnI_open x n i p LT with "[HI WSAT EN3]") as "(P & WSAT & DIS)".
    { iFrame. auto. }
    iModIntro. iFrame. iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". { iFrame. }
    replace (∅ ∪ E ∖ ↑N) with (E ∖ ↑N). 2: set_solver.
    iFrame. iIntros "P (A & WSAT & EN1)".
    iMod (wsats_OwnI_close x n i p LT with "[HI WSAT P DIS]") as "(WSAT & EN3)".
    { iFrame. auto. }
    iModIntro. iFrame. iSplit; auto.
    iPoseProof (OwnE_union with "[EN2 EN3]") as "EN2". { iFrame. }
    rewrite <- union_difference_singleton_L; ss.
    iPoseProof (OwnEs_union with "[EN1 EN2]") as "ENS". { iFrame. }
    rewrite insert_id. { iFrame. } rewrite INE. f_equal.
    rewrite difference_union_L. set_solver.
  Qed.

  Lemma FUpd_open x A Es n N (LT : n < x) (IN : (↑N) ⪿ (Es, n)) p :
    inv n N p ⊢
        FUpd x A Es
        (<[n := (Es !? n)∖↑N]> Es)
        ((prop n p) ∗ ((prop n p) -∗ FUpd x A (<[n := (Es !? n)∖↑N]> Es) Es emp)).
  Proof.
    iIntros "[% (%iN & #HI)] (A & WSAT & ENS)".
    unfold lookup_def, subseteq_def in *. destruct (Es !! n) eqn:CASES; ss.
    - iApply FUpd_open_aux; auto. { unfold inv; auto. } iFrame.
    - iAssert (
          (#=> (A ∗ (wsats x ∗ (OwnEs (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd x A (<[n:=⊤ ∖ ↑N]> Es) (<[n:=⊤]>Es) emp))))))
            -∗
            #=> (A ∗ (wsats x ∗ (OwnEs (<[n:=⊤ ∖ ↑N]> Es) ∗ (prop n p ∗ (prop n p -∗ FUpd x A (<[n:=⊤ ∖ ↑N]> Es) Es emp))))))%I as "K".
      { iIntros ">[A [SAT [ENS [P K]]]]". iModIntro. iFrame. iIntros "P".
        iPoseProof ("K" with "P") as "K". iIntros "[A [SAT ENS]]".
        iPoseProof ("K" with "[A SAT ENS]") as ">[A [SAT [ENS _]]]". { iFrame. }
        iMod (OwnEs_free with "ENS") as "ENS"; eauto.
        iModIntro. iFrame.
      }
      iApply "K". iClear "K".
      iMod (OwnEs_alloc _ _ CASES with "ENS") as "ENS". remember (<[n:=⊤]> Es) as Es'.
      replace (<[n:=⊤ ∖ ↑N]> Es) with (<[n:=⊤ ∖ ↑N]> Es').
      2:{ subst. rewrite insert_insert. auto. }
      iApply FUpd_open_aux; auto.
      { subst. apply lookup_insert. }
      { unfold inv; auto. }
      { iFrame. }
  Qed.

  Lemma FUpd_intro x A Es P :
    #=> P ⊢ FUpd x A Es Es P.
  Proof.
    iIntros "P H". iMod "P". iModIntro. iFrame. iFrame.
  Qed.

  Lemma FUpd_mask_frame_gen x A Es1 Es2 n E P :
    (Es1 !? n) ## E ->
    FUpd x A Es1 Es2 P ⊢
         FUpd x A (<[n := (Es1 !? n) ∪ E]>Es1) (<[n := (Es2 !? n) ∪ E]>Es2) P.
  Proof.
    rewrite /FUpd. iIntros (D) "H (A & WSAT & ENS)".
    iPoseProof ((OwnEs_acc_in _ n) with "ENS") as "[EN ENS]". { apply lookup_insert. }
    iPoseProof (OwnE_disjoint _ _ _ D with "EN") as "[EN1 EN]".
    iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". { iFrame. }
    replace (∅ ∪ lookup_def Es1 n) with (lookup_def Es1 n) by set_solver.
    destruct (coPset_equiv_dec E ∅); cycle 1.
    { unfold lookup_def, default in D. des_ifs; ss.
      2:{ exfalso. set_solver. }
      rewrite insert_insert. rewrite (insert_id Es1).
      2:{ unfold lookup_def, default. rewrite Heq. ss. }
      iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". { iFrame. }
      destruct (Es2 !! n) eqn:CASES.
      2:{ iMod ((OwnEs_acc_new _ _ CASES) with "ENS2") as "[EN2 _]".
          iPoseProof (OwnE_exploit with "[EN EN2]") as "%DIS". { iFrame. }
          set_solver.
      }
      unfold lookup_def. rewrite CASES. ss.
      iPoseProof ((OwnEs_acc_in _ _ _ CASES) with "ENS2") as "[EN2 ENS]".
      iPoseProof (OwnE_union with "[EN EN2]") as "EN". { iFrame. }
      iPoseProof (OwnEs_union with "[ENS EN]") as "ENS". { iFrame. }
      replace (∅ ∪ (c0 ∪ E)) with (c0 ∪ E) by set_solver.
      iModIntro. iFrame.
    }
    { replace (lookup_def Es1 n ∪ E) with (lookup_def Es1 n) by set_solver.
      replace (lookup_def Es2 n ∪ E) with (lookup_def Es2 n) by set_solver.
      rewrite insert_insert.
      destruct (Es1 !! n) eqn:CASES.
      - rewrite (insert_id Es1).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". { iFrame. }
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
      - replace (lookup_def Es1 n) with (⊤ : coPset).
        2:{ unfold lookup_def, default. rewrite CASES. ss. }
        iMod ((OwnEs_free _ _ CASES) with "ENS") as "ENS".
        iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS2 & P)". { iFrame. }
        iMod (OwnEs_lookup_def with "ENS2") as "ENS2". iModIntro. iFrame.
    }
  Qed.

  Lemma FUpd_mask_frame x A Es1 Es2 n E1 E2 E P :
    E1 ## E ->
    FUpd x A (<[n:=E1]>Es1) (<[n:=E2]>Es2) P ⊢
         FUpd x A (<[n :=E1 ∪ E]>Es1) (<[n :=E2 ∪ E]>Es2) P.
  Proof.
    iIntros (D) "FUPD".
    iPoseProof (FUpd_mask_frame_gen with "FUPD") as "FUPD".
    { unfold lookup_def. rewrite lookup_insert. ss. eauto. }
    unfold lookup_def. rewrite ! lookup_insert. ss. rewrite ! insert_insert. auto.
  Qed.

  Lemma FUpd_intro_mask x A Es1 Es2 Es3 n E1 E2 P :
    E2 ⊆ E1 ->
    FUpd x A (<[n:=E1]>Es1) (<[n:=E1]>Es2) P ⊢
         FUpd x A (<[n:=E1]>Es1) (<[n:=E2]>Es2) (FUpd x A (<[n:=E2]>Es3) (<[n:=E1]>Es3) P).
  Proof.
    rewrite /FUpd. iIntros (HE) "H (A & WSAT & ENS)".
    iPoseProof ("H" with "[A WSAT ENS]") as ">(A & WSAT & ENS & P)". { iFrame. }
    iModIntro.
    rewrite (union_difference_L _ _ HE).
    iPoseProof (OwnEs_disjoint with "ENS") as "[ENS EN]".
    { set_solver. }
    iFrame. iIntros "(A & WSAT & ENS)". iModIntro. iFrame.
    iApply OwnEs_union. iFrame.
  Qed.

  Lemma FUpd_mask_mono x A Es1 Es2 n E1 E2 P :
    E1 ⊆ E2 ->
    FUpd x A (<[n:=E1]>Es1) (<[n:=E1]>Es2) P ⊢ FUpd x A (<[n:=E2]>Es1) (<[n:=E2]>Es2) P.
  Proof.
    i. replace E2 with (E1 ∪ E2 ∖ E1).
    - eapply FUpd_mask_frame. set_solver.
    - symmetry. eapply leibniz_equiv. eapply union_difference. ss.
  Qed.

  Global Instance from_modal_FUpd x A Es P :
    FromModal True modality_id (FUpd x A Es Es P) (FUpd x A Es Es P) P.
  Proof.
    rewrite /FromModal /= /FUpd. iIntros. iModIntro. iFrame. iFrame.
  Qed.

  Global Instance from_modal_FUpd_alloc x A Es n P :
    FromModal (Es !! n = None) modality_id P (FUpd x A Es (<[n:=⊤]>Es) P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)".
    iMod (OwnEs_alloc with "EN") as "EN"; eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_free x A Es n P :
    FromModal (Es !! n = None) modality_id P (FUpd x A (<[n:=⊤]>Es) Es P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)".
    iMod (OwnEs_free with "EN") as "EN"; eauto. iModIntro. iFrame.
  Qed.

  Global Instance from_modal_FUpd_general x A Es n E1 E2 P :
    FromModal (E2 ⊆ E1) modality_id P (FUpd x A (<[n:=E1]>Es) (<[n:=E2]>Es) P) P.
  Proof.
    rewrite /FromModal /FUpd. ss.
    iIntros (HE) "P (A & WSAT & EN)". iModIntro. iFrame.
    iPoseProof (OwnEs_acc_in with "EN") as "[EN ENS]". { apply lookup_insert. }
    iPoseProof ((OwnE_subset _ _ _ HE) with "EN") as "[EN1 _]".
    iPoseProof (OwnEs_union with "[ENS EN1]") as "ENS". { iFrame. }
    rewrite insert_insert.
    replace (∅ ∪ E2) with E2 by set_solver. iFrame.
  Qed.

  Global Instance from_modal_FUpd_wrong_mask x A Es1 Es2 P :
    FromModal (pm_error "Only non-mask-changing update modalities can be introduced directly.
Use [FUpd_mask_frame] and [FUpd_intro_mask]")
              modality_id (FUpd x A Es1 Es2 P) (FUpd x A Es1 Es2 P) P | 100.
  Proof.
    intros [].
  Qed.

  Global Instance elim_modal_bupd_FUpd p x A Es1 Es2 P Q :
    ElimModal True p false (|==> P) P (FUpd x A Es1 Es2 Q) (FUpd x A Es1 Es2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] I". iMod "P". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd p n x A Es1 Es2 Es3 P Q :
    ElimModal (n <= x) p false (FUpd n A Es1 Es2 P) P (FUpd x A Es1 Es3 Q) (FUpd x A Es2 Es3 Q).
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim.
    iIntros (LT) "[P K] I". inv LT.
    - rewrite /FUpd.
      iMod ("P" with "I") as "(A & WSAT & EN & P)". iApply ("K" with "P"). iFrame.
    - iPoseProof (FUpd_mono n (S m) with "P") as "P". { lia. }
      rewrite /FUpd.
      iMod ("P" with "I") as "(A & WSAT & EN & P)". iApply ("K" with "P"). iFrame.
  Qed.

  Global Instance elim_modal_FUpd_FUpd_general p x A Es0 Es1 Es2 n E0 E1 E2 E3 P Q :
    ElimModal (E0 ⊆ E2) p false
              (FUpd x A (<[n:=E0]>Es0) (<[n:=E1]>Es1) P)
              P
              (FUpd x A (<[n:=E2]>Es0) (<[n:=E3]>Es2) Q)
              (FUpd x A (<[n:=(E1 ∪ (E2 ∖ E0))]>Es1) (<[n:=E3]>Es2) Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim. ss.
    iIntros (HE) "[M K]".
    iPoseProof (FUpd_mask_frame _ _ _ _ _ _ _ (E2 ∖ E0) with "M") as "M".
    { set_solver. }
    replace (E0 ∪ E2 ∖ E0) with E2 by (eapply union_difference_L; ss).
    iMod "M". iPoseProof ("K" with "M") as "M". iFrame.
  Qed.

  Global Instance elim_acc_FUpd
         {X : Type} i A Es1 Es2 Es (α β : X -> iProp) (mγ : X -> option iProp) (Q : iProp) :
    ElimAcc True (FUpd i A Es1 Es2) (FUpd i A Es2 Es1) α β mγ (FUpd i A Es1 Es Q) (fun x : X => ((FUpd i A Es2 Es2 (β x)) ∗ (mγ x -∗? FUpd i A Es1 Es Q))%I).
  Proof.
    iIntros (_) "Hinner >[% [Hα Hclose]]".
    iPoseProof ("Hinner" with "Hα") as "[>Hβ Hfin]".
    iPoseProof ("Hclose" with "Hβ") as ">Hγ".
    iApply "Hfin". iFrame.
  Qed.

  Global Instance into_acc_FUpd_inv x A Es n N p :
    IntoAcc (inv n N p) (n < x /\ (↑N) ⪿ (Es, n)) True
            (FUpd x A Es (<[n := Es !? n ∖ ↑N]>Es))
            (FUpd x A (<[n := Es !? n ∖ ↑N]>Es) Es)
            (fun _ : () => prop n p) (fun _ : () => prop n p) (fun _ : () => None).
  Proof.
    rewrite /IntoAcc. iIntros ((LT & iE)) "INV _". rewrite /accessor.
    iPoseProof (FUpd_open _ _ _ _ _ LT iE with "INV") as ">[open close]".
    iModIntro. iExists tt. iFrame.
  Qed.

  Global Instance elim_modal_iupd_FUpd p x A Es1 Es2 P Q :
    ElimModal True p false (#=(A)=> P) P (FUpd x A Es1 Es2 Q) (FUpd x A Es1 Es2 Q) | 10.
  Proof.
    rewrite /ElimModal bi.intuitionistically_if_elim /FUpd.
    iIntros (_) "[P K] [A I]".
    iMod ("P" with "A") as "[A P]". iApply ("K" with "P"). iFrame.
  Qed.

End FANCY_UPDATE.

Global Opaque FUpd.
