Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB.
From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.
Require Import ProofMode IProofMode.
Require Import Mem1.
Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.
Set Implicit Arguments.

Section RESOURCE.
  Context `{_W: CtxWD.t}.

  Global Instance MapRA: URA.t := URA.prod (Excl.t unit) (Auth.t (Z ==> (Excl.t Z)))%ra.
  Context `{@GRA.inG MapRA Γ}.

  Definition map_points_to_r (k: Z) (v: Z): MapRA :=
    (ε, Auth.white ((fun n => if Z.eq_dec n k then Excl.just v else ε): @URA.car (Z ==> (Excl.t Z))%ra)).

  Definition map_points_to (k: Z) (v: Z): iProp :=
    OwnM (map_points_to_r k v).

  (* Definition S_map_points_to {n} (k: Z) (v: Z): SRFSyn.t n :=
    (<ownm> (map_points_to_r k v))%SRF. *)

  Definition pending_r: MapRA :=
    (Excl.just tt, ε).

  Definition pending: iProp :=
    OwnM pending_r.
    
  (* Definition S_pending {n}: SRFSyn.t n :=
    (<ownm> pending_r)%SRF. *)


  (* Definition pending `{@GRA.inG MapRA0 Σ} `{@GRA.inG MapRA Σ}: iProp :=
      pending0 ∗ pending1. *)

  Fixpoint initial_points_tos (sz: nat): iProp :=
    match sz with
    | 0 => True%I
    | S sz' => initial_points_tos sz' ∗ map_points_to sz' 0
    end.

  Definition MapRA0: URA.t := Excl.t unit.
  Context `{@GRA.inG MapRA0 Γ}.

  Definition pending0_r: MapRA0 := Excl.just tt.

  Definition pending0: iProp :=
    OwnM pending0_r.

  
  Definition initial_r: (Z ==> (Excl.t Z))%ra := (fun _ => Excl.just 0%Z).
  
  Definition initial_map_r: MapRA :=
    (ε, (Auth.black initial_r) ⋅ (Auth.white initial_r)).

  Definition black_map_r (f: Z -> Z): MapRA :=
    (Excl.unit, Auth.black ((fun k => Excl.just (f k)): (Z ==> (Excl.t Z))%ra)).

  Definition unallocated_r (sz: Z): MapRA :=
    (Excl.unit, Auth.white ((fun k =>
                               if (Z_gt_le_dec 0 k) then Excl.just 0%Z
                               else if (Z_gt_le_dec sz k) then Excl.unit else Excl.just 0%Z)
                             : (Z ==> (Excl.t Z))%ra)).

  Definition initial_map: iProp :=
    OwnM initial_map_r.

  Definition black_map (f: Z -> Z): iProp :=
    OwnM (black_map_r f).

  Definition unallocated (sz: Z): iProp :=
    OwnM (unallocated_r sz).

  Global Opaque map_points_to pending pending0 initial_map black_map unallocated.

End RESOURCE.

Section SPECS.
  Context `{_W: CtxWD.t}.
  Context `{@GRA.inG MapRA Γ}.
  Context `{@GRA.inG MapRA0 Γ}.

  (* Definition PENDING := (nroot .@ "MAP" .@ "PENDING"). *)

  Definition init_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun (sz: nat) =>
                    (ord_top,
                      (fun varg => ( ⌜varg = ([Vint sz]: list val)↑⌝
                                     ∗ ⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝
                                     ∗ pending)%I),
                                     (* exists N, inv u n N S_pending *)
                                     (* inv u n PENDING S_pending *)
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ initial_points_tos sz)%I)))).

  Definition init_specM: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun (sz: nat) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint sz]: list val)↑⌝
                                     ∗ ⌜(8 * (Z.of_nat sz) < modulus_64%Z)%Z⌝
                                     ∗ pending0)%I),
                      (fun vret => True%I)))).

  Definition get_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, v) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k])↑⌝
                                     ∗ map_points_to k v)%I),
                      (fun vret => (⌜vret = (Vint v)↑⌝ ∗ map_points_to k v)%I)))).

  Definition get_specM: fspec := fspec_trivial.

  Definition set_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, w, v) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k; Vint v])↑⌝
                                     ∗ map_points_to k w)%I),
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ map_points_to k v)%I)))).

  Definition set_specM: fspec := fspec_trivial.

  Definition set_by_user_spec: fspec :=
    mk_fspec_inv 0
      (fun _ _ => mk_simple (fun '(k, w) =>
                    (ord_top,
                      (fun varg => (⌜varg = ([Vint k])↑⌝
                                     ∗ map_points_to k w)%I),
                      (fun vret => (⌜vret = Vundef↑⌝ ∗ ∃ v, map_points_to k v)%I)))).

  Definition set_by_user_specM: fspec := fspec_trivial.

  Definition Map_initial_cond : iProp := initial_map ∗ pending0.
  
  Definition Map0_initial_cond : iProp := emp.

  Definition MapStb: alist gname fspec :=
    Seal.sealing "stb" [("init", init_spec); ("get", get_spec); ("set", set_spec); ("set_by_user", set_by_user_spec)].

  Definition MapStbM: alist gname fspec :=
    Seal.sealing "stb" [("init", init_specM); ("get", get_specM); ("set", set_specM); ("set_by_user", set_by_user_specM)].
End SPECS.
Global Hint Unfold MapStb MapStbM: stb.



Definition set `{Dec K} V (k: K) (v: V) (f: K -> V): K -> V := fun k0 => if dec k k0 then v else f k0.



Section PROOF.
  Context `{Σ: GRA.t}.

  Lemma Own_unit
    :
      bi_entails True%I (Own ε)
  .
  Proof.
    red. uipropall. ii. rr. esplits; et. rewrite URA.unit_idl. refl.
  Qed.

  Context `{@GRA.inG M Σ}.

  Lemma embed_unit
    :
      (GRA.embed ε) = ε
  .
  Proof.
    unfold GRA.embed.
    Local Transparent GRA.to_URA. unfold GRA.to_URA. Local Opaque GRA.to_URA.
    Local Transparent URA.unit. unfold URA.unit. Local Opaque URA.unit.
    cbn.
    apply func_ext_dep. i.
    dependent destruction H. ss. rewrite inG_prf. cbn. des_ifs.
  Qed.

End PROOF.

Section PROOF.
  Context `{@GRA.inG M Σ}.

  Lemma OwnM_unit
    :
      bi_entails True%I (OwnM ε)
  .
  Proof.
    unfold OwnM. r. uipropall. ii. rr. esplits; et. rewrite embed_unit. rewrite URA.unit_idl. refl.
  Qed.
End PROOF.


Ltac get_fresh_string :=
  match goal with
  | |- context["A"] =>
    match goal with
    | |- context["A0"] =>
      match goal with
      | |- context["A1"] =>
        match goal with
        | |- context["A2"] =>
          match goal with
          | |- context["A3"] =>
            match goal with
            | |- context["A4"] =>
              match goal with
              | |- context["A5"] => fail 5
              | _ => constr:("A5")
              end
            | _ => constr:("A4")
            end
          | _ => constr:("A3")
          end
        | _ => constr:("A2")
        end
      | _ => constr:("A1")
      end
    | _ => constr:("A0")
    end
  | _ => constr:("A")
  end
.
Ltac iDes :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ _ (INamed ?namm) ?ip] =>
           match ip with
           | @bi_or _ _ _ =>
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ "|" +:+ namm +:+ "]")) in
             iDestruct namm as pat
           | @bi_pure _ _ => iDestruct namm as "%"
           | @iNW _ ?newnamm _ => iEval (unfold iNW) in namm; iRename namm into newnamm
           | @bi_sep _ _ _ =>
             let f := get_fresh_string in
             let pat := ltac:(eval vm_compute in ("[" +:+ namm +:+ " " +:+ f +:+ "]")) in
             iDestruct namm as pat
           | @bi_exist _ _ (fun x => _) =>
             let x := fresh x in
             iDestruct namm as (x) namm
           end
         end
.
Ltac iCombineAll :=
  repeat multimatch goal with
         | |- context[@environments.Esnoc _ (@environments.Esnoc _ _ (INamed ?nam1) _) (INamed ?nam2) _] =>
           iCombine nam1 nam2 as nam1
         end
.
Ltac xtra := iCombineAll; iAssumption.

(*** TODO: MOVE TO ImpPrelude ***)
Definition add_ofs (ptr: val) (d: Z): val :=
  match ptr with
  | Vptr b ofs => Vptr b (ofs + d)
  | _ => Vundef
  end
.

Lemma scale_int_8 n: scale_int (8 * n) = Some n.
Proof.
  unfold scale_int. des_ifs.
  - rewrite Z.mul_comm. rewrite Z.div_mul; ss.
  - contradict n0. eapply Z.divide_factor_l.
Qed.
Notation syscallU name vs := (z <- trigger (Syscall name vs↑ top1);; `z: Z <- z↓?;; Ret z).

Notation pget := (p0 <- trigger sGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
Notation pput p0 := (trigger (sPut p0↑)) (only parsing).


(* Notation pget := (p0 <- trigger PGet;; p0 <- p0↓ǃ;; Ret p0) (only parsing).
Notation pput p0 := (trigger (PPut p0↑)) (only parsing). *)

Fixpoint set_nth A (n:nat) (l:list A) (new:A) {struct l} : option (list A) :=
  match n, l with
  | O, x :: l' => Some (new :: l')
  | O, other => None
  | S m, [] => None
  | S m, x :: t => option_map (cons x) (set_nth m t new)
  end.
