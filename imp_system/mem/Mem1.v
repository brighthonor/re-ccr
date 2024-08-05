Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import Mod HMod SMod Events.
Require Import Skeleton.
Require Import PCM.
Require Import STB.
Require Import IPM.


Set Implicit Arguments.



Let _memRA: URA.t := (mblock ==> Z ==> (Excl.t val))%ra.
Compute (URA.car (t:=_memRA)).
Instance memRA: URA.t := Auth.t _memRA.
Compute (URA.car).

Local Arguments Z.of_nat: simpl nomatch.


Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition _points_to_singleton_r (loc: mblock * Z) (v: val): _memRA := 
    fun b ofs => if (dec loc.1 b) && (dec loc.2 ofs) then Some v else ε.

  Definition points_to_singleton_r (loc: mblock * Z) (v: val): memRA := Auth.white (_points_to_singleton_r loc v).

  Definition points_to_singleton (loc: mblock * Z) (v: val): iProp := OwnM (points_to_singleton_r loc v).

  Definition points_to: (mblock * Z) -> list val -> iProp :=
    fun '(blk, ofs) vs => ([∗ list] i↦v ∈ vs, points_to_singleton (blk, ofs + i)%Z v)%I.

  (* Definition points_to (loc: mblock * Z) (vs: list val): iProp := [∗ list] i↦v ∈ vs, points_to_singleton (loc.1, loc.2 + i)%Z v. *)

  Lemma points_to_split
        blk ofs hd tl
    :
        points_to (blk, ofs) (hd::tl) = (points_to_singleton (blk, ofs) hd ∗ points_to (blk, (ofs + 1)%Z) tl)%I.
  Proof.
    unfold points_to. ss.
    replace (ofs + 0)%Z with ofs; [|nia]. do 2 f_equal.
    extensionalities. do 2 f_equal. nia.
  Qed. 

  Definition _initial_mem_r (csl: gname -> bool) (sk: Sk.t): _memRA :=
    fun blk ofs =>
      match List.nth_error sk blk with
      | Some (g, gd) =>
        match gd↓ with
        | Some Gfun => ε
        | Some (Gvar gv) => if csl g then if (dec ofs 0%Z) then Some (Vint gv) else ε else ε
        | _ => ε
        end
      | _ => ε
      end.

  Definition initial_mem_r (csl: gname -> bool) (sk: Sk.t): memRA :=
    Auth.black (_initial_mem_r csl sk).
 
  Definition initial_mem (csl: gname -> bool) (sk: Sk.t): iProp :=
    OwnM (initial_mem_r csl sk).


(* Lemma points_tos_points_to *)
(*       loc v *)
(*   : *)
(*     (points_to loc v) = (points_tos loc [v]) *)
(* . *)
(* Proof. *)
(*   apply func_ext. i. *)
(*   apply prop_ext. *)
(*   ss. split; i; r. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*   - des_ifs. ss. eapply Own_extends; et. rp; try refl. repeat f_equal. repeat (apply func_ext; i). *)
(*     des_ifs; bsimpl; des; des_sumbool; ss; clarify. *)
(*     + rewrite Z.sub_diag; ss. *)
(*     + rewrite Z.ltb_lt in *. lia. *)
(*     + rewrite Z.leb_refl in *; ss. *)
(*     + rewrite Z.ltb_ge in *. lia. *)
(* Qed. *)

End PROOF.

Notation "loc ⤇ v" := (points_to_singleton loc v) (at level 20).
Notation "loc |-> vs" := (points_to loc vs) (at level 20).

Section AUX.
  Context `{@GRA.inG memRA Σ}.

  Lemma points_to_nil ptr: ptr |-> [] = emp%I.
  Proof. destruct ptr. ss. Qed.
  
  Lemma points_to_disj
        ptr x0 x1
    :
      ((ptr |-> [x0]) -∗ (ptr |-> [x1]) -* False)
  .
  Proof.
    destruct ptr as [blk ofs].
    iIntros "[A _] [B _]". s. iCombine "A B" as "A". iOwnWf "A" as WF0.
    unfold points_to_singleton_r in WF0. unfold _points_to_singleton_r in WF0. repeat (ur in WF0); ss.
    specialize (WF0 blk ofs). des_ifs; bsimpl; des; des_sumbool; zsimpl; ss; try lia.
  Qed.

  Fixpoint is_list (ll: val) (xs: list val): iProp :=
    match xs with
    | [] => (⌜ll = Vnullptr⌝: iProp)%I
    | xhd :: xtl =>
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                             ∗ is_list ltl xtl: iProp)%I
    end
  .

  Lemma unfold_is_list: forall ll xs,
      is_list ll xs =
      match xs with
      | [] => (⌜ll = Vnullptr⌝: iProp)%I
      | xhd :: xtl =>
        (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                               ∗ is_list ltl xtl: iProp)%I
      end
  .
  Proof.
    i. destruct xs; auto.
  Qed.

  Lemma unfold_is_list_cons: forall ll xhd xtl,
      is_list ll (xhd :: xtl) =
      (∃ lhd ltl, ⌜ll = Vptr lhd 0⌝ ∗ ((lhd,0%Z) |-> [xhd; ltl])
                             ∗ is_list ltl xtl: iProp)%I.
  Proof.
    i. eapply unfold_is_list.
  Qed.

  Lemma is_list_wf
        ll xs
    :
      (is_list ll xs) -∗ (⌜(ll = Vnullptr) \/ (match ll with | Vptr _ 0 => True | _ => False end)⌝)
  .
  Proof.
    iIntros "H0". destruct xs; ss; et.
    { iPure "H0" as H0. iPureIntro. left. et. }
    iDestruct "H0" as (lhd ltl) "(H0 & H1 & H2)".
    iPure "H0" as H0. iPureIntro. right. subst. et.
  Qed.

  (* Global Opaque is_list. *)
End AUX.

(* Section POINTS_TO.
  Context `{@GRA.inG memRA Σ}.

  Definition PointsTo p v := p |-> [v].
  
  Lemma points_to_conv b ofs l:
    ((b,ofs) |-> l) -∗ [∗ list] i↦v ∈ l, PointsTo (b, ofs + i)%Z v.
  Proof.
    revert b ofs. induction l; eauto; i.
    rewrite points_to_split. s.
    iIntros "(H&T)". rewrite Z.add_0_r.
    iFrame. iPoseProof (IHl with "T") as "T". clear IHl.
    eapply eq_ind. { iApply "T". }
    f_equal. extensionalities i v. do 2 f_equal. nia.
  Qed.

  Lemma points_to_conv_r b ofs l:
    ([∗ list] i↦v ∈ l, PointsTo (b, ofs + i)%Z v) -∗ ((b,ofs) |-> l).
  Proof.
    revert b ofs. induction l; i.
    { s. rewrite points_to_nil. apply OwnM_unit. }
    rewrite points_to_split. s.
    iIntros "(H&T)". rewrite Z.add_0_r. 
    iFrame. iApply IHl. clear IHl.
    eapply eq_ind. { iApply "T". }
    f_equal. extensionalities x i. do 2 f_equal. nia.
  Qed.
  
End POINTS_TO. *)




Section PROOF.
  Context `{@GRA.inG memRA Σ}.

  Definition alloc_spec: fspec :=
    (mk_simple (fun sz => (
                    (ord_pure 0),
                    (fun varg => (⌜varg = [Vint (Z.of_nat sz)]↑ /\ (8 * (Z.of_nat sz) < modulus_64)%Z⌝: iProp)),
                    (fun vret => (∃ b, (⌜vret = (Vptr b 0)↑⌝)
                                         ∗ (b, 0%Z) |-> (List.repeat Vundef sz)): iProp)
    )))%I.

  Definition free_spec: fspec :=
    (mk_simple (fun '(b, ofs) => (
                    (ord_pure 0),
                    (fun varg => (∃ v, (⌜varg = [Vptr b ofs]↑⌝) ∗ (b, ofs) ⤇ v)),
                    (fun vret => ⌜vret = (Vint 0)↑⌝)
    )))%I.

  Definition load_spec: fspec :=
    (mk_simple (fun '(b, ofs, v) => (
                    (ord_pure 0),
                    (fun varg => (⌜varg = [Vptr b ofs]↑⌝) ∗ (b, ofs) ⤇ v),
                    (fun vret => (b, ofs) ⤇ v ∗ ⌜vret = v↑⌝)
    )))%I.

  Definition store_spec: fspec :=
    (mk_simple
       (fun '(b, ofs, v_new) => (
            (ord_pure 0),
            (fun varg => (∃ v_old, (⌜varg = [Vptr b ofs ; v_new]↑⌝) ∗ (b, ofs) ⤇ v_old)),
            (fun vret => (b, ofs) ⤇ v_new ∗ ⌜vret = (Vint 0)↑⌝)
    )))%I.

  (* Is this the best way to define cmp? (points_to is not resource anymore)*)
  Definition cmp_spec: fspec :=
    (mk_simple
       (fun '(result, resource) => (
            (ord_pure 0),
            (fun varg =>
               ((∃ b ofs v, ⌜varg = [Vptr b ofs; Vnullptr]↑⌝ ∗ (OwnM resource -* ((b, ofs) |-> [v])) ∗ ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vnullptr; Vptr b ofs]↑⌝ ∗(OwnM resource -* ((b, ofs) |-> [v])) ∗ ⌜result = false⌝) ∨
                (∃ b0 ofs0 v0 b1 ofs1 v1, ⌜varg = [Vptr b0 ofs0; Vptr b1 ofs1]↑⌝ ∗ (OwnM resource -* ((b0, ofs0) |-> [v0] ∗ (b1, ofs1) |-> [v1])) ∗ ⌜result = false⌝) ∨
                (∃ b ofs v, ⌜varg = [Vptr b ofs; Vptr b  ofs]↑⌝ ∗ (OwnM resource -* (b, ofs) |-> [v]) ∗ ⌜result = true⌝) ∨
                (⌜varg = [Vnullptr; Vnullptr]↑ /\ result = true⌝))
                 ∗ OwnM resource
            ),
            (fun vret => OwnM resource ∗ ⌜vret = (if result then Vint 1 else Vint 0)↑⌝)
    )))%I.

  Definition MemStb: list (gname * fspec).
    eapply (Seal.sealing "stb").
    apply [("alloc", alloc_spec) ; ("free", free_spec) ; ("load", load_spec) ; ("store", store_spec) ; ("cmp", cmp_spec)].
  Defined.

  Definition MemSbtb: list (gname * fspecbody) :=
    [("alloc", mk_specbody alloc_spec (fun _ => trigger (Choose _)));
    ("free",   mk_specbody free_spec (fun _ => trigger (Choose _)));
    ("load",   mk_specbody load_spec (fun _ => trigger (Choose _)));
    ("store",  mk_specbody store_spec (fun _ => trigger (Choose _)));
    ("cmp",    mk_specbody cmp_spec (fun _ => trigger (Choose _)))
    ]
  .

  Variable csl: gname -> bool.

  Definition SMemSem (sk: Sk.t): SModSem.t := {|
    SModSem.fnsems := MemSbtb;
    SModSem.initial_cond := initial_mem csl sk;
    SModSem.initial_st := tt↑;
  |}
  .

  Definition SMem: SMod.t := {|
    SMod.get_modsem := SMemSem;
    SMod.sk := Sk.unit;
  |}
  .

  Definition _HMem: HMod.t := (SMod.to_hmod (fun _ => to_stb [])) SMem.
  Definition HMem := _HMem.

  Lemma HMem_unfold: HMem = _HMem.
  Proof. eauto. Qed.
  
  Global Opaque HMem.
  
End PROOF.
Global Hint Unfold MemStb: stb.

Global Opaque _points_to_singleton_r.
