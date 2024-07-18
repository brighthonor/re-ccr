 Require Import Coqlib AList.
Require Import STS.
Require Import Behavior.
Require Import ModSemFacts ModSem.
Require Import Skeleton.
Require Import PCM.
From Ordinal Require Export Ordinal Arithmetic Inaccessible.
Require Import Any.
Require Import IRed.

From ExtLib Require Import
     Core.RelDec
     Structures.Maps
     Data.Map.FMapAList.

Set Implicit Arguments.



(*** TODO: move to ITreelib, and replace raw definitions with this ***)
Definition trivial_Handler `{E -< F}: Handler E F := fun T X => trigger X.

Inductive ord: Type :=
| ord_pure (n: Ord.t)
| ord_top
.

Definition is_pure (o: ord): bool := match o with | ord_pure _ => true | _ => false end.

Definition ord_lt (next cur: ord): Prop :=
  match next, cur with
  | ord_pure next, ord_pure cur => (next < cur)%ord
  | _, ord_top => True
  | _, _ => False
  end
.

(**
(defface hi-light-green-b
  '((((min-colors 88)) (:weight bold :foreground "dark magenta"))
    (t (:weight bold :foreground "dark magenta")))
  "Face for hi-lock mode."
  :group 'hi-lock-faces)

 **)


Section PSEUDOTYPING.

(*** execute following commands in emacs (by C-x C-e)
     (progn (highlight-phrase "Any" 'hi-red-b) (highlight-phrase "Any_src" 'hi-green-b) (highlight-phrase "Any_tgt" 'hi-blue-b)
            (highlight-phrase "Any_mid" 'hi-light-green-b)
            (highlight-phrase "Y" 'hi-green-b) (highlight-phrase "Z" 'hi-green-b)) ***)
Let Any_src := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_mid := Any.t. (*** src argument (e.g., List nat) ***)
Let Any_tgt := Any.t. (*** tgt argument (i.e., list val) ***)

Require Import IPM.

Section FSPEC.
  Context `{Σ: GRA.t}.

  (*** spec table ***)
  Record fspec: Type := mk_fspec {
    meta: Type;
    measure: meta -> ord;
    precond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }
  .

  Definition mk (X AA AR: Type) (measure: X -> ord) (precond: X -> AA -> Any_tgt -> iProp) (postcond: X -> AR -> Any_tgt -> iProp) :=
    @mk_fspec
      X
      measure
      (fun x arg_src arg_tgt => (∃ (aa: AA), ⌜arg_src = aa↑⌝ ∧ precond x aa arg_tgt)%I)
      (fun x ret_src ret_tgt => (∃ (ar: AR), ⌜ret_src = ar↑⌝ ∧ postcond x ar ret_tgt)%I)
  .

  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I)
  .
End FSPEC.


Section PROOF.
  (* Context {myRA} `{@GRA.inG myRA Σ}. *)
  Context {Σ: GRA.t}.
  Let GURA: URA.t := GRA.to_URA Σ.
  Local Existing Instance GURA.


  Definition mput E `{sE -< E} `{eventE -< E} (mr: Σ): itree E unit :=
    st <- trigger sGet;; '(mp, _) <- ((Any.split st)?);;
    trigger (sPut (Any.pair mp mr↑))
  .

  Definition mget E `{sE -< E} `{eventE -< E}: itree E Σ :=
    st <- trigger sGet;; '(_, mr) <- ((Any.split st)?);;
    mr↓?
  .

  Definition pupdate E `{sE -< E} `{eventE -< E} {X} (run: Any.t -> Any.t * X) : itree E X :=
    trigger (SUpdate (fun st => 
      match (Any.split st) with
      | Some (x, mr) => ((Any.pair (fst (run x)) mr), snd (run x))
      | None => run tt↑
      end
    ))
  .

End PROOF.

Notation "'update_and_discard' fr0" :=
  ('(rarg, fr1, mr1) <- trigger (Choose (_ * _ * _));;
   mr0 <- mget;;
   guarantee(Own (fr0 ⋅ mr0) ⊢ #=> Own (rarg ⋅ fr1 ⋅ mr1));;;
   mput mr1;;;
   Ret (fr1, rarg)) (at level 60)
.  


(* Section PROOF.

  Context {Σ: GRA.t}.


  Definition HoareCall
             (tbr: bool)
             (ord_cur: ord)
             (fsp: fspec):
    gname -> Any.t -> stateT (Σ) (itree Es) Any.t :=
    fun fn varg_src fr0 =>

      '(fr1, rarg) <- update_and_discard fr0;;

      x <- trigger (Choose fsp.(meta));; 
      
      (* ASSERT *)
      varg_tgt <- trigger (Choose Any_tgt);;
      (*** precondition ***)
      guarantee(fsp.(precond) x varg_src varg_tgt rarg);;; 

      let ord_next := fsp.(measure) x in
      guarantee(ord_lt ord_next ord_cur /\ (tbr = true -> is_pure ord_next) /\ (tbr = false -> ord_next = ord_top));;;

      vret_tgt <- trigger (Call fn varg_tgt);; (*** call ***)

      (* ASSUME *)
      rret <- trigger (Take Σ);;
      mr2 <- mget;;
      assume (URA.wf (rret ⋅ fr1 ⋅ mr2));;;

      vret_src <- trigger (Take Any.t);;
      assume(fsp.(postcond) x vret_src vret_tgt rret);;; (*** postcondition ***)

      Ret (rret ⋅ fr1, vret_src)
  .  


End PROOF. *)















(*** TODO: Move to Coqlib. TODO: Somehow use case_ ??? ***)
(* Definition map_fst A0 A1 B (f: A0 -> A1): (A0 * B) -> (A1 * B) := fun '(a, b) => (f a, b). *)
(* Definition map_snd A B0 B1 (f: B0 -> B1): (A * B0) -> (A * B1) := fun '(a, b) => (a, f b). *)

Section CANCEL.

Context {Σ: GRA.t}.

Variant hAPCE: Type -> Type :=
| hAPC: hAPCE unit
.

Variant hCallE: Type -> Type :=
| hCall (tbr: bool) (fn: gname) (varg_src: Any_src): hCallE Any_src
(*** tbr == to be removed ***)
.

Variant hAGE: Type -> Type :=
| Assume (P: iProp): hAGE unit
| Guarantee (P: iProp): hAGE unit
.


Definition hEs := (hAGE +' hAPCE +' Es).
Definition hAGEs := (hAGE +' Es).

Definition ord_eval (tbr: bool) (o: ord): Prop :=
  match tbr with
  | true => is_pure o
  | false => o = ord_top
  end.

  Definition HoareCall
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec): gname -> Any.t -> (itree hAGEs) Any.t :=
  fun fn varg_src =>
  
    x <- trigger (Choose fsp.(meta));; 
  
    (*** precondition ***)
    varg_tgt <- trigger (Choose Any_tgt);;
    let ord_next := fsp.(measure) x in
    trigger (Guarantee ((fsp.(precond) x varg_src varg_tgt) ∗ ⌜ord_lt ord_next ord_cur⌝%I ∗ (⌜ord_eval tbr ord_next⌝%I)));;;

    (*** call ***)
    vret_tgt <- trigger (Call fn varg_tgt);; 

    (*** postcondition ***)
    vret_src <- trigger (Take Any.t);;
    trigger (Assume (fsp.(postcond) x vret_src vret_tgt));;;

    Ret vret_src
  .  


  Definition HoareCallPre
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec): gname -> Any.t -> (itree hAGEs) _ :=
  fun fn varg_src =>
  
    x <- trigger (Choose fsp.(meta));; 
  
    (*** precondition ***)
    varg_tgt <- trigger (Choose Any.t);;
    let ord_next := fsp.(measure) x in
    trigger (Guarantee ((fsp.(precond) x varg_src varg_tgt) ∗ ⌜ord_lt ord_next ord_cur⌝%I ∗ (⌜ord_eval tbr ord_next⌝%I)));;;
    Ret (x, varg_tgt).

  Definition HoareCallPost
        (tbr: bool) (ord_cur: ord) (fsp: fspec) vret_tgt x : (itree hAGEs) Any.t :=
    vret_src <- trigger (Take Any.t);;
    trigger (Assume (fsp.(postcond) x vret_src vret_tgt));;;
    Ret vret_src
  .

  Lemma HoareCall_parse
        (tbr: bool)
        (ord_cur: ord)
        (fsp: fspec)
        (fn: gname)
        (varg_src: Any.t)
    :
      HoareCall tbr ord_cur fsp fn varg_src =
      '(x, varg_tgt) <- HoareCallPre tbr ord_cur fsp fn varg_src;;
      vret_tgt <- trigger (Call fn varg_tgt);;
      HoareCallPost tbr ord_cur fsp vret_tgt x
  .
  Proof.
    unfold HoareCall, HoareCallPre, HoareCallPost. grind.
  Qed.

  Variable stb: gname -> option fspec.


Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most} : ord -> itree hAGEs unit :=
  fun ord_cur => 
  break <- trigger (Choose _);;
  if break: bool
  then Ret tt
  else
    n <- trigger (Choose Ord.t);;
    trigger (Choose (n < at_most)%ord);;;
    '(fn, varg) <- trigger (Choose _);;
    fsp <- (stb fn)ǃ;;
    _ <- HoareCall true ord_cur fsp fn varg;;
    (_APC n) _ ord_cur.
Next Obligation.
  i. auto.
Qed.
Next Obligation.
  eapply Ord.lt_well_founded.
Qed.

Definition HoareAPC (ord_cur: ord): itree hAGEs unit :=
  at_most <- trigger (Choose _);;
  _APC at_most ord_cur
.

Lemma unfold_APC:
  forall at_most ord_cur, _APC at_most ord_cur = 
                  break <- trigger (Choose _);;
                  if break: bool
                  then Ret tt
                  else
                    n <- trigger (Choose Ord.t);;
                    guarantee (n < at_most)%ord;;;
                    '(fn, varg) <- trigger (Choose _);;
                    fsp <- (stb fn)ǃ;;
                    _ <- HoareCall true ord_cur fsp fn varg;;
                    (_APC n) ord_cur.
Proof.
  i. unfold _APC. rewrite Fix_eq; eauto.
  { repeat f_equal. extensionality break. destruct break; ss.
    repeat f_equal. extensionality n.
    unfold guarantee. rewrite bind_bind.
    repeat f_equal. extensionality p.
    rewrite bind_ret_l. repeat f_equal. extensionality x. destruct x. auto. }
  { i. replace g with f; auto. extensionality o. eapply H. }
Qed.
Global Opaque _APC.

  Record fspecbody: Type := mk_specbody {
    fsb_fspec:> fspec;
    fsb_body: Any.t -> itree hEs Any.t;
  }
  .

  Definition mk_simple {X: Type} (DPQ: X -> ord * (Any_tgt -> iProp) * (Any_tgt -> iProp)): fspec :=
    mk_fspec (fst ∘ fst ∘ DPQ)
             (fun x y a => (((snd ∘ fst ∘ DPQ) x a: iProp) ∧ ⌜y = a⌝)%I)
             (fun x z a => (((snd ∘ DPQ) x a: iProp) ∧ ⌜z = a⌝)%I)
  .

  Definition handle_hAPCE_hAGEs (ord_cur: ord): hAPCE ~> itree hAGEs :=
        fun _ '(hAPC) => HoareAPC ord_cur.

  Definition handle_callE_hAGEs ord_cur: callE ~> itree hAGEs :=
    fun _ '(Call fn arg) => 
          fsp <- (stb fn)ǃ;;
          HoareCall false ord_cur fsp fn arg
    .

  Definition interp_hEs_hAGEs ord_cur: itree hEs ~> itree hAGEs :=
    interp (case_ (bif:=sum1) (trivial_Handler) (case_ (bif:=sum1) (handle_hAPCE_hAGEs ord_cur)
                          (case_ (bif:=sum1) (handle_callE_hAGEs ord_cur)
                                  trivial_Handler))).    

  Definition HoareFun
             {X: Type}
             (D: X -> ord)
             (P: X -> Any.t -> Any_tgt -> iProp)
             (Q: X -> Any.t -> Any_tgt -> iProp)
             (body: Any.t -> itree hEs Any.t): Any_tgt -> itree hAGEs Any_tgt := fun varg_tgt =>
    x <- trigger (Take X);;

    (* ASSUME *)
    varg_src <- trigger (Take _);;
    let ord_cur := D x in
    trigger (Assume (P x varg_src varg_tgt));;; (*** precondition ***)


    vret_src <- interp_hEs_hAGEs
                          ord_cur
                             (match ord_cur with
                              | ord_pure _ => _ <- trigger hAPC;; trigger (Choose _)
                              | _ => body (varg_src)
                              end);;

    (* ASSERT *)
    vret_tgt <- trigger (Choose Any_tgt);;
    trigger (Guarantee (Q x vret_src vret_tgt));;; (*** postcondition ***)


    Ret vret_tgt
  .

  Definition interp_sb_hp (sb: fspecbody): (Any_tgt -> itree hAGEs Any_tgt) :=
    let fs: fspec := sb.(fsb_fspec) in
    (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body)))
  .


  Definition handle_sE_tgt: sE ~> itree Es :=
      (fun _ e =>
         match e with
         | SUpdate run => pupdate run
         end).
  
  Definition handle_Assume P: stateT (Σ) (itree Es) unit :=
    fun fr =>
      r <- trigger (Take Σ);;
      mr <- mget;; 
      assume (URA.wf (r ⋅ fr ⋅ mr));;;
      assume(Own r ⊢ P);;; 
      Ret (r ⋅ fr, tt).
  
  Definition handle_Guarantee P: stateT (Σ) (itree Es) unit :=
    fun fr =>
      '(r, fr', mr') <- trigger (Choose (Σ * Σ * Σ));;
      mr <- mget;;
      guarantee(Own (fr ⋅ mr) ⊢ #=> Own (r ⋅ fr' ⋅ mr'));;;
      guarantee(Own r ⊢ P);;;
      mput mr';;;
      Ret (fr', tt).

  Definition handle_hAGE_tgt: hAGE ~> stateT (Σ) (itree Es) :=
    fun _ e fr =>
      match e with
      | Assume P => handle_Assume P fr
      | Guarantee P => handle_Guarantee P fr
      end
  .

  Definition interp_hp : itree hAGEs ~> stateT Σ (itree Es) :=
      interp_state 
        (case_ (bif:=sum1) (handle_hAGE_tgt)
        (case_ (bif:=sum1) ((fun T X fr => '(fr', _) <- (handle_Guarantee (True%I) fr);; x <- trigger X;; Ret (fr', x)): _ ~> stateT Σ (itree Es)) 
        (case_ (bif:=sum1) ((fun T X fr => x <- handle_sE_tgt X;; Ret (fr, x)): _ ~> stateT Σ (itree Es)) 
                           ((fun T X fr => x <- trigger X;; Ret (fr, x)): _ ~> stateT Σ (itree Es)))))
    .

  Definition hp_fun_tail := (fun '(fr, x) => handle_Guarantee (True%I) fr ;;; Ret (x: Any.t)).
    
  Definition interp_hp_body (i: itree hAGEs Any.t) (fr: Σ) : itree Es Any.t :=
    interp_hp i fr >>= hp_fun_tail.

  Definition interp_hp_fun (f: Any.t -> itree hAGEs Any.t) : Any.t -> itree Es Any.t :=
    fun x => interp_hp_body (f x) ε.
  
End CANCEL.

End PSEUDOTYPING.


Section TRANSL. 
  Context {Σ: GRA.t}.

  Definition body_spec_hp stb o (body: itree hEs Any.t): itree hAGEs Any.t :=
    interp_hEs_hAGEs stb o body.

  Definition fun_spec_hp stb o (f: Any.t -> itree hEs Any.t): Any.t -> itree hAGEs Any.t :=
    fun x => body_spec_hp stb o (f x).

  Definition interp_Es_hAGEs: itree Es ~> itree hAGEs :=
    interp trivial_Handler.
    
  Definition lift_Es_fun (f: Any.t -> itree Es Any.t): Any.t -> itree hAGEs Any.t :=
    fun x => interp_Es_hAGEs (f x).

  Definition fun_to_tgt stb (sb: fspecbody): (Any.t -> itree Es Any.t) :=
    interp_hp_fun (interp_sb_hp stb sb).
    
End TRANSL.


(********** Modules **********)

Module HModSem.
Section HMODSEM.
  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems : alist gname (Any.t -> itree hAGEs Any.t);
    initial_st : itree eventE Any.t;
    initial_cond: iProp;
  }
  .

  Definition transl (tr: (Any.t -> itree hAGEs Any.t) -> Any.t -> itree Es Any.t) (mst: t -> itree eventE Any.t) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, bd) => (fn, tr bd)) ms.(fnsems);
    ModSem.init_st := mst ms;
  |}
  .

  Definition to_mod (ms: t): ModSem.t := transl (interp_hp_fun) initial_st ms.


  (* move lifting Mod -> HMod into somewhere else *)
  Definition lift (ms: ModSem.t): t := {|
    fnsems := List.map (fun '(fn, bd) => (fn, lift_Es_fun bd)) (ModSem.fnsems ms);
    initial_st := ModSem.init_st ms;
    initial_cond := ⌜True⌝%I
  |}
  .

  (**** Linking (need refactor)****)

  (* Definition translate_emb : Type := forall T, itree Es T -> itree Es T. *)

  Definition emb_ : ModSem.RUN -> (forall T, hAGEs T -> hAGEs T) :=
    fun run_ch T es =>
      match es with
      | inr1 (inr1 (inl1 (SUpdate run))) => inr1 (inr1 (inl1 (SUpdate (run_ch T run))))
      | _ => es
      end.

  Definition emb_l := emb_ ModSem.run_l.

  Definition emb_r := emb_ ModSem.run_r.

  Definition trans_l '(fn, f): gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate (emb_ ModSem.run_l) (f args))).

  Definition trans_r '(fn, f) : gname * (Any.t -> itree _ Any.t) :=
    (fn, (fun args => translate (emb_ ModSem.run_r) (f args))).
  
  Definition add_fnsems ms1 ms2: alist gname (Any.t -> itree _ Any.t) :=
    (List.map trans_l ms1.(fnsems)) ++ (List.map trans_r ms2.(fnsems)).
  
  Definition add ms1 ms2: t := {|
    fnsems := add_fnsems ms1 ms2;
    initial_st := st1 <- (initial_st ms1);; st2 <- (initial_st ms2);; Ret (Any.pair st1 st2);
    (* initial_st := Any.pair (initial_st ms1) (initial_st ms2); *)
    initial_cond := (initial_cond ms1) ∗ (initial_cond ms2);
  |}.

End HMODSEM.
End HModSem.

Module HMod.
Section HMOD.
  Context `{Σ: GRA.t}.
  Context `{Sk.ld}.

  Record t: Type := mk {
    get_modsem: Sk.t -> HModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: Sk.t -> (Any.t -> itree hAGEs Any.t) -> Any.t -> itree Es Any.t) (mst: HModSem.t -> itree eventE Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => HModSem.transl (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  . 


  (********** What will be initial_st of Mod? (How to compile initial_cond) *********)
  Definition to_mod (md: t): Mod.t := transl (fun _ => interp_hp_fun) HModSem.initial_st md.

  Definition lift (md: Mod.t): t := {|
    get_modsem := fun sk => HModSem.lift (md.(Mod.get_modsem) sk);
    sk := md.(Mod.sk);
  |}
  .

  (***** LINKING ****)

  Definition add (md0 md1: t): t := {|
    get_modsem := fun sk => HModSem.add (md0.(get_modsem) sk) (md1.(get_modsem) sk);
    sk := Sk.add md0.(sk) md1.(sk);
  |}
  .
    
End HMOD.
End HMod.

Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.
  Variable stb: gname -> option fspec.
  (* Variable o: ord. *)

  Record t: Type := mk {
    fnsems: list (gname * fspecbody);
    initial_st: itree eventE Any.t;
    initial_cond: iProp;
  }
  .

  (* DEFINE HMod first. *)
  Definition transl (tr: fspecbody -> (Any.t -> itree hAGEs Any.t)) (mst: t -> itree eventE Any.t) (ms: t): HModSem.t := {|
    HModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    HModSem.initial_st := mst ms;
    HModSem.initial_cond := ms.(initial_cond);
  |}
  .

  (* Compile directly to ModSem. *)
  Definition compile (tr: fspecbody -> (Any.t -> itree Es Any.t)) (mst: t -> itree eventE Any.t) (ms: t) : ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    ModSem.init_st := mst ms;
  |}
 .
  Definition to_hmod (ms: t): HModSem.t := transl (interp_sb_hp stb) initial_st ms.
  (* Definition to_hmod (ms: t): HModSem.t := transl ((fun_spec_hp stb o) ∘ fsb_body) initial_st ms. *)
  (* Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid stb ∘ fsb_body) initial_st ms.
  Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid2 ∘ fsb_body) initial_st ms. *)
  (* Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := compile (fun_to_tgt stb) (fun ms => Any.pair ms.(initial_st) ms.(initial_mr)↑) ms. *)

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
      fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody))];
      (* initial_mr := ε; *)
      initial_st := Ret tt↑;
      initial_cond := ⌜True⌝%I;
    |}
  .

End SMODSEM.
End SModSem.


Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.
  Context `{Sk.ld}.
  Variable stb: Sk.t -> gname -> option fspec.
  (* Variable o: ord. *)

  Record t: Type := mk {
    get_modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: Sk.t -> fspecbody -> ( Any.t -> itree hAGEs Any.t)) (mst: SModSem.t -> itree eventE Any.t) (md: t): HMod.t := {|
    HMod.get_modsem := fun sk => SModSem.transl (tr sk) mst (md.(get_modsem) sk);
    HMod.sk := md.(sk);
  |}
  .

  Definition compile (tr: Sk.t -> fspecbody -> (Any.t -> itree Es Any.t)) (mst: SModSem.t -> itree eventE Any.t) (md: t) : Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.compile (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_hmod (md:t): HMod.t := transl (fun sk => (interp_sb_hp (stb sk))) SModSem.initial_st md.
  (* Definition to_hmod (md:t): HMod.t := transl (fun sk => (fun_spec_hp (stb sk) o) ∘ fsb_body) SModSem.initial_st md. *)


  (* Definition to_src (md: t): Mod.t := transl (fun _ => fun_to_src ∘ fsb_body) SModSem.initial_st md. *)
  (* Definition to_mid (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid stb ∘ fsb_body) SModSem.initial_st md. *)
  (* Definition to_mid2 (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid2 ∘ fsb_body) SModSem.initial_st md. *)
  (* Definition to_tgt (stb: Sk.t -> gname -> option fspec) (md: t): Mod.t :=
    compile (fun sk => fun_to_tgt (stb sk)) (fun ms => Any.pair ms.(SModSem.initial_st) ms.(SModSem.initial_mr)↑) md. *)

    
  Definition get_stb (mds: list t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.canon (fold_right Sk.add Sk.unit (List.map sk mds)).

  (* Definition get_initial_mrs (mds: list t): Sk.t -> Σ :=
    fun sk => fold_left (⋅) (List.map (SModSem.initial_mr ∘ (flip get_modsem sk)) mds) ε. *)

End SMOD.
End SMod.

  (* Definition get_stb (md: t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (SModSem.fnsems (get_modsem md sk)).

  Definition get_sk (md: t): Sk.t :=
    Sk.sort (Sk.add Sk.unit (sk md)).

  Definition get_init_mr (md: t): Sk.t -> Σ :=
    fun sk => (SModSem.initial_mr (get_modsem md sk)).
 *)

    

  (* Definition transl (tr: SModSem.t -> ModSem.t) (md: t): Mod.t := {| *)
  (*   Mod.get_modsem := (SModSem.transl tr) ∘ md.(get_modsem); *)
  (*   Mod.sk := md.(sk); *)
  (* |} *)
  (* . *)

  (* Definition to_src (md: t): Mod.t := transl SModSem.to_src md. *)
  (* Definition to_mid (md: t): Mod.t := transl SModSem.to_mid md. *)
  (* Definition to_tgt (stb: list (gname * fspec)) (md: t): Mod.t := transl (SModSem.to_tgt stb) md. *)

  (* Lemma to_src_comm: forall sk smd,
      (SModSem.to_src) (get_modsem smd sk) = (to_src smd).(Mod.get_modsem) sk.
  Proof. refl. Qed. *)
  (* Lemma to_mid_comm: forall sk stb smd,
      (SModSem.to_mid stb) (get_modsem smd sk) = (to_mid stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed. *)
  (* Lemma to_tgt_comm: forall sk stb smd,
      (SModSem.to_tgt (stb sk)) (get_modsem smd sk) = (to_tgt stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed. *)




  (* Definition l_bind A B (x: list A) (f: A -> list B): list B := List.flat_map f x. *)
  (* Definition l_ret A (a: A): list A := [a]. *)

  (* Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma unconcat
        A (xs: list A)
    :
      List.concat (List.map (fun x => [x]) xs) = xs
  .
  Proof.
    induction xs; ii; ss. f_equal; ss.
  Qed.

  Lemma red_do_ret A B (xs: list A) (f: A -> B)
    :
      (do x <- xs; ret (f x)) = List.map f xs
  .
  Proof.
    rewrite flat_map_concat_map.
    erewrite <- List.map_map with (f:=f) (g:=ret).
    rewrite unconcat. ss.
  Qed.

  Lemma red_do_ret2 A0 A1 B (xs: list (A0 * A1)) (f: A0 -> A1 -> B)
    :
      (do '(x0, x1) <- xs; ret (f x0 x1)) = List.map (fun '(x0, x1) => f x0 x1) xs
  .
  Proof.
    induction xs; ss. rewrite IHxs. destruct a; ss.
  Qed.



  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr0 mr0 mds
    :
      <<SK: Mod.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) = fold_right Sk.add Sk.unit (List.map sk mds)>>
  .
  Proof.
    induction mds; ss.
    destruct mds.
    - Local Transparent Mod.add_list. s. r. rewrite Sk.add_unit_r. Local Opaque Mod.add_list. refl. 
    - rewrite ModFacts.add_list_cons; ss. r. f_equal. ss.
  Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 mds
    :
      Mod.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) =
      Mod.sk (Mod.add_list (List.map (transl tr1 mr1) mds))
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition get_fnsems (sk: Sk.t) (md: t) (tr0: fspecbody -> Any.t -> itree Es Any.t) :=
    let ms := (get_modsem md sk) in
    (do '(fn, fsb) <- ms.(SModSem.fnsems);
      let fsem := tr0 fsb in
      ret (fn, fsem))
  .

  Fixpoint load_fnsems (sk: Sk.t) (mds: list t) (tr0: fspecbody -> Any.t -> itree Es Any.t) : list (string * (Any.t -> itree Es Any.t)):=
    match mds with
    | [] => nil
    | h::[] => get_fnsems sk h tr0
    | h::t => (List.map ModSem.trans_l (get_fnsems sk h tr0)) ++ (List.map ModSem.trans_r (load_fnsems sk t tr0))
    end.
    
  Let transl_fnsems_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSem.fnsems (Mod.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_fnsems sk mds (tr0 sk))
  .
  Proof.
    induction mds; ss.
    destruct mds.
    - Local Transparent Mod.add_list.
      ss. unfold get_fnsems.
      rewrite flat_map_concat_map.
      replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, (tr0 sk fsb))]) with
      (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, (tr0 sk fsb))));
      cycle 1.
      { apply func_ext. i. des_ifs. }
      erewrite <- List.map_map with (g:=ret).
      rewrite unconcat.
      apply map_ext. ii. des_ifs.
      Local Opaque Mod.add_list.
    - rewrite ModFacts.add_list_cons; ss.
      cbn. rewrite List.map_map. 
      unfold get_fnsems in *.
      rewrite ! flat_map_concat_map in *.
      replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, (tr0 sk fsb))]) with
      (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, (tr0 sk fsb)))) in *;
      cycle 1.
      { apply func_ext. i. des_ifs. }
      f_equal.
      { erewrite <- List.map_map with (g:=ret); rewrite unconcat.
        rewrite List.map_map. ss. }
      f_equal. ss.
Qed.

  Lemma transl_fnsems
        tr0 mr0 mds
    :
      (ModSem.fnsems (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_fnsems (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds (tr0 (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds)))))
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_fnsems_aux. do 2 f_equal.
    { rewrite transl_sk. ss. }
    rewrite transl_sk. auto.
  Qed.


  Lemma flat_map_assoc
        A B C
        (f: A -> list B)
        (g: B -> list C)
        (xs: list A)
    :
      (do y <- (do x <- xs; f x); g y) =
      (do x <- xs; do y <- (f x); g y)
  .
  Proof.
    induction xs; ii; ss.
    rewrite ! flat_map_concat_map in *. rewrite ! map_app. rewrite ! concat_app. f_equal; ss.
  Qed.

  Lemma transl_fnsems_stable
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSem.fnsems) =
      List.map fst (Mod.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSem.fnsems)
  .

  Proof.
    rewrite ! transl_fnsems.
    set (Sk.sort (foldr Sk.add Sk.unit (map sk mds))).
    clearbody a. revert a.
    induction mds; ss. i.
    unfold get_fnsems.
    destruct mds. 
    { 
      rewrite <- ! red_do_ret.
      rewrite ! flat_map_assoc. eapply flat_map_ext. i. des_ifs.
    }
    rewrite ! List.map_app.
    rewrite ! List.map_map.
    rewrite fun_fst_trans_l.
    rewrite fun_fst_trans_r.
    rewrite <- IHmds.
    f_equal.
    rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i. des_ifs.
Qed.

  Fixpoint link_mrs mrs : Any.t :=
    match mrs with
    | [] => tt↑
    | h::[] => h
    | h::t => Any.pair h (link_mrs t)
    end.


  Definition load_initial_mrs (sk: Sk.t) (mds: list t) (mr0: SModSem.t -> Any.t): Any.t :=
    let mrs := (do md <- mds;
    let ms := (get_modsem md sk) in
    ret (mr0 ms)) in
    link_mrs mrs
    (* How to link initial states *)
  .

  Let transl_initial_mrs_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSem.init_st (Mod.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_initial_mrs sk mds mr0)
  .
  Proof.
    induction mds; ii; ss.
    destruct mds; ss.
    rewrite ModFacts.add_list_cons; ss. cbn. f_equal; ss.
  Qed.

  Lemma transl_initial_mrs
        tr0 mr0 mds
    :
      (ModSem.init_st (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_initial_mrs (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds mr0)
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_initial_mrs_aux. do 2 f_equal. rewrite transl_sk. ss.
  Qed.

            

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
    get_modsem := fun _ => (SModSem.main mainpre mainbody);
    sk := Sk.unit;
  |}
  .

End SMOD.
End SMod. *)





  (* (* Which fr to put in interp_hp & What to return *) *)
  (* Definition interp_hp_fun (hp: Any.t -> itree hAGEs Any.t): Any.t -> itree Es Any.t := *)
  (*   fun arg => interp_hp_fun (hp arg) ε >>= (fun '(_, x) => Ret x). *)

    
    (*  *)
  (* Definition body_to_agEs (ord_cur: ord)
             {X} (body: X -> itree hEs Any_src): X -> itree hAGEs Any_src :=
    (@interp_Es'_agEs ord_cur _) ∘ (@interp_hEs_Es' _) ∘ body.


  

  Definition body_to_tgt
             {X} (body: X -> itree hAGEs Any_src): X -> stateT Σ (itree Es) Any_src :=
    (@interp_agEs_tgt _) ∘ body. *)



  (* Definition HoareFun
             {X: Type}
             (D: X -> ord)
             (P: X -> Any.t -> Any_tgt -> iProp)
             (Q: X -> Any.t -> Any_tgt -> iProp)
             (body: Any.t -> itree hEs Any.t): Any_tgt -> itree Es Any_tgt := fun varg_tgt =>
    x <- trigger (Take X);;

    (* ASSUME *)
    varg_src <- trigger (Take _);;
    '(rarg) <- trigger (Take _);;
    mr <- mget;;
    assume(URA.wf (rarg ⋅ mr));;;
    let ord_cur := D x in
    assume(P x varg_src varg_tgt rarg);;; (*** precondition ***)
    '(fr0, vret_src) <- interp_Es'_tgt
                          ord_cur
                          (interp_hEs_tgt
                             (match ord_cur with
                              | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                              | _ => body (varg_src)
                              end)) rarg;;

    (* ASSERT *)
    vret_tgt <- trigger (Choose Any_tgt);;
    '(_, rret) <- update_and_discard fr0;;
    guarantee(Q x vret_src vret_tgt rret);;; (*** postcondition ***)


    Ret vret_tgt
  .

  Definition fun_to_tgt (sb: fspecbody): (Any_tgt -> itree Es Any_tgt) :=
    let fs: fspec := sb.(fsb_fspec) in
    (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body)))
  . *)

(*** NOTE:
body can execute eventE events.
Notably, this implies it can also execute UB.
With this flexibility, the client code can naturally be included in our "type-checking" framework.
Also, note that body cannot execute "rE" on its own. This is intended.

NOTE: we can allow normal "callE" in the body too, but we need to ensure that it does not call "HoareFun".
If this feature is needed; we can extend it then. At the moment, I will only allow hCallE.
***)

(* 
  Definition HoareFunArg
             {X: Type}
             (P: X -> Any.t -> Any_tgt -> iProp):
    Any_tgt -> itree Es ((Σ) * (X * Any.t)) := fun varg_tgt =>
    x <- trigger (Take X);;
    (*ASSUME*)
    varg_src <- trigger (Take _);;
    '(rarg) <- trigger (Take _);;
    mr <- mget;;
    assume(URA.wf (rarg ⋅ mr));;;
    assume(P x varg_src varg_tgt rarg);;; (*** precondition ***)
    Ret (rarg, (x, varg_src))
  .

  Definition HoareFunRet
             {X: Type}
             (Q: X -> Any.t -> Any_tgt -> iProp):
    X -> ((Σ) * Any.t) -> itree Es Any_tgt := fun x '(fr0, vret_src) =>
    (*ASSERT*)
    vret_tgt <- trigger (Choose Any_tgt);;
    '(_, rret) <- update_and_discard fr0;;
    guarantee(Q x vret_src vret_tgt rret);;; (*** postcondition ***)
    Ret vret_tgt
  .

  Lemma HoareFun_parse
        {X: Type}
        (D: X -> ord)
        (P: X -> Any.t -> Any_tgt -> iProp)
        (Q: X -> Any.t -> Any_tgt -> iProp)
        (body: Any.t -> itree hEs Any.t)
        (varg_tgt: Any_tgt)
    :
      HoareFun D P Q body varg_tgt =
      '(ctx, (x, varg_src)) <- HoareFunArg P varg_tgt;;
      interp_Es'_tgt (D x)
                        (interp_hEs_tgt
                           (match D x with
                            | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                            | _ => body varg_src
                            end)) ctx >>= (HoareFunRet Q x).
  Proof.
    unfold HoareFun, HoareFunArg, HoareFunRet. grind.
  Qed.
*)
  (* End INTERP. *)
 


  (* Variable md_tgt: Mod.t.
  Let ms_tgt: ModSem.t := (Mod.get_modsem md_tgt md_tgt.(Mod.sk)).

  Variable sbtb: alist gname fspecbody.
  Let stb: alist gname fspec := List.map (fun '(gn, fsb) => (gn, fsb_fspec fsb)) sbtb.




 *)




(* TODO: following 'mid' definitions are auxilary functions for proving cancelation thm *)


  (* Definition handle_hCallE_mid2: hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      match tbr with
      | true => tau;; trigger (Choose _)
      | false => trigger (Call fn varg_src)
      end
  .

  Definition interp_hCallE_mid2: itree Es' ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid2)
                  trivial_Handler)
  .

  Definition body_to_mid2 {X} (body: X -> itree (hCallE +' sE +' eventE) Any.t): X -> itree Es Any.t :=
    (@interp_hCallE_mid2 _) ∘ body
  .

  Definition fun_to_mid2 (body: Any.t -> itree hEs Any.t): (Any_src -> itree Es Any_src) :=
    body_to_mid2 ((@interp_hEs_tgt _) ∘ body)
  .


  Definition handle_hCallE_mid (ord_cur: ord): hCallE ~> itree Es :=
    fun _ '(hCall tbr fn varg_src) =>
      tau;;
      f <- (stb fn)ǃ;; guarantee (tbr = true -> ~ (forall x, f.(measure) x = ord_top));;;
      ord_next <- (if tbr then o0 <- trigger (Choose _);; Ret (ord_pure o0) else Ret ord_top);;
      guarantee(ord_lt ord_next ord_cur);;;
      let varg_mid: Any_mid := Any.pair ord_next↑ varg_src in
      trigger (Call fn varg_mid)
  .

  Definition interp_hCallE_mid (ord_cur: ord): itree Es' ~> itree Es :=
    interp (case_ (bif:=sum1) (handle_hCallE_mid ord_cur)
                  ((fun T X => trigger X): _ ~> itree Es))
  .

  Definition body_to_mid (ord_cur: ord) {X} (body: X -> itree (hCallE +' sE +' eventE) Any.t): X -> itree Es Any.t :=
    fun varg_mid => interp_hCallE_mid ord_cur (body varg_mid)
  .

  Definition fun_to_mid (body: Any.t -> itree hEs Any.t): (Any_mid -> itree Es Any_src) :=
    fun ord_varg_src =>
      '(ord_cur, varg_src) <- (Any.split ord_varg_src)ǃ;; ord_cur <- ord_cur↓ǃ;;
      interp_hCallE_mid ord_cur (interp_hEs_tgt
                                   (match ord_cur with
                                    | ord_pure n => _ <- trigger hAPC;; trigger (Choose _)
                                    | _ => body (varg_src)
                                    end)). *)









Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_hp_bind
      (R S: Type)
      (s : itree hAGEs R) (k : R -> itree hAGEs S)
      fmr
  :
    interp_hp (s >>= k) fmr
    =
    st <- interp_hp s fmr;; interp_hp (k st.2) st.1.
Proof.
  unfold interp_hp in *. eapply interp_state_bind.
Qed.

Lemma interp_hp_body_bind
  R (s : itree hAGEs R) (k : R -> itree hAGEs Any.t) fmr
  :
  interp_hp_body (s >>= k) fmr
  =
  '(fr,r) <- interp_hp s fmr;; interp_hp_body (k r) fr.
Proof.
  unfold interp_hp_body. rewrite interp_hp_bind. grind. destruct x. eauto.
Qed.


Lemma interp_hp_tau
      (U: Type)
      (t : itree _ U)
      fmr
  :
    interp_hp (tau;; t) fmr
    =
    tau;; (interp_hp t fmr).
Proof.
  unfold interp_hp in *. eapply interp_state_tau.
Qed.

Lemma interp_hp_ret
      (U: Type)
      (t: U)
      fmr
  :
    interp_hp (Ret t) fmr
    =
    Ret (fmr, t).
Proof.
  unfold interp_hp in *. eapply interp_state_ret.
Qed.

Lemma interp_hp_call
      (R: Type)
      (i: callE R)
      fr
  :
    interp_hp (trigger i) fr
    =
    '(fr', _) <- handle_Guarantee (True%I:iProp) fr;; r <- trigger i;; tau;; Ret (fr', r).
Proof.
  unfold interp_hp in *. grind.
Qed.

Lemma interp_hp_triggerp
      (R: Type)
      (i: sE R)
      fmr
  :
    interp_hp (trigger i) fmr
    =
    r <- handle_sE_tgt i;; tau;; Ret (fmr, r).
Proof.
  unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_hp_triggere
      (R: Type)
      (i: eventE R)
      fmr
  :
    interp_hp (trigger i) fmr
    =
    r <- trigger i;; tau;; Ret (fmr, r).
Proof.
  unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_hp_triggerUB
      (R: Type)
      fmr
  :
    interp_hp (triggerUB) fmr
    =
    triggerUB (A:=Σ*R).
Proof.
  unfold interp_hp, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_hp_triggerNB
      (R: Type)
      fmr
  :
    interp_hp (triggerNB) fmr
    =
    triggerNB (A:=Σ*R).
Proof.
  unfold interp_hp, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_hp_unwrapU 
      (R: Type)
      (i: option R)
      fmr
  :
    interp_hp (@unwrapU hAGEs _ _ i) fmr
    =
    r <- (unwrapU i);; Ret (fmr, r).
Proof.
  unfold interp_hp, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_hp_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hp_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_hp_unwrapN
      (R: Type)
      (i: option R)
      fmr
  :
    interp_hp (@unwrapN hAGEs _ _ i) fmr
    =
    r <- (unwrapN i);; Ret (fmr, r).
Proof.
  unfold interp_hp, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_hp_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hp_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_hp_Assume
      P
      fmr
  :
    interp_hp (trigger (Assume P)) fmr
    =
    x <- handle_Assume P fmr ;; tau;; Ret x
.
Proof.
  unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_hp_Guarantee
      P
      fmr
  :
    interp_hp (trigger (Guarantee P)) fmr
    =
    x <- handle_Guarantee P fmr ;; tau;; Ret x
.
Proof.
  unfold interp_hp. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_hp_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
      fmr
  :
    interp_hp itr0 fmr
    =
    interp_hp itr1 fmr
.
Proof. subst; et. Qed.

Global Program Instance interp_hp_rdb: red_database (mk_box (@interp_hp)) :=
  mk_rdb
    1
    (mk_box interp_hp_bind)
    (mk_box interp_hp_tau)
    (mk_box interp_hp_ret)
    (mk_box interp_hp_call)
    (mk_box interp_hp_triggere)
    (mk_box interp_hp_triggerp)
    (mk_box interp_hp_triggerp)
    (mk_box interp_hp_triggerUB)
    (mk_box interp_hp_triggerNB)
    (mk_box interp_hp_unwrapU)
    (mk_box interp_hp_unwrapN)
    (mk_box interp_hp_Assume)
    (mk_box interp_hp_Guarantee)
    (mk_box interp_hp_ext)
.

End AUX.

Section AUX.

Context `{Σ: GRA.t}.

(* itree reduction *)
Lemma interp_hAGEs_bind
      (R S: Type)
      stb o
      (s : itree hEs R) (k : R -> itree hEs S)
  :
    interp_hEs_hAGEs stb o (s >>= k)
    =
    st <- interp_hEs_hAGEs stb o s;; interp_hEs_hAGEs stb o (k st).
Proof.
  unfold interp_hEs_hAGEs in *. grind.
Qed.

Lemma interp_hAGEs_tau
      (U: Type)
      (t : itree _ U)
      stb o
  :
    interp_hEs_hAGEs stb o (tau;; t)
    =
    tau;; (interp_hEs_hAGEs stb o t).
Proof.
  unfold interp_hEs_hAGEs in *. grind.
Qed.

Lemma interp_hAGEs_ret
      (U: Type)
      (t: U)
      stb o
  :
    interp_hEs_hAGEs stb o (Ret t)
    =
    Ret t.
Proof.
  unfold interp_hEs_hAGEs in *. grind.
Qed.

Lemma interp_hAGEs_call
      (R: Type)
      (i: callE R)
      stb o
  :
    interp_hEs_hAGEs stb o (trigger i)
    =
    r <- handle_callE_hAGEs stb o i;; tau;; Ret r.
    (* '(fr', _) <- handle_Guarantee (True%I:iProp) fr;; r <- trigger i;; tau;; Ret (fr', r). *)
Proof.
  unfold interp_hEs_hAGEs in *. rewrite interp_trigger. grind.
Qed.

Lemma interp_hAGEs_hapc
      (R: Type)
      (i: hAPCE R)
      stb o
  :
    interp_hEs_hAGEs stb o (trigger i)
    =
    (handle_hAPCE_hAGEs stb o i) >>= (fun r => tau;; Ret r).
Proof.
  unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
Qed.

Lemma interp_hAGEs_triggerp
      (R: Type)
      (i: sE R)
      stb o
  :
    interp_hEs_hAGEs stb o (trigger i)
    =
    r <- trigger i;; tau;; Ret r.
Proof.
  unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
Qed.

Lemma interp_hAGEs_triggere
      (R: Type)
      (i: eventE R)
      stb o
  :
    interp_hEs_hAGEs stb o (trigger i)
    =
    r <- trigger i;; tau;; Ret r.
Proof.
  unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
Qed.

Lemma interp_hAGEs_assume
      stb o P
  :
    interp_hEs_hAGEs stb o (assume P)
    =
    r <- assume P;; tau;; Ret r.
Proof.
  unfold assume. rewrite interp_hAGEs_bind. rewrite interp_hAGEs_triggere. grind. rewrite interp_hAGEs_ret. refl.
Qed. 

Lemma interp_hAGEs_guarantee
      stb o P
  :
    interp_hEs_hAGEs stb o (guarantee P)
    =
    r <- guarantee P;; tau;; Ret r.
Proof.
  unfold guarantee. rewrite interp_hAGEs_bind. rewrite interp_hAGEs_triggere. grind. rewrite interp_hAGEs_ret. refl.
Qed.

Lemma interp_hAGEs_triggerUB
      (R: Type)
      stb o
  :
    interp_hEs_hAGEs stb o (triggerUB)
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_hAGEs, triggerUB in *. rewrite unfold_interp. grind.
Qed.

Lemma interp_hAGEs_triggerNB
      (R: Type)
      stb o
  :
    interp_hEs_hAGEs stb o (triggerNB)
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_hAGEs, triggerNB in *. rewrite unfold_interp. grind.
Qed.

Lemma interp_hAGEs_unwrapU 
      (R: Type)
      (i: option R)
      stb o
  :
    interp_hEs_hAGEs stb o (@unwrapU hEs _ _ i)
    =
    r <- (unwrapU i);; Ret r.
Proof.
  unfold interp_hEs_hAGEs, unwrapU in *. des_ifs; grind.
  eapply interp_hAGEs_triggerUB.
Qed.

Lemma interp_hAGEs_unwrapN
      (R: Type)
      (i: option R)
      stb o
  :
    interp_hEs_hAGEs stb o (@unwrapN hEs _ _ i)
    =
    r <- (unwrapN i);; Ret r.
Proof.
  unfold interp_hEs_hAGEs, unwrapN in *. des_ifs; grind.
  eapply interp_hAGEs_triggerNB.
Qed.

Lemma interp_hAGEs_Assume
      P
      stb o
  :
    interp_hEs_hAGEs stb o (trigger (Assume P))
    =
    x <- trigger (Assume P) ;; tau;; Ret x
.
Proof.
  unfold interp_hEs_hAGEs. rewrite interp_trigger. grind.
Qed.

Lemma interp_hAGEs_Guarantee
      P
      stb o
  :
    interp_hEs_hAGEs stb o (trigger (Guarantee P))
    =
    x <- trigger (Guarantee P);; tau;; Ret x
.
Proof.
  unfold interp_hEs_hAGEs. rewrite interp_trigger. grind. 
Qed.

Lemma interp_hAGEs_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
      stb o
  :
    interp_hEs_hAGEs stb o itr0
    =
    interp_hEs_hAGEs stb o itr1
.
Proof. subst; et. Qed.

End AUX.

Global Program Instance interp_hAGEs_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hEs_hAGEs)) :=
  mk_rdb
    1
    (mk_box interp_hAGEs_bind)
    (mk_box interp_hAGEs_tau)
    (mk_box interp_hAGEs_ret)
    (mk_box interp_hAGEs_call)
    (mk_box interp_hAGEs_triggere)
    (mk_box interp_hAGEs_triggerp)
    (mk_box interp_hAGEs_triggerp)
    (mk_box interp_hAGEs_triggerUB)
    (mk_box interp_hAGEs_triggerNB)
    (mk_box interp_hAGEs_unwrapU)
    (mk_box interp_hAGEs_unwrapN)
    (mk_box interp_hAGEs_Assume)
    (mk_box interp_hAGEs_Guarantee)
    (mk_box interp_hAGEs_ext)
.

Section AUX.

  Context `{Σ: GRA.t}.

  Lemma translate_emb_bind
    A B
    run_
    (itr: itree hAGEs A) (ktr: A -> itree hAGEs B)
  :
    translate (HModSem.emb_ run_) (itr >>= ktr) = a <- (translate (HModSem.emb_ run_) itr);; (translate (HModSem.emb_ run_) (ktr a))
  .
  Proof. rewrite (bisim_is_eq (translate_bind _ _ _)). et. Qed.

  Lemma translate_emb_tau
    A
    run_
    (itr: itree hAGEs A)
  :
    translate (HModSem.emb_ run_) (tau;; itr) = tau;; (translate (HModSem.emb_ run_) itr)
  .
  Proof. rewrite (bisim_is_eq (translate_tau _ _)). et. Qed.

  Lemma translate_emb_ret
      A (a: A) run_
  :
    translate (HModSem.emb_ run_) (Ret a) = Ret a
  .
  Proof. rewrite (bisim_is_eq (translate_ret _ _)). et. Qed.

  Lemma translate_emb_callE
      run_ fn args
  :
    translate (HModSem.emb_ run_) (trigger (Call fn args)) =
    trigger (Call fn args)
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss. 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_sE
      T run_
      (run : Any.t -> Any.t * T)
  :
    translate (HModSem.emb_ run_) (trigger (SUpdate run)) = trigger (SUpdate (run_ T run))
  .
  Proof. 
    unfold trigger. 
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). 
    do 2 f_equal. extensionalities. apply translate_emb_ret. 
  Qed.

  Lemma translate_emb_eventE
      T run_ 
      (e: eventE T)
    :
      translate (HModSem.emb_ run_) (trigger e) = trigger e.
  Proof.
    unfold trigger.
    rewrite (bisim_is_eq (translate_vis _ _ _ _)). ss.
    do 2 f_equal.
    extensionalities. rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_triggerUB
    T run_
  :
    translate (HModSem.emb_ run_) (triggerUB: itree _ T) = triggerUB
  .
  Proof. 
    unfold triggerUB. rewrite translate_emb_bind. f_equal.
    { extensionalities. ss. }
    apply translate_emb_eventE.
  Qed.

  Lemma translate_emb_triggerNB
    T run_
  :
    translate (HModSem.emb_ run_) (triggerNB: itree _ T) = triggerNB
  .
  Proof.
    unfold triggerNB. rewrite translate_emb_bind. f_equal. 
    { extensionalities. ss. }
    apply translate_emb_eventE.
  Qed.
  
  Lemma translate_emb_unwrapU
    R run_ (r: option R)
  :
    translate (HModSem.emb_ run_) (unwrapU r) = unwrapU r
  .
  Proof.
    unfold unwrapU. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerUB.
  Qed.

  Lemma translate_emb_unwrapN
    R run_ (r: option R)
  :
    translate (HModSem.emb_ run_) (unwrapN r) = unwrapN r
  .
  Proof.
    unfold unwrapN. destruct r.
    - apply translate_emb_ret.
    - apply translate_emb_triggerNB.
  Qed.

  Lemma translate_emb_assume
    run_ P
  :
    translate (HModSem.emb_ run_) (assume P) = assume P
  .
  Proof.
    unfold assume. rewrite translate_emb_bind.
    rewrite translate_emb_eventE. f_equal.
    extensionalities.
    rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_guarantee
    run_ P
  :
    translate (HModSem.emb_ run_) (guarantee P) = guarantee P
  .
  Proof.
    unfold guarantee. rewrite translate_emb_bind.
    rewrite translate_emb_eventE. f_equal.
    extensionalities.
    rewrite translate_emb_ret. et.
  Qed.

  Lemma translate_emb_ext
    T run_ (itr0 itr1: itree _ T)
    (EQ: itr0 = itr1)
  :
    translate (HModSem.emb_ run_) itr0 = translate (HModSem.emb_ run_) itr1
  .
  Proof. subst. refl. Qed.
  

  Global Program Instance translate_emb_rdb: red_database (mk_box (@translate)) :=
  mk_rdb
    0
    (mk_box translate_emb_bind)
    (mk_box translate_emb_tau)
    (mk_box translate_emb_ret)
    (mk_box translate_emb_sE)
    (mk_box translate_emb_sE)
    (mk_box translate_emb_callE)
    (mk_box translate_emb_eventE)
    (mk_box translate_emb_triggerUB)
    (mk_box translate_emb_triggerNB)
    (mk_box translate_emb_unwrapU)
    (mk_box translate_emb_unwrapN)
    (mk_box translate_emb_assume)
    (mk_box translate_emb_guarantee)
    (mk_box translate_emb_ext)
.

End AUX.




(* TODO: Modify the Definition of  Spec Module *)
(* TODO: Modify the Definition of  Spec Module *)
(* TODO: Modify the Definition of  Spec Module *)
(* TODO: Modify the Definition of  Spec Module *)
(* TODO: Modify the Definition of  Spec Module *)
(* TODO: Modify the Definition of  Spec Module *)


(* Module SModSem.
Section SMODSEM.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    fnsems: list (gname * fspecbody);
    initial_mr: Σ;
    initial_st: Any.t;
  }
  .

  Definition transl (tr: fspecbody -> (Any.t -> itree Es Any.t)) (mst: t -> Any.t) (ms: t): ModSem.t := {|
    ModSem.fnsems := List.map (fun '(fn, sb) => (fn, tr sb)) ms.(fnsems);
    ModSem.init_st := mst ms;
  |}
  .

  Definition to_src (ms: t): ModSem.t := transl (fun_to_src ∘ fsb_body) initial_st ms.
  (* Definition to_mid (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid stb ∘ fsb_body) initial_st ms.
  Definition to_mid2 (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_mid2 ∘ fsb_body) initial_st ms. *)
  Definition to_tgt (stb: gname -> option fspec) (ms: t): ModSem.t := transl (fun_to_tgt stb) (fun ms => Any.pair ms.(initial_st) ms.(initial_mr)↑) ms.

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
      fnsems := [("main", (mk_specbody (mk_simple (fun (_: unit) => (ord_top, mainpre, fun _ => (⌜True⌝: iProp)%I))) mainbody))];
      initial_mr := ε;
      initial_st := tt↑;
    |}
  .

End SMODSEM.
End SModSem.



Module SMod.
Section SMOD.

  Context `{Σ: GRA.t}.

  Record t: Type := mk {
    get_modsem: Sk.t -> SModSem.t;
    sk: Sk.t;
  }
  .

  Definition transl (tr: Sk.t -> fspecbody -> ( Any.t -> itree Es Any.t)) (mst: SModSem.t -> Any.t) (md: t): Mod.t := {|
    Mod.get_modsem := fun sk => SModSem.transl (tr sk) mst (md.(get_modsem) sk);
    Mod.sk := md.(sk);
  |}
  .

  Definition to_src (md: t): Mod.t := transl (fun _ => fun_to_src ∘ fsb_body) SModSem.initial_st md.
  (* Definition to_mid (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid stb ∘ fsb_body) SModSem.initial_st md.
  Definition to_mid2 (stb: gname -> option fspec) (md: t): Mod.t := transl (fun _ => fun_to_mid2 ∘ fsb_body) SModSem.initial_st md. *)
  Definition to_tgt (stb: Sk.t -> gname -> option fspec) (md: t): Mod.t :=
    transl (fun sk => fun_to_tgt (stb sk)) (fun ms => Any.pair ms.(SModSem.initial_st) ms.(SModSem.initial_mr)↑) md.

    
  Definition get_stb (mds: list t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (flat_map (SModSem.fnsems ∘ (flip get_modsem sk)) mds).

  Definition get_sk (mds: list t): Sk.t :=
    Sk.sort (fold_right Sk.add Sk.unit (List.map sk mds)).

  Definition get_initial_mrs (mds: list t): Sk.t -> Σ :=
    fun sk => fold_left (⋅) (List.map (SModSem.initial_mr ∘ (flip get_modsem sk)) mds) ε.


  (* Definition get_stb (md: t): Sk.t -> alist gname fspec :=
    fun sk => map (map_snd fsb_fspec) (SModSem.fnsems (get_modsem md sk)).

  Definition get_sk (md: t): Sk.t :=
    Sk.sort (Sk.add Sk.unit (sk md)).

  Definition get_init_mr (md: t): Sk.t -> Σ :=
    fun sk => (SModSem.initial_mr (get_modsem md sk)).
 *)

    

  (* Definition transl (tr: SModSem.t -> ModSem.t) (md: t): Mod.t := {| *)
  (*   Mod.get_modsem := (SModSem.transl tr) ∘ md.(get_modsem); *)
  (*   Mod.sk := md.(sk); *)
  (* |} *)
  (* . *)

  (* Definition to_src (md: t): Mod.t := transl SModSem.to_src md. *)
  (* Definition to_mid (md: t): Mod.t := transl SModSem.to_mid md. *)
  (* Definition to_tgt (stb: list (gname * fspec)) (md: t): Mod.t := transl (SModSem.to_tgt stb) md. *)
  Lemma to_src_comm: forall sk smd,
      (SModSem.to_src) (get_modsem smd sk) = (to_src smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.
  (* Lemma to_mid_comm: forall sk stb smd,
      (SModSem.to_mid stb) (get_modsem smd sk) = (to_mid stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed. *)
  Lemma to_tgt_comm: forall sk stb smd,
      (SModSem.to_tgt (stb sk)) (get_modsem smd sk) = (to_tgt stb smd).(Mod.get_modsem) sk.
  Proof. refl. Qed.




  (* Definition l_bind A B (x: list A) (f: A -> list B): list B := List.flat_map f x. *)
  (* Definition l_ret A (a: A): list A := [a]. *)

  Declare Scope l_monad_scope.
  Local Open Scope l_monad_scope.
  Notation "'do' X <- A ; B" := (List.flat_map (fun X => B) A) : l_monad_scope.
  Notation "'do' ' X <- A ; B" := (List.flat_map (fun _x => match _x with | X => B end) A) : l_monad_scope.
  Notation "'ret'" := (fun X => [X]) (at level 60) : l_monad_scope.

  Lemma unconcat
        A (xs: list A)
    :
      List.concat (List.map (fun x => [x]) xs) = xs
  .
  Proof.
    induction xs; ii; ss. f_equal; ss.
  Qed.

  Lemma red_do_ret A B (xs: list A) (f: A -> B)
    :
      (do x <- xs; ret (f x)) = List.map f xs
  .
  Proof.
    rewrite flat_map_concat_map.
    erewrite <- List.map_map with (f:=f) (g:=ret).
    rewrite unconcat. ss.
  Qed.

  Lemma red_do_ret2 A0 A1 B (xs: list (A0 * A1)) (f: A0 -> A1 -> B)
    :
      (do '(x0, x1) <- xs; ret (f x0 x1)) = List.map (fun '(x0, x1) => f x0 x1) xs
  .
  Proof.
    induction xs; ss. rewrite IHxs. destruct a; ss.
  Qed.



  Local Opaque Mod.add_list.

  Lemma transl_sk
        tr0 mr0 mds
    :
      <<SK: Mod.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) = fold_right Sk.add Sk.unit (List.map sk mds)>>
  .
  Proof.
    induction mds; ss.
    destruct mds.
    - Local Transparent Mod.add_list. s. r. rewrite Sk.add_unit_r. Local Opaque Mod.add_list. refl. 
    - rewrite ModFacts.add_list_cons; ss. r. f_equal. ss.
  Qed.

  Lemma transl_sk_stable
        tr0 tr1 mr0 mr1 mds
    :
      Mod.sk (Mod.add_list (List.map (transl tr0 mr0) mds)) =
      Mod.sk (Mod.add_list (List.map (transl tr1 mr1) mds))
  .
  Proof. rewrite ! transl_sk. ss. Qed.

  Definition get_fnsems (sk: Sk.t) (md: t) (tr0: fspecbody -> Any.t -> itree Es Any.t) :=
    let ms := (get_modsem md sk) in
    (do '(fn, fsb) <- ms.(SModSem.fnsems);
      let fsem := tr0 fsb in
      ret (fn, fsem))
  .

  Fixpoint load_fnsems (sk: Sk.t) (mds: list t) (tr0: fspecbody -> Any.t -> itree Es Any.t) : list (string * (Any.t -> itree Es Any.t)):=
    match mds with
    | [] => nil
    | h::[] => get_fnsems sk h tr0
    | h::t => (List.map ModSem.trans_l (get_fnsems sk h tr0)) ++ (List.map ModSem.trans_r (load_fnsems sk t tr0))
    end.
    
  Let transl_fnsems_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSem.fnsems (Mod.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_fnsems sk mds (tr0 sk))
  .
  Proof.
    induction mds; ss.
    destruct mds.
    - Local Transparent Mod.add_list.
      ss. unfold get_fnsems.
      rewrite flat_map_concat_map.
      replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, (tr0 sk fsb))]) with
      (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, (tr0 sk fsb))));
      cycle 1.
      { apply func_ext. i. des_ifs. }
      erewrite <- List.map_map with (g:=ret).
      rewrite unconcat.
      apply map_ext. ii. des_ifs.
      Local Opaque Mod.add_list.
    - rewrite ModFacts.add_list_cons; ss.
      cbn. rewrite List.map_map. 
      unfold get_fnsems in *.
      rewrite ! flat_map_concat_map in *.
      replace (fun _x: string * fspecbody => let (fn, fsb) := _x in [(fn, (tr0 sk fsb))]) with
      (ret ∘ (fun _x: string * fspecbody => let (fn, fsb) := _x in (fn, (tr0 sk fsb)))) in *;
      cycle 1.
      { apply func_ext. i. des_ifs. }
      f_equal.
      { erewrite <- List.map_map with (g:=ret); rewrite unconcat.
        rewrite List.map_map. ss. }
      f_equal. ss.
Qed.

  Lemma transl_fnsems
        tr0 mr0 mds
    :
      (ModSem.fnsems (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_fnsems (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds (tr0 (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds)))))
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_fnsems_aux. do 2 f_equal.
    { rewrite transl_sk. ss. }
    rewrite transl_sk. auto.
  Qed.


  Lemma flat_map_assoc
        A B C
        (f: A -> list B)
        (g: B -> list C)
        (xs: list A)
    :
      (do y <- (do x <- xs; f x); g y) =
      (do x <- xs; do y <- (f x); g y)
  .
  Proof.
    induction xs; ii; ss.
    rewrite ! flat_map_concat_map in *. rewrite ! map_app. rewrite ! concat_app. f_equal; ss.
  Qed.

  Lemma transl_fnsems_stable
        tr0 tr1 mr0 mr1 mds
    :
      List.map fst (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds))).(ModSem.fnsems) =
      List.map fst (Mod.enclose (Mod.add_list (List.map (transl tr1 mr1) mds))).(ModSem.fnsems)
  .

  Proof.
    rewrite ! transl_fnsems.
    set (Sk.sort (foldr Sk.add Sk.unit (map sk mds))).
    clearbody a. revert a.
    induction mds; ss. i.
    unfold get_fnsems.
    destruct mds. 
    { 
      rewrite <- ! red_do_ret.
      rewrite ! flat_map_assoc. eapply flat_map_ext. i. des_ifs.
    }
    rewrite ! List.map_app.
    rewrite ! List.map_map.
    rewrite fun_fst_trans_l.
    rewrite fun_fst_trans_r.
    rewrite <- IHmds.
    f_equal.
    rewrite <- ! red_do_ret.
    rewrite ! flat_map_assoc. eapply flat_map_ext. i. des_ifs.
Qed.

  Fixpoint link_mrs mrs : Any.t :=
    match mrs with
    | [] => tt↑
    | h::[] => h
    | h::t => Any.pair h (link_mrs t)
    end.


  Definition load_initial_mrs (sk: Sk.t) (mds: list t) (mr0: SModSem.t -> Any.t): Any.t :=
    let mrs := (do md <- mds;
    let ms := (get_modsem md sk) in
    ret (mr0 ms)) in
    link_mrs mrs
    (* How to link initial states *)
  .

  Let transl_initial_mrs_aux
        tr0 mr0 mds
        (sk: Sk.t)
    :
      (ModSem.init_st (Mod.get_modsem (Mod.add_list (List.map (transl tr0 mr0) mds)) sk)) =
      (load_initial_mrs sk mds mr0)
  .
  Proof.
    induction mds; ii; ss.
    destruct mds; ss.
    rewrite ModFacts.add_list_cons; ss. cbn. f_equal; ss.
  Qed.

  Lemma transl_initial_mrs
        tr0 mr0 mds
    :
      (ModSem.init_st (Mod.enclose (Mod.add_list (List.map (transl tr0 mr0) mds)))) =
      (load_initial_mrs (Sk.sort (List.fold_right Sk.add Sk.unit (List.map sk mds))) mds mr0)
  .
  Proof.
    unfold Mod.enclose.
    rewrite transl_initial_mrs_aux. do 2 f_equal. rewrite transl_sk. ss.
  Qed.

            

  Definition main (mainpre: Any.t -> iProp) (mainbody: Any.t -> itree hEs Any.t): t := {|
    get_modsem := fun _ => (SModSem.main mainpre mainbody);
    sk := Sk.unit;
  |}
  .

End SMOD.
End SMod.















  Hint Resolve Ord.lt_le_lt Ord.le_lt_lt OrdArith.lt_add_r OrdArith.le_add_l
       OrdArith.le_add_r Ord.lt_le
       Ord.lt_S
       Ord.S_lt
       Ord.S_supremum
       Ord.S_pos
    : ord.
  Hint Resolve Ord.le_trans Ord.lt_trans: ord_trans.
  Hint Resolve OrdArith.add_base_l OrdArith.add_base_r: ord_proj.

  Global Opaque interp_Es.






  Require Import Red.

  Ltac interp_red := erewrite interp_vis ||
                              erewrite interp_ret ||
                              erewrite interp_tau ||
                              erewrite interp_trigger ||
                              erewrite interp_bind.

  (* TODO: remove it *)
  Ltac interp_red2 := rewrite interp_vis ||
                              rewrite interp_ret ||
                              rewrite interp_tau ||
                              rewrite interp_trigger ||
                              rewrite interp_bind.

  Ltac _red_itree f :=
    match goal with
    | [ |- ?itr >>= _ = _] =>
      match itr with
      | _ >>= _ =>
        instantiate (f:=_continue); apply bind_bind; fail
      | Tau _ =>
        instantiate (f:=_break); apply bind_tau; fail
      | Ret _ =>
        instantiate (f:=_continue); apply bind_ret_l; fail
      | _ =>
        fail
      end
    | _ => fail
    end.



Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_tgt_bind
      (R S: Type)
      (s : itree (hCallE +' hAAE +' sE +' eventE) R) (k : R -> itree (hCallE +' hAAE +' sE +' eventE) S)
      stb o ctx
  :
    (interp_Es'_tgt stb o (s >>= k)) ctx
    =
    st <- interp_Es'_tgt stb o s ctx;; interp_Es'_tgt stb o (k st.2) st.1.
Proof.
  unfold interp_Es'_tgt in *. eapply interp_state_bind.
Qed.

Lemma interp_tgt_tau stb o ctx
      (U: Type)
      (t : itree _ U)
  :
    (interp_Es'_tgt stb o (Tau t) ctx)
    =
    (Tau (interp_Es'_tgt stb o t ctx)).
Proof.
  unfold interp_Es'_tgt in *. eapply interp_state_tau.
Qed.

Lemma interp_tgt_ret stb o ctx
      (U: Type)
      (t: U)
  :
    (interp_Es'_tgt stb o (Ret t) ctx)
    =
    Ret (ctx, t).
Proof.
  unfold interp_Es'_tgt in *. eapply interp_state_ret.
Qed.

Lemma interp_tgt_triggerp stb o ctx
      (R: Type)
      (i: sE R)
  :
    (interp_Es'_tgt stb o (trigger i) ctx)
    =
    (handle_sE_tgt i >>= (fun r => tau;; Ret (ctx, r))).
Proof.
  unfold interp_Es'_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_triggere stb o ctx
      (R: Type)
      (i: eventE R)
  :
    (interp_Es'_tgt stb o (trigger i) ctx)
    =
    (trigger i >>= (fun r => tau;; Ret (ctx, r))).
Proof.
  unfold interp_Es'_tgt. rewrite interp_state_trigger. cbn. grind.
Qed.

Lemma interp_tgt_hcall stb o ctx
      (R: Type)
      (i: hCallE R)
  :
    (interp_Es'_tgt stb o (trigger i) ctx)
    =
    ((handle_hCallE_tgt stb o i ctx) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_Es'_tgt in *. rewrite interp_state_trigger. cbn. auto.
Qed.

Lemma interp_tgt_triggerUB stb o ctx
      (R: Type)
  :
    (interp_Es'_tgt stb o (triggerUB) ctx)
    =
    triggerUB (A:=Σ*R).
Proof.
  unfold interp_Es'_tgt, triggerUB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_triggerNB stb o ctx
      (R: Type)
  :
    (interp_Es'_tgt stb o (triggerNB) ctx)
    =
    triggerNB (A:=Σ*R).
Proof.
  unfold interp_Es'_tgt, triggerNB in *. rewrite unfold_interp_state. cbn. grind.
Qed.

Lemma interp_tgt_unwrapU stb o ctx
      (R: Type)
      (i: option R)
  :
    (interp_Es'_tgt stb o (@unwrapU (hCallE +' hAAE +' sE +' eventE) _ _ i) ctx)
    =
    r <- (unwrapU i);; Ret (ctx, r).
Proof.
  unfold interp_Es'_tgt, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_tgt_unwrapN stb o ctx
      (R: Type)
      (i: option R)
  :
    (interp_Es'_tgt stb o (@unwrapN (hCallE +' hAAE +' sE +' eventE) _ _ i) ctx)
    =
    r <- (unwrapN i);; Ret (ctx, r).
Proof.
  unfold interp_Es'_tgt, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_tgt_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_tgt_assume stb o ctx
      P
  :
    (interp_Es'_tgt stb o (assume P) ctx)
    =
    (assume P;;; tau;; Ret (ctx, tt))
.
Proof.
  unfold assume. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_guarantee stb o ctx
      P
  :
    (interp_Es'_tgt stb o (guarantee P) ctx)
    =
    (guarantee P;;; tau;; Ret (ctx, tt)).
Proof.
  unfold guarantee. rewrite interp_tgt_bind. rewrite interp_tgt_triggere. grind. eapply interp_tgt_ret.
Qed.

Lemma interp_tgt_ext stb o ctx
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_Es'_tgt stb o itr0 ctx)
    =
    (interp_Es'_tgt stb o itr1 ctx)
.
Proof. subst; et. Qed.

Global Program Instance interp_Es'_tgt_rdb: red_database (mk_box (@interp_Es'_tgt)) :=
  mk_rdb
    1
    (mk_box interp_tgt_bind)
    (mk_box interp_tgt_tau)
    (mk_box interp_tgt_ret)
    (mk_box interp_tgt_hcall)
    (mk_box interp_tgt_triggere)
    (mk_box interp_tgt_triggerp)
    (mk_box interp_tgt_triggerp)
    (mk_box interp_tgt_triggerUB)
    (mk_box interp_tgt_triggerNB)
    (mk_box interp_tgt_unwrapU)
    (mk_box interp_tgt_unwrapN)
    (mk_box interp_tgt_assume)
    (mk_box interp_tgt_guarantee)
    (mk_box interp_tgt_ext)
.

End AUX.



Section AUX.

Context `{Σ: GRA.t}.
Variable stb: gname -> option fspec.
(* itree reduction *)
(* Lemma interp_mid_bind
      (R S: Type)
      (s : itree (hCallE +' sE +' eventE) R) (k : R -> itree (hCallE +' sE +' eventE) S)
      o
  :
    (interp_hCallE_mid stb o (s >>= k))
    =
    ((interp_hCallE_mid stb o s) >>= (fun r => interp_hCallE_mid stb o (k r))).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_tau o
      (U: Type)
      (t : itree _ U)
  :
    (interp_hCallE_mid stb o (Tau t))
    =
    (Tau (interp_hCallE_mid stb o t)).
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_ret o
      (U: Type)
      (t: U)
  :
    ((interp_hCallE_mid stb o (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid in *. grind.
Qed.

Lemma interp_mid_triggerp o
      (R: Type)
      (i: sE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggere o
      (R: Type)
      (i: eventE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_hcall o
      (R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_mid stb o (trigger i))
    =
    ((handle_hCallE_mid stb o i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid_triggerUB o
      (R: Type)
  :
    (interp_hCallE_mid stb o (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_triggerNB o
      (R: Type)
  :
    (interp_hCallE_mid stb o (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid_unwrapU o
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapU (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hCallE_mid, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_mid_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_mid_unwrapN o
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid stb o (@unwrapN (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hCallE_mid, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_mid_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_mid_assume o
      P
  :
    (interp_hCallE_mid stb o (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_guarantee o
      P
  :
    (interp_hCallE_mid stb o (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid_bind. rewrite interp_mid_triggere. grind. eapply interp_mid_ret.
Qed.

Lemma interp_mid_ext o
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hCallE_mid stb o itr0)
    =
    (interp_hCallE_mid stb o itr1)
.
Proof. subst; et. Qed. *)

End AUX.


(* Global Program Instance interp_hCallE_mid_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hCallE_mid)) :=
  mk_rdb
    0
    (mk_box interp_mid_bind)
    (mk_box interp_mid_tau)
    (mk_box interp_mid_ret)
    (mk_box interp_mid_hcall)
    (mk_box interp_mid_triggere)
    (mk_box interp_mid_triggerp)
    (mk_box interp_mid_triggerp)
    (mk_box interp_mid_triggerUB)
    (mk_box interp_mid_triggerNB)
    (mk_box interp_mid_unwrapU)
    (mk_box interp_mid_unwrapN)
    (mk_box interp_mid_assume)
    (mk_box interp_mid_guarantee)
    (mk_box interp_mid_ext)
. *)

Section AUX.

Context `{Σ: GRA.t}.
Variable stb: gname -> option fspec.
(* itree reduction *)
(* Lemma interp_mid2_bind
      (R S: Type)
      (s : itree (hCallE +' sE +' eventE) R) (k : R -> itree (hCallE +' sE +' eventE) S)
  :
    (interp_hCallE_mid2 (s >>= k))
    =
    ((interp_hCallE_mid2 s) >>= (fun r => interp_hCallE_mid2 (k r))).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hCallE_mid2 (Tau t))
    =
    (Tau (interp_hCallE_mid2 t)).
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_ret
      (U: Type)
      (t: U)
  :
    ((interp_hCallE_mid2 (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hCallE_mid2 in *. grind.
Qed.

Lemma interp_mid2_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_hcall
      (R: Type)
      (i: hCallE R)
  :
    (interp_hCallE_mid2 (trigger i))
    =
    ((handle_hCallE_mid2 i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hCallE_mid2 in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_mid2_triggerUB
      (R: Type)
  :
    (interp_hCallE_mid2 (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_triggerNB
      (R: Type)
  :
    (interp_hCallE_mid2 (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hCallE_mid2, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_mid2_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapU (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hCallE_mid2, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_mid2_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid2_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_mid2_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hCallE_mid2 (@unwrapN (hCallE +' sE +' eventE) _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hCallE_mid2, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_mid2_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_mid2_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_mid2_assume
      P
  :
    (interp_hCallE_mid2 (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_guarantee
      P
  :
    (interp_hCallE_mid2 (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_mid2_bind. rewrite interp_mid2_triggere. grind. eapply interp_mid2_ret.
Qed.

Lemma interp_mid2_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hCallE_mid2 itr0)
    =
    (interp_hCallE_mid2 itr1)
.
Proof. subst; et. Qed. *)

End AUX.


(* Global Program Instance interp_hCallE_mid2_rdb `{Σ: GRA.t}: red_database (mk_box (@interp_hCallE_mid2)) :=
  mk_rdb
    0
    (mk_box interp_mid2_bind)
    (mk_box interp_mid2_tau)
    (mk_box interp_mid2_ret)
    (mk_box interp_mid2_hcall)
    (mk_box interp_mid2_triggere)
    (mk_box interp_mid2_triggerp)
    (mk_box interp_mid2_triggerp)
    (mk_box interp_mid2_triggerUB)
    (mk_box interp_mid2_triggerNB)
    (mk_box interp_mid2_unwrapU)
    (mk_box interp_mid2_unwrapN)
    (mk_box interp_mid2_assume)
    (mk_box interp_mid2_guarantee)
    (mk_box interp_mid2_ext)
. *)



Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_src_bind
      (R S: Type)
      (s : itree hEs R) (k : R -> itree hEs S)
  :
    (interp_hEs_src (s >>= k))
    =
    ((interp_hEs_src s) >>= (fun r => interp_hEs_src (k r))).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hEs_src (Tau t))
    =
    (Tau (interp_hEs_src t)).
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_ret
      (U: Type)
      (t: U)
  :
    ((interp_hEs_src (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hEs_src in *. grind.
Qed.

Lemma interp_src_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_call
      (R: Type)
      (i: callE R)
  :
    (interp_hEs_src (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_hapc
      (R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_src (trigger i))
    =
    ((handle_hAPCE_src i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_src in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_src_triggerUB
      (R: Type)
  :
    (interp_hEs_src (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_src, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_triggerNB
      (R: Type)
  :
    (interp_hEs_src (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_src, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_src_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapU hEs _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hEs_src, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_src_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hEs_src (@unwrapN hEs _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hEs_src, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_src_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_src_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_src_assume
      P
  :
    (interp_hEs_src (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_guarantee
      P
  :
    (interp_hEs_src (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_src_bind. rewrite interp_src_triggere. grind. eapply interp_src_ret.
Qed.

Lemma interp_src_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hEs_src itr0)
    =
    (interp_hEs_src itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_hEs_src_rdb: red_database (mk_box (@interp_hEs_src)) :=
  mk_rdb
    0
    (mk_box interp_src_bind)
    (mk_box interp_src_tau)
    (mk_box interp_src_ret)
    (mk_box interp_src_call)
    (mk_box interp_src_triggere)
    (mk_box interp_src_triggerp)
    (mk_box interp_src_hapc)
    (mk_box interp_src_triggerUB)
    (mk_box interp_src_triggerNB)
    (mk_box interp_src_unwrapU)
    (mk_box interp_src_unwrapN)
    (mk_box interp_src_assume)
    (mk_box interp_src_guarantee)
    (mk_box interp_src_ext)
.

End AUX.


Section AUX.

Context `{Σ: GRA.t}.
(* itree reduction *)
Lemma interp_hEs_tgt_bind
      (R S: Type)
      (s : itree hEs R) (k : R -> itree hEs S)
  :
    (interp_hEs_tgt (s >>= k))
    =
    ((interp_hEs_tgt s) >>= (fun r => interp_hEs_tgt (k r))).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_tau
      (U: Type)
      (t : itree _ U)
  :
    (interp_hEs_tgt (Tau t))
    =
    (Tau (interp_hEs_tgt t)).
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_ret
      (U: Type)
      (t: U)
  :
    ((interp_hEs_tgt (Ret t)))
    =
    Ret t.
Proof.
  unfold interp_hEs_tgt in *. grind.
Qed.

Lemma interp_hEs_tgt_triggerp
      (R: Type)
      (i: sE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggere
      (R: Type)
      (i: eventE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (trigger i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_call
      (R: Type)
      (i: callE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    (handle_callE_hEs i >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_hapc
      (R: Type)
      (i: hAPCE R)
  :
    (interp_hEs_tgt (trigger i))
    =
    ((handle_hAPCE_tgt i) >>= (fun r => tau;; Ret r)).
Proof.
  unfold interp_hEs_tgt in *.
  repeat rewrite interp_trigger. grind.
Qed.

Lemma interp_hEs_tgt_triggerUB
      (R: Type)
  :
    (interp_hEs_tgt (triggerUB))
    =
    triggerUB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerUB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_triggerNB
      (R: Type)
  :
    (interp_hEs_tgt (triggerNB))
    =
    triggerNB (A:=R).
Proof.
  unfold interp_hEs_tgt, triggerNB in *. rewrite unfold_interp. cbn. grind.
Qed.

Lemma interp_hEs_tgt_unwrapU
      (R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapU hEs _ _ i))
    =
    (unwrapU i).
Proof.
  unfold interp_hEs_tgt, unwrapU in *. des_ifs.
  { etrans.
    { eapply interp_hEs_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hEs_tgt_triggerUB. }
    { unfold triggerUB. grind. }
  }
Qed.

Lemma interp_hEs_tgt_unwrapN
      (R: Type)
      (i: option R)
  :
    (interp_hEs_tgt (@unwrapN hEs _ _ i))
    =
    (unwrapN i).
Proof.
  unfold interp_hEs_tgt, unwrapN in *. des_ifs.
  { etrans.
    { eapply interp_hEs_tgt_ret. }
    { grind. }
  }
  { etrans.
    { eapply interp_hEs_tgt_triggerNB. }
    { unfold triggerNB. grind. }
  }
Qed.

Lemma interp_hEs_tgt_assume
      P
  :
    (interp_hEs_tgt (assume P))
    =
    (assume P;;; tau;; Ret tt)
.
Proof.
  unfold assume. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_guarantee
      P
  :
    (interp_hEs_tgt (guarantee P))
    =
    (guarantee P;;; tau;; Ret tt).
Proof.
  unfold guarantee. rewrite interp_hEs_tgt_bind. rewrite interp_hEs_tgt_triggere. grind. eapply interp_hEs_tgt_ret.
Qed.

Lemma interp_hEs_tgt_ext
      R (itr0 itr1: itree _ R)
      (EQ: itr0 = itr1)
  :
    (interp_hEs_tgt itr0)
    =
    (interp_hEs_tgt itr1)
.
Proof. subst; et. Qed.

Global Program Instance interp_hEs_tgt_rdb: red_database (mk_box (@interp_hEs_tgt)) :=
  mk_rdb
    0
    (mk_box interp_hEs_tgt_bind)
    (mk_box interp_hEs_tgt_tau)
    (mk_box interp_hEs_tgt_ret)
    (mk_box interp_hEs_tgt_call)
    (mk_box interp_hEs_tgt_triggere)
    (mk_box interp_hEs_tgt_triggerp)
    (mk_box interp_hEs_tgt_hapc)
    (mk_box interp_hEs_tgt_triggerUB)
    (mk_box interp_hEs_tgt_triggerNB)
    (mk_box interp_hEs_tgt_unwrapU)
    (mk_box interp_hEs_tgt_unwrapN)
    (mk_box interp_hEs_tgt_assume)
    (mk_box interp_hEs_tgt_guarantee)
    (mk_box interp_hEs_tgt_ext)
.

End AUX.



(*** TODO: move to ITreeLib ***)
Lemma bind_eta E X Y itr0 itr1 (ktr: ktree E X Y): itr0 = itr1 -> itr0 >>= ktr = itr1 >>= ktr. i; subst; refl. Qed.

Ltac ired_l := try (prw _red_gen 2 0).
Ltac ired_r := try (prw _red_gen 1 0).

Ltac ired_both := ired_l; ired_r.

  Ltac mred := repeat (cbn; ired_both).
  Ltac Esred :=
            try rewrite ! interp_Es_sE;
            try rewrite ! interp_Es_eventE; try rewrite ! interp_Es_callE;
            try rewrite ! interp_Es_triggerNB; try rewrite ! interp_Es_triggerUB (*** igo ***).
  (*** step and some post-processing ***)
  Ltac _step :=
    match goal with
    (*** terminal cases ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerUB >>= _) _ ] =>
      unfold triggerUB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerNB >>= _) ] =>
      unfold triggerNB; mred; _step; ss; fail
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (triggerNB >>= _) _ ] =>
      exfalso
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (triggerUB >>= _) ] =>
      exfalso

    (*** assume/guarantee ***)
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (assume ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) _ ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (assume ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (assume P) as tvar eqn:thyp; unfold assume in thyp; subst tvar
    | [ |- gpaco6 _ _ _ _ _ _ _ _ _ (guarantee ?P ;;; _) ] =>
      let tvar := fresh "tmp" in
      let thyp := fresh "TMP" in
      remember (guarantee P) as tvar eqn:thyp; unfold guarantee in thyp; subst tvar

    (*** default cases ***)
    | _ =>
      (gstep; econs; eauto; try (by eapply OrdArith.lt_from_nat; ss);
       (*** some post-processing ***)
       i;
       try match goal with
           | [ |- (eq ==> _)%signature _ _ ] =>
             let v_src := fresh "v_src" in
             let v_tgt := fresh "v_tgt" in
             intros v_src v_tgt ?; subst v_tgt
           end)
    end
  .
  Ltac steps := repeat (mred; try _step; des_ifs_safe).
  Ltac seal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_src
    end.
  Ltac seal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src ?i_tgt ] => seal i_tgt
    end.
  Ltac unseal_left :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ (@Seal.sealing _ _ ?i_src) ?i_tgt ] => unseal i_src
    end.
  Ltac unseal_right :=
    match goal with
    | [ |- gpaco6 _ _ _ _ _ _ _ _ ?i_src (@Seal.sealing _ _ ?i_tgt) ] => unseal i_tgt
    end.
  Ltac force_l := seal_right; _step; unseal_right.
  Ltac force_r := seal_left; _step; unseal_left.
  (* Ltac mstep := gstep; econs; eauto; [eapply from_nat_lt; ss|]. *)

  From ExtLib Require Import
       Data.Map.FMapAList.

  Hint Resolve cpn3_wcompat: paco.
  Ltac init :=
    split; ss; ii; clarify; rename y into varg; eexists 100%nat; ss; des; clarify;
    ginit; []; unfold alist_add, alist_remove; ss;
    unfold fun_to_tgt, cfunN; ss.


Notation Es' := (hCallE +' sE +' eventE).
*)

Module IPCNotations.
  Notation ";;; t2" :=
    (ITree.bind (trigger hAPC) (fun _ => t2))
      (at level 63, t2 at next level, right associativity) : itree_scope.
  Notation "` x : t <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x : t => ;;; t2))
      (at level 62, t at next level, t1 at next level, x ident, right associativity) : itree_scope.
  Notation "x <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x => ;;; t2))
      (at level 62, t1 at next level, right associativity) : itree_scope.
  Notation "' p <- t1 ;;; t2" :=
    (ITree.bind t1 (fun x_ => match x_ with p => ;;; t2 end))
      (at level 62, t1 at next level, p pattern, right associativity) : itree_scope.
End IPCNotations.

Export IPCNotations. 
