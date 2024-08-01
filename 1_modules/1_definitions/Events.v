Require Import Coqlib.
Require Export sflib.
Require Export ITreelib.
Require Export AList.
Require Import Any.
Require Export BasicEvents.
Require Import IRed.

From Ordinal Require Export Ordinal Arithmetic Inaccessible.

Set Implicit Arguments.

Section ORD.
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
    end.

  Definition ord_eval (tbr: bool) (o: ord): Prop :=
    match tbr with
    | true => is_pure o
    | false => o = ord_top
    end.

End ORD.

Section FSPEC.
  Context `{Σ: GRA.t}.

  Record fspec: Type := mk_fspec {
    meta: Type;
    measure: meta -> ord;
    precond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical arg -> current logical arg -> resource arg -> Prop ***)
    postcond: meta -> Any.t -> Any_tgt -> iProp; (*** meta-variable -> new logical ret -> current logical ret -> resource ret -> Prop ***)
  }.

  Definition mk (X AA AR: Type) (measure: X -> ord) (precond: X -> AA -> Any_tgt -> iProp) (postcond: X -> AR -> Any_tgt -> iProp) :=
    @mk_fspec
      X
      measure
      (fun x arg_src arg_tgt => (∃ (aa: AA), ⌜arg_src = aa↑⌝ ∗ precond x aa arg_tgt)%I)
      (fun x ret_src ret_tgt => (∃ (ar: AR), ⌜ret_src = ar↑⌝ ∗ postcond x ar ret_tgt)%I).


  Definition fspec_trivial: fspec :=
    mk_fspec (meta:=unit) (fun _ => ord_top) (fun _ argh argl => (⌜argh = argl⌝: iProp)%I)
             (fun _ reth retl => (⌜reth = retl⌝: iProp)%I).
             
End FSPEC.

Section HOARE.
  Context `{Σ: GRA.t}.

  Variant hAPCE: Type -> Type :=
  | hAPC: hAPCE unit.

  Variant hAGE: Type -> Type :=
  | Assume (P: iProp): hAGE unit
  | Guarantee (P: iProp): hAGE unit.

  Definition hEs := (hAGE +' hAPCE +' Es).
  Definition hAGEs := (hAGE +' Es).

  Section APC.
    Definition HoareCall (tbr: bool) (ord_cur: ord) (fsp: fspec): gname -> Any.t -> (itree hAGEs) Any.t 
      := 
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

        Ret vret_src.  

    Program Fixpoint _APC (at_most: Ord.t) {wf Ord.lt at_most} : ord -> itree hAGEs unit :=
      fun ord_cur => 
        break <- trigger (Choose _);;
        if break: bool then Ret tt
        else
          n <- trigger (Choose Ord.t);;
          trigger (Choose (n < at_most)%ord);;;
          '(fn, varg) <- trigger (Choose _);;
          fsp <- (stb fn)ǃ;;
          _ <- HoareCall true ord_cur fsp fn varg;;
          (_APC n) _ ord_cur.
    Next Obligation. i. auto. Qed.
    Next Obligation. eapply Ord.lt_well_founded. Qed.

    Definition HoareAPC (ord_cur: ord): itree hAGEs unit :=
      at_most <- trigger (Choose _);;
      _APC at_most ord_cur.

    Lemma unfold_APC: forall at_most ord_cur, 
      _APC at_most ord_cur 
      = 
      break <- trigger (Choose _);;
      if break: bool then Ret tt
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

  End APC.

  Section INTERP.
    Definition handle_hAPCE_hAGEs (ord_cur: ord): hAPCE ~> itree hAGEs :=
      fun _ '(hAPC) => HoareAPC ord_cur.

    Definition handle_callE_hAGEs ord_cur: callE ~> itree hAGEs :=
      fun _ '(Call fn arg) => 
          fsp <- (stb fn)ǃ;;
          HoareCall false ord_cur fsp fn arg.

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

      Ret vret_tgt.

    Definition interp_sb_hp (sb: fspecbody): (Any_tgt -> itree hAGEs Any_tgt) :=
      let fs: fspec := sb.(fsb_fspec) in
      (HoareFun (fs.(measure)) (fs.(precond)) (fs.(postcond)) (sb.(fsb_body))).



  End INTERP.



End HOARE.

Section INTERP.

End INTERP.

