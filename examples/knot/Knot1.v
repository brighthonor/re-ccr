Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import Mem1.
Require Import ProofMode.
Require Import KnotHeader.
Require Import Invariant.
Require Import STB.

Set Implicit Arguments.



Section KNOT.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG memRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: Sk.t -> gname -> option fspec.
  Variable FunStb: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Variable sk: Sk.t.

    Definition rec_spec:    fspec :=
      mk_fspec_inv
        (mk_simple (X:=(nat -> nat) * nat)
                   (fun '(f, n) => (
                        (ord_pure (2 * n + 1)%nat),
                        (fun varg =>
                           (⌜varg = [Vint (Z.of_nat n)]↑ /\ (intrange_64 n)⌝)
                             ** (OwnM (knot_frag (Some f)))
                        ),
                        (fun vret =>
                           (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                             ** (OwnM (knot_frag (Some f)))
                        )
                   ))).

    Definition fun_gen (f: nat -> nat): fspec :=
      mk_fspec_inv
        (mk_simple (X:=nat)
                   (fun n => (
                        (ord_pure (2 * n)%nat),
                        (fun varg =>
                           (⌜exists fb,
                                 varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ (intrange_64 n) /\
                                 fb_has_spec (Sk.load_skenv sk) (RecStb sk) fb rec_spec⌝)
                             ** OwnM (knot_frag (Some f))
                        ),
                        (fun vret =>
                           (⌜vret = (Vint (Z.of_nat (f n)))↑⌝)
                             ** OwnM (knot_frag (Some f))
                        )
                   ))).

    Definition KnotRecStb: list (gname * fspec) := [("rec", rec_spec)].

    Definition knot_spec:    fspec :=
      mk_fspec_inv
        (mk_simple (X:=(nat -> nat))
                   (fun f => (
                        (ord_pure 1%nat),
                        (fun varg =>
                           (⌜exists fb,
                                 varg = [Vptr fb 0]↑ /\
                                 fb_has_spec (Sk.load_skenv sk) (FunStb sk) fb (fun_gen f)⌝)
                             ** (∃ old, OwnM (knot_frag old))
                        ),
                        (fun vret =>
                           (⌜exists fb,
                                 vret = (Vptr fb 0)↑ /\
                                 fb_has_spec (Sk.load_skenv sk) (RecStb sk) fb rec_spec⌝)
                             ** OwnM (knot_frag (Some f))
                        )
                   ))).

    Definition knot_spec2:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (ord_pure 1%nat),
                     (fun varg =>
                        (⌜exists fb,
                              varg = [Vptr fb 0]↑ /\
                              fb_has_spec (Sk.load_skenv sk) (FunStb sk) fb (fun_gen f)⌝)
                          ** OwnM (knot_init)
                          ** inv_closed
                     ),
                     (fun vret =>
                        (∃ INV,
                            (⌜exists fb,
                                  vret = (Vptr fb 0)↑ /\
                                  fb_has_spec (Sk.load_skenv sk) (RecStb sk) fb (mrec_spec f INV)⌝)
                              ** INV)%I
                     )
                )).

    Definition KnotStb: list (gname * fspec) := [("rec", rec_spec); ("knot", knot_spec)].

    Definition KnotSbtb: list (gname * fspecbody) :=[("rec", mk_specbody rec_spec (fun _ => trigger (Choose _)));
                                                    ("knot", mk_specbody knot_spec (fun _ => trigger (Choose _)))].

    Definition SKnotSem: SModSem.t := {|
      SModSem.fnsems := KnotSbtb;
      SModSem.initial_mr := (GRA.embed (var_points_to (Sk.load_skenv sk) "_f" (Vint 0))) ⋅ (GRA.embed (knot_full None)) ;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SKnot: SMod.t := {|
    SMod.get_modsem := SKnotSem;
    SMod.sk := [("rec", Gfun↑); ("knot", Gfun↑); ("_f", (Gvar 0)↑)];
  |}
  .

  Definition Knot: Mod.t := (SMod.to_tgt GlobalStb) SKnot.
End KNOT.


Section WEAK.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Lemma rec_spec_weaker f: fspec_weaker (mrec_spec f (OwnM (knot_frag (Some f)) ** inv_closed)) rec_spec.
  Proof.
    ii. ss. exists (f, x_src). esplits; ss; et.
    { refl. }
    { intros arg_src arg_tgt. ss.
      iIntros "H". iDestruct "H" as "[[% [H0 H1]] %]".
      iModIntro. iFrame. et. }
    { intros ret_src ret_tgt. ss.
      iIntros "H". iDestruct "H" as "[H0 [[% H2] %]]".
      iModIntro. iFrame. et. }
  Qed.
End WEAK.

Section WEAK.
  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: Sk.t -> gname -> option fspec.
  Variable FunStb: Sk.t -> gname -> option fspec.

  Lemma knot_spec2_weaker sk: fspec_weaker (knot_spec2 RecStb FunStb sk) (knot_spec RecStb FunStb sk).
  Proof.
    ii. ss. exists x_src. esplits; ss; et.
    { refl. }
    { intros arg_src arg_tgt.
      iIntros "H". iDestruct "H" as "[[[% H0] H1] %]".
      des. subst. iModIntro. iSplitL "H1"; ss. iSplitL; ss; et. iSplitR; et.
    }
    { intros ret_src ret_tgt.
      iIntros "H". iDestruct "H" as "[H0 [[% H1] %]]".
      des. subst.
      iModIntro. iSplitL; ss.
      iExists (OwnM (knot_frag (Some x_src)) ** inv_closed).
      iFrame. iPureIntro. des. eexists.
      split; eauto. eapply fb_has_spec_weaker; eauto.
      eapply rec_spec_weaker.
    }
  Qed.
End WEAK.
