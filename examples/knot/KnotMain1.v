Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef.
Require Import ProofMode.
Require Import KnotHeader.
Require Import Invariant.
Require Import STB.

Set Implicit Arguments.




Fixpoint Fib (n: nat): nat :=
  match n with
  | 0 => 1
  | S n' =>
    let r := Fib n' in
    match n' with
    | 0 => 1
    | S n'' => r + Fib n''
    end
  end.

Section MAIN.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG invRA Σ}.
  Context `{@GRA.inG knotRA Σ}.

  Variable RecStb: Sk.t -> gname -> option fspec.
  Variable GlobalStb: Sk.t -> gname -> option fspec.

  Section SKENV.
    Variable sk: Sk.t.

    Definition fib_spec: fspec :=
      mk_simple (X:=nat*iProp)
                (fun '(n, INV) => (
                     (ord_pure (2 * n)),
                     (fun varg =>
                        ((⌜exists fb,
                               varg = [Vptr fb 0; Vint (Z.of_nat n)]↑ /\ (intrange_64 n) /\
                               fb_has_spec (Sk.load_skenv sk) (RecStb sk) fb (mrec_spec Fib INV)⌝)
                           ** INV)%I),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (Fib n)))↑⌝)
                          ** INV)
                )).

    Definition MainFunStb: list (gname * fspec) := [("fib", fib_spec)].

    Definition main_spec:    fspec :=
      mk_simple (X:=(nat -> nat))
                (fun f => (
                     (ord_top),
                     (fun varg =>
                        (⌜varg = ([]: list val)↑⌝)
                          ** OwnM (knot_init)
                          ** inv_closed: iProp
                     ),
                     (fun vret =>
                        (⌜vret = (Vint (Z.of_nat (Fib 10)))↑⌝: iProp)%I)
                )).

    Definition MainStb: list (gname * fspec) := [("fib", fib_spec); ("main", main_spec)].

    Definition MainSbtb: list (gname * fspecbody) :=[("fib", mk_specbody fib_spec (fun _ => trigger (Choose _)));
                                                    ("main", mk_specbody main_spec (fun _ => ;;; Ret (Vint (Z.of_nat (Fib 10)))↑))].

    Definition SMainSem: SModSem.t := {|
      SModSem.fnsems := MainSbtb;
      SModSem.initial_mr := ε;
      SModSem.initial_st := tt↑;
    |}
    .
  End SKENV.

  Definition SMain: SMod.t := {|
    SMod.get_modsem := SMainSem;
    SMod.sk := [("fib", Gfun↑)];
  |}
  .

  Definition Main: Mod.t := (SMod.to_tgt GlobalStb) SMain.

End MAIN.
