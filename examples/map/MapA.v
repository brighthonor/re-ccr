Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef STB IPM.
Require Import MapHeader.

Require Import sProp sWorld World SRF.

Set Implicit Arguments.


(*** module A Map
private map := (fun k => 0)

def init(sz: int) ≡
  skip

def get(k: int): int ≡
  return map[k]

def set(k: int, v: int) ≡
  map := map[k ← v]

def set_by_user(k: int) ≡
  set(k, input())
***)

Section A.
  Context `{_W: CtxWD.t}.
  Context `{@GRA.inG MapRA Γ}.
  Context `{@GRA.inG MapRA0 Γ}.

  (* Let Es := (hAPCE +' Es). *)

  Definition initF: list val -> itree hEs val :=
    fun varg =>
      ;;;
      Ret Vundef
  .

  Definition setF: list val -> itree hEs val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      f <- pget;;
      _ <- pput (fun n => if Z.eq_dec n k then v else f n);;;
      Ret Vundef
  .

  Definition getF: list val -> itree hEs val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      f <- pget;;;
      Ret (Vint (f k))
  .

  Definition set_by_userF: list val -> itree hEs val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (Syscall "input" (([]: list Z)↑) (fun _ => True));; v <- v↓?;;
      ccallU "set" [Vint k; Vint v]
  .

  Definition MapSbtb: list (string * fspecbody) :=
    [("init", mk_specbody init_spec (cfunU initF));
     ("get", mk_specbody get_spec (cfunU getF));
     ("set", mk_specbody set_spec (cfunU setF));
     ("set_by_user", mk_specbody set_by_user_spec (cfunU set_by_userF))].

  Definition SMapSem: SModSem.t := {|
    SModSem.fnsems := MapSbtb;
    SModSem.initial_cond := OwnM (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra));
    (* SModSem.initial_mr := GRA.embed (Excl.unit, Auth.excl ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra) ((fun _ => Excl.just 0%Z): @URA.car (Z ==> (Excl.t Z))%ra)); *)
    SModSem.initial_st := Ret (fun (_: Z) => 0%Z)↑;
  |}
  .

  Definition SMap: SMod.t := {|
    SMod.get_modsem := fun _ => SMapSem;
    SMod.sk := [("init", Gfun↑); ("get", Gfun↑); ("set", Gfun↑); ("set_by_user", Gfun↑)];
  |}
  .

  Variable GlobalStb: Sk.t -> gname -> option fspec.
  Definition HMap: HMod.t := (SMod.to_hmod GlobalStb SMap).
  (* Definition Map: Mod.t := (SMod.to_tgt GlobalStb SMap). *)
End A.
