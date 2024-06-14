Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import MapHeader.
Require Import PCM.
Require Import HoareDef STB IPM.


Require Import sProp sWorld World SRF.
From stdpp Require Import coPset gmap namespaces.

Set Implicit Arguments.


(*** module I Map
private data := NULL

def init(sz: int) ≡
  data := calloc(sz)

def get(k: int): int ≡
  return *(data + k)

def set(k: int, v: int) ≡
  *(data + k) := v

def set_by_user(k: int) ≡
  set(k, input())
***)

Section I.
  Local Open Scope string_scope.
  Context `{_W: CtxWD.t}.
  Context `{@GRA.inG MapRA0 Γ}.
  (* Context `{@GRA.inG MapRA1 Σ}. *)
  Definition initF: list val -> itree hAGEs val :=
    fun varg =>
      `sz: Z <- (pargs [Tint] varg)?;;
      `r: val <- ccallU "alloc" [Vint sz];;
      pput r;;;
      _ <- (ITree.iter
              (fun i =>
                 if (Z_lt_le_dec i sz)
                 then
                   vptr <- (vadd r (Vint (i * 8)))?;;
                   `r: val <- ccallU "store" [vptr; Vint 0];;
                   Ret (inl (i + 1)%Z)
                 else
                   Ret (inr tt)) 0%Z);;
      Ret Vundef
  .

  Definition getF: list val -> itree hAGEs val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      data <- trigger sGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      `r: val <- ccallU "load" [vptr];; r <- (unint r)?;;
      Ret (Vint r)
  .

  Definition setF: list val -> itree hAGEs val :=
    fun varg =>
      '(k, v) <- (pargs [Tint; Tint] varg)?;;
      data <- trigger sGet;; data <- data↓?;; vptr <- (vadd data (Vint (k * 8)))?;;
      `_: val <- ccallU "store" [vptr; Vint v];;
      Ret Vundef
  .

  Definition set_by_userF: list val -> itree hAGEs val :=
    fun varg =>
      k <- (pargs [Tint] varg)?;;
      v <- trigger (Syscall "input" (([]: list Z)↑) (fun _ => True));; v <- v↓?;;
      ccallU "set" [Vint k; Vint v]
  .

  Definition MapSem: HModSem.t := {|
    HModSem.fnsems := [("init", cfunU initF); ("get", cfunU getF); ("set", cfunU setF); ("set_by_user", cfunU set_by_userF)];
    HModSem.initial_st := Ret Vnullptr↑;
    HModSem.initial_cond := ⌜True⌝%I
  |}
  .

  Definition Map: HMod.t := {|
    HMod.get_modsem := fun _ => MapSem;
    HMod.sk := [("init", Gfun↑); ("get", Gfun↑); ("set", Gfun↑); ("set_by_user", Gfun↑)];
  |}
  .

  (* Definition HMap : HMod.t := HMod.lift Map. *)

End I.
