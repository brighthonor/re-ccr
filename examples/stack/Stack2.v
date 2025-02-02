Require Import Coqlib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import PCM.
Require Import HoareDef OpenDef.
Require Import ProofMode.
Require Import Mem1.
Require Import AList.

Set Implicit Arguments.



Section PROOF.

  Context `{Σ: GRA.t}.
  Context `{@GRA.inG memRA Σ}.

  Notation sget := (p0 <- trigger sGet;; `p0: (gmap mblock (list val)) <- p0↓ǃ;; Ret p0) (only parsing).
  Notation sput p0 := (trigger (sPut p0↑)) (only parsing).

  (* def new(): Ptr *)
  (*   let handle := Choose(Ptr); *)
  (*   guarantee(stk_mgr(handle) = None); *)
  (*   stk_mgr(handle) := Some []; *)
  (*   return handle *)

  Definition new_body: list val -> itree Es val :=
    fun args =>
      _ <- (pargs [] args)?;;
      handle <- trigger (Choose _);;
      stk_mgr0 <- sget;;
      guarantee(stk_mgr0 !! handle = None);;;
      let stk_mgr1 := <[handle:=[]]> stk_mgr0 in
      sput stk_mgr1;;;
      Ret (Vptr handle 0)
  .

  (* def pop(handle: Ptr): Int64 *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   match stk with *)
  (*   | x :: stk' =>  *)
  (*     stk_mgr(handle) := Some stk'; *)
  (*     return x *)
  (*   | [] => return -1 *)
  (*   end *)

  Definition pop_body: list val -> itree Es val :=
    fun args =>
      handle <- (pargs [Tblk] args)?;;
      stk_mgr0 <- sget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      match stk0 with
      | x :: stk1 =>
        sput (<[handle:=stk1]> stk_mgr0);;;
        Ret x
      | _ => Ret (Vint (- 1))
      end
  .

  (* def push(handle: Ptr, x: Int64): Unit *)
  (*   let stk := unwrap(stk_mgr(handle)); *)
  (*   stk_mgr(handle) := Some (x :: stk); *)
  (*   () *)

  Definition push_body: list val -> itree Es val :=
    fun args =>
      '(handle, x) <- (pargs [Tblk; Tuntyped] args)?;;
      stk_mgr0 <- sget;;
      stk0 <- (stk_mgr0 !! handle)?;;
      sput (<[handle:=(x :: stk0)]> stk_mgr0);;;
      Ret Vundef
  .

  Definition StackSem: ModSem.t := {|
    ModSem.fnsems := [("new", cfunU new_body); ("pop", cfunU pop_body); ("push", cfunU push_body)];
    ModSem.init_st := (∅: gmap mblock (list val))↑;
  |}
  .

  Definition Stack: Mod.t := {|
    Mod.get_modsem := fun _ => StackSem;
    Mod.sk := [("new", Gfun↑); ("pop", Gfun↑); ("push", Gfun↑)];
  |}
  .

End PROOF.
