Require Import Coqlib.
Require Import ITreelib.
Require Import ImpPrelude.
Require Import STS.
Require Import Behavior.
Require Import ModSem.
Require Import Skeleton.
Require Import IntroHeader.

Set Implicit Arguments.


(***
F.f(n) {
  if (n < 0) {
    r := -1
  } else if (n == 0) {
    r := ...
  } else {
    r := 5 * Ncall P Q G.g(n)
  }
  r
}
***)

Section PROOF.

  Definition fF: list val -> itree Es val :=
    fun varg =>
      `n: Z <- (pargs [Tint] varg)?;;
      assume (intrange_64 n);;;
      if (n <? 0)%Z
      then `_: val <- ccallU "log" [Vint n];; Ret (Vint (- 1))
      else if (n =? 0)%Z
           then Ret (Vint 0)
           else r <- (Ncall True (fun r => r = Vint (5 * n - 2)) "g" [Vint n]);;
                res <- (vadd (Vint 2) r)?;;
                Ret res
  .

  (* Definition Ncall {X Y} (f: string) (x: X): itree Es Y := *)
  (*   `b: bool <- trigger (Choose bool);; *)
  (*   if b then ccallU f x else trigger (Choose _) *)
  (* . *)

  (* Definition fF: list val -> itree Es val := *)
  (*   fun varg => *)
  (*     `n: Z <- (pargs [Tint] varg)?;; *)
  (*     assume (intrange_64 n);;; *)
  (*     assume ((Z.to_nat n) < max);;; *)
  (*     if (n <? 0)%Z *)
  (*     then `_: val <- ccallU "log" [Vint n];; Ret (Vint (- 1)) *)
  (*     else if (n =? 0)%Z *)
  (*          then Ret (Vint 0) *)
  (*          else (Ncall "g" [Vint n]) *)
  (* . *)

  Definition FSem: ModSem.t := {|
    ModSem.fnsems := [("f", cfunU fF)];
    ModSem.init_st := tt↑;
  |}
  .

  Definition F: Mod.t := {|
    Mod.get_modsem := fun _ => FSem;
    Mod.sk := [("f", Gfun↑)];
  |}
  .

End PROOF.
