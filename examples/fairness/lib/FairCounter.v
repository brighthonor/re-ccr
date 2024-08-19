Require Import String.
Require Import ITreelib.
Require Import WFLibLarge.
Require Import sflib.
From Coq Require Import Classes.RelationClasses Program.

Module Flag.

  Variant t: Type :=
  | fail
  | emp
  | success
  .

  Definition le: t -> t -> Prop :=
    fun f0 f1 =>
      match f0, f1 with
      | fail, _ => True
      | _, fail => False
      | emp, _ => True
      | _, emp => False
      | success, _ => True
      end.

  Global Program Instance le_PreOrder: PreOrder le.
  Next Obligation.
    ii. destruct x; ss.
  Qed.
  Next Obligation.
    ii. destruct x, y, z; ss.
  Qed.

End Flag.

Notation ID := (Type) (only parsing).
Notation id_prod A B := (prod A B) (only parsing).
Notation id_sum A B := (sum A B) (only parsing).

Notation fname := string (only parsing).
Notation thread_id := nat (only parsing).

Section Fcnt.

  Variable (id: ID).
  Variable (wf: WF).

  Definition ffmap := id -> Flag.t.

  Definition iimap := id -> wf.(T).

  Definition soft_update (m0 m1: iimap): Prop :=
    forall i, wf.(le) (m1 i) (m0 i).

  Global Program Instance soft_update_Reflexive: Reflexive soft_update.
  Next Obligation.
    ii. reflexivity.
  Qed.

  Definition fair_update (m0 m1: iimap) (f: ffmap): Prop :=
    forall i, match f i with
          | Flag.fail => wf.(lt) (m1 i) (m0 i)
          | Flag.emp => (m1 i) = (m0 i)
          | Flag.success => True
          end.

End Fcnt.


From Ordinal Require Import Ordinal Hessenberg ClassicalOrdinal.
Definition owf: WF := mk_wf Ord.lt_well_founded.

Definition nat_wf: WF := mk_wf Wf_nat.lt_wf.

Require Import HoareDef IPM PCM.
Definition Fair {Σ: GRA.t} {id: ID} {wf: WF} :=
  fun (f: ffmap id) (im: iimap id wf) (nim: iimap id wf) =>
  Guarantee(⌜fair_update id wf im nim f⌝).