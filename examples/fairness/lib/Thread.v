Require Import sflib.
Require Import Program.
Require Export ITreelib WFLibLarge NatStructsLarge Any FairCounter.

Module TIdSet := NatSet.

Section TID.

  Definition tid_dec := PeanoNat.Nat.eq_dec.

  Lemma reldec_correct_tid_dec: RelDec.RelDec_Correct (RelDec.RelDec_from_dec eq tid_dec).
  Proof. eapply RelDec.RelDec_Correct_eq_typ. Qed.

  Definition tid_dec_bool :=
    fun t1 t2 => if (tid_dec t1 t2) then true else false.


  Definition sum_tid (_id: ID) := id_sum thread_id _id.

  Definition tids_fmap (tid: thread_id) (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (PeanoNat.Nat.eq_dec t tid) then Flag.success
          else if (NatMapP.F.In_dec tidf t) then Flag.fail
               else Flag.emp.

  Definition tids_fmap_all (tidf: TIdSet.t): @fmap thread_id :=
    fun t => if (NatMapP.F.In_dec tidf t) then Flag.fail
             else Flag.emp.

  Lemma tids_fmap_rm_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.remove tid tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.remove_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.remove_neq_in_iff; eauto.
  Qed.

  Lemma tids_fmap_add_same_eq
        tid tset
    :
    tids_fmap tid tset = tids_fmap tid (NatMap.add tid () tset).
  Proof.
    extensionality t. unfold tids_fmap. des_ifs.
    - exfalso. apply n0; clear n0. rewrite NatMapP.F.add_neq_in_iff; eauto.
    - exfalso. apply n0; clear n0. rewrite <- NatMapP.F.add_neq_in_iff; eauto.
  Qed.

  Definition kernel_tid: thread_id := 0.

  Definition kernel_success_fmap: @fmap thread_id :=
    fun t => if (tid_dec t kernel_tid)
             then Flag.success else Flag.emp.

  Definition initial_threads := TIdSet.add kernel_tid NatSet.empty.
End TID.