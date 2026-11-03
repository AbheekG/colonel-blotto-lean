import Blotto.GeneralPaperRetainedDPStorage
import Blotto.GeneralPaperCatalogueOuterTrajectory

/-! Payload bits of the actual recorded closed-code rows. This observer
counts stored coordinates; descriptors/references, live chunks and all other
workspaces remain separate in the simultaneous-storage join. -/
namespace Blotto.GeneralPaperRetainedTrajectoryBits
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open GeneralPaperCatalogueEpochCache
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rowBits {m : ℕ} (row : FixedArrayTable m ℕ) : ℕ := ∑ j, (1+binaryWordWidth (row.read j))
def trajectoryBits {m : ℕ} (rows : Array (FixedArrayTable m ℕ)) : ℕ := ∑ j : Fin rows.size, rowBits rows[j.val]

theorem row_bound {m : ℕ} (row : FixedArrayTable m ℕ) (L : ℕ) (hWord : ∀ j,1+binaryWordWidth (row.read j)≤L) : rowBits row≤m*L := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hWord j)
  simpa only [rowBits,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

theorem trajectory_bound {m : ℕ} (rows : Array (FixedArrayTable m ℕ)) (L : ℕ)
    (hRows : ∀ j : Fin rows.size,rowBits rows[j.val]≤m*L) : trajectoryBits rows≤rows.size*(m*L) := by
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hRows j)
  simpa only [trajectoryBits,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using h

theorem candidate_word {m k : ℕ} (cache : Cache m k) (powers : GeneralPaperPreparedPowers.Prepared)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (state : State cache) (j : Fin m) :
    1+binaryWordWidth ((GeneralPaperCatalogueEpoch.round cache powers profit T weights Bc Br state).candidate.read j)≤
      GeneralPaperDecoderControls.operandWidth cache.alphabet.lambda := by
  have h := GeneralPaperSelectedRowCodesPrice.code_word cache.candidate
    (GeneralPaperCatalogueEpochRows.chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).candidate j
  have ha : cache.candidate.alphabet=cache.alphabet := by rw [cache.candidate_spec]; rfl
  rw [ha] at h
  change 1+binaryWordWidth ((GeneralPaperCatalogueRowSemantics.rowCodes cache.candidate.data
    (GeneralPaperCatalogueEpochRows.chooseRows cache profit T weights (GeneralPaperAdaptiveEpoch.snapshots powers state.fields) Bc Br).candidate).read j)≤_
  rw [GeneralPaperCatalogueRowSemantics.rowCodes,FixedArrayTable.read_ofFn]
  exact h

theorem epoch_bits {m : ℕ} (shared : Shared m) (a : Alphabet) (k : ℕ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda) :
    trajectoryBits (epoch shared a k trees).2≤shared.trajectory.period*(m*GeneralPaperDecoderControls.operandWidth a.lambda) := by
  have h := trajectory_bound (epoch shared a k trees).2 (GeneralPaperDecoderControls.operandWidth a.lambda) (by
    intro j
    have ht : j.val<shared.trajectory.period := lt_of_lt_of_eq j.isLt (epoch_size shared a k trees)
    change rowBits ((GeneralPaperCatalogueEpoch.execute (cache shared a k trees) shared.powers shared.profit shared.trajectory.rows
      shared.weights shared.Bc shared.Br (initial (cache shared a k trees)) shared.trajectory.period).2[j.val])≤_
    rw [GeneralPaperCatalogueEpoch.trajectory_read _ _ _ _ _ _ _ _ _ _ ht]
    exact row_bound _ _ (candidate_word _ _ _ _ _ _ _ _))
  rw [epoch_size] at h
  exact h

theorem global_row_word {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (time : Fin (execute (prepare a k Qv weights Bc Br) a k count).2.size) (j : Fin m) :
    1+binaryWordWidth (((execute (prepare a k Qv weights Bc Br) a k count).2[time.val]).read j)≤
      GeneralPaperDecoderControls.operandWidth a.lambda := by
  let shared := prepare a k Qv weights Bc Br
  let period := shared.trajectory.period
  have hp : 0<period := GeneralPaperCatalogueGlobalHistory.period_positive a.lambda k
  have ht : time.val<count*period := lt_of_lt_of_eq time.isLt (trajectory_size shared a k count)
  have he : time.val/period<count := (Nat.div_lt_iff_lt_mul hp).mpr ht
  have hr : time.val%period<period := Nat.mod_lt _ hp
  have hd : time.val/period*period+time.val%period=time.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod time.val period
  have hread := GeneralPaperCatalogueOuterTrajectory.trajectory_read shared a k count (time.val/period) (time.val%period) he hr
  change time.val/period*shared.trajectory.period+time.val%period=time.val at hd
  simp only [hd] at hread
  erw [hread,GeneralPaperCatalogueOuterTrajectory.epoch_preupdate shared a k (time.val/period) (time.val%period) hr]
  exact candidate_word _ _ _ _ _ _ _ _ j

theorem global_bits {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    trajectoryBits (execute (prepare a k Qv weights Bc Br) a k count).2≤
      count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(m*GeneralPaperDecoderControls.operandWidth a.lambda) := by
  have h := trajectory_bound (execute (prepare a k Qv weights Bc Br) a k count).2 (GeneralPaperDecoderControls.operandWidth a.lambda)
    (fun time => row_bound _ _ (global_row_word a k Qv weights Bc Br count time))
  rw [trajectory_size] at h
  exact h

theorem returned_bits {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    trajectoryBits (GeneralPaperGeometricSourceExecution.run bits index model W k Qv a c hc shared count).1.2≤
      count*shared.trajectory.period*(m*GeneralPaperDecoderControls.operandWidth a.lambda) := by
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data bits index model W k Qv a c hc weights Bc Br count he]
  exact global_bits a k Qv weights Bc Br count

theorem old_chunk_bits {m : ℕ} (a : Alphabet) (k Qv : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) :
    let shared := prepare a k Qv weights Bc Br
    trajectoryBits (execute shared a k count).2+trajectoryBits (epoch shared a k (treesAt shared a k count)).2≤
      (count+1)*shared.trajectory.period*(m*GeneralPaperDecoderControls.operandWidth a.lambda) := by
  have hp := global_bits a k Qv weights Bc Br count
  have hn := epoch_bits (prepare a k Qv weights Bc Br) a k (treesAt (prepare a k Qv weights Bc Br) a k count)
  exact (Nat.add_le_add hp hn).trans_eq (by
    change count*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(m*GeneralPaperDecoderControls.operandWidth a.lambda)+
      (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(m*GeneralPaperDecoderControls.operandWidth a.lambda)=
      (count+1)*(GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(m*GeneralPaperDecoderControls.operandWidth a.lambda)
    ring)

end Blotto.GeneralPaperRetainedTrajectoryBits
