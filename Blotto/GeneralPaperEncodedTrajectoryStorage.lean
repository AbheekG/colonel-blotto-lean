import Blotto.GeneralPaperEncodedSnapshotStorage

/-! Complete recorded-row storage includes code payloads, per-coordinate
references, row descriptors, outer references and reserved unused row slots.
No full trajectory or output allocation product is materialized again. -/
namespace Blotto.GeneralPaperEncodedTrajectoryStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueOuterLoop
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def rowFootprint {m : ℕ} (W : ℕ) (row : FixedArrayTable m ℕ) : ℕ := GeneralPaperEncodedNatArray.footprint W row+32*W

def footprint {m : ℕ} (W capacity : ℕ) (rows : Array (FixedArrayTable m ℕ)) : ℕ :=
  GeneralPaperRetainedTrajectoryBits.trajectoryBits rows+rows.size*(m*W+64*W)+capacity*W+64*W

theorem structural_footprint {m : ℕ} (W capacity : ℕ) (rows : Array (FixedArrayTable m ℕ)) :
    GeneralPaperEncodedReferenceVector.reservedFootprint W capacity (rowFootprint W) rows=footprint W capacity rows := by
  simp only [GeneralPaperEncodedReferenceVector.reservedFootprint,GeneralPaperEncodedReferenceVector.payload,rowFootprint,
    GeneralPaperEncodedNatArray.footprint,GeneralPaperEncodedNatArray.payload,footprint,
    GeneralPaperRetainedTrajectoryBits.trajectoryBits,GeneralPaperRetainedTrajectoryBits.rowBits,
    Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
  ring

def profile (W m lambda k : ℕ) : ℕ :=
  (GeneralPaperTrajectoryParameters.prepare lambda k).rows*
    (m*GeneralPaperDecoderControls.operandWidth lambda+m*W+65*W)+64*W

theorem actual {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    footprint W (GeneralPaperTrajectoryParameters.prepare a.lambda k).rows (execute (prepare a k Qv weights Bc Br) a k count).2≤
      profile W m a.lambda k := by
  have hp := GeneralPaperRetainedTrajectoryBits.global_bits a k Qv weights Bc Br count
  have hs : (execute (prepare a k Qv weights Bc Br) a k count).2.size≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows := by
    rw [trajectory_size]
    exact Nat.mul_le_mul_right _ he
  have hb := Nat.mul_le_mul_right (m*GeneralPaperDecoderControls.operandWidth a.lambda)
    (Nat.mul_le_mul_right (GeneralPaperTrajectoryParameters.prepare a.lambda k).period he)
  change _≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).rows*(m*GeneralPaperDecoderControls.operandWidth a.lambda) at hb
  have hm := Nat.mul_le_mul_right (m*W+64*W) hs
  unfold footprint profile
  nlinarith only [hp,hb,hm]

theorem epoch {m : ℕ} (W k : ℕ) (a : Alphabet) (shared : Shared m) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda) :
    footprint W shared.trajectory.period (GeneralPaperCatalogueOuterLoop.epoch shared a k trees).2≤
      shared.trajectory.period*(m*GeneralPaperDecoderControls.operandWidth a.lambda+m*W+65*W)+64*W := by
  have hb := GeneralPaperRetainedTrajectoryBits.epoch_bits shared a k trees
  unfold footprint
  rw [epoch_size]
  nlinarith only [hb]

theorem old_chunk {m : ℕ} (W k Qv : ℕ) (a : Alphabet) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ)
    (count : ℕ) (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    footprint W shared.trajectory.rows (execute shared a k count).2+
      footprint W shared.trajectory.period (GeneralPaperCatalogueOuterLoop.epoch shared a k (treesAt shared a k count)).2≤
      profile W m a.lambda k+
        (GeneralPaperTrajectoryParameters.prepare a.lambda k).period*(m*GeneralPaperDecoderControls.operandWidth a.lambda+m*W+65*W)+64*W := by
  have h := Nat.add_le_add (actual W k Qv a weights Bc Br count he)
    (epoch W k a (prepare a k Qv weights Bc Br) (treesAt (prepare a k Qv weights Bc Br) a k count))
  simpa only [Nat.add_assoc,GeneralPaperCatalogueShared.prepare] using h

theorem returned {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    footprint W shared.trajectory.rows (GeneralPaperGeometricSourceExecution.run bits index model W k Qv a c hc shared count).1.2≤
      profile W m a.lambda k := by
  dsimp only
  rw [GeneralPaperGeometricSourceExecution.data bits index model W k Qv a c hc weights Bc Br count he]
  exact actual W k Qv a weights Bc Br count he

end Blotto.GeneralPaperEncodedTrajectoryStorage
