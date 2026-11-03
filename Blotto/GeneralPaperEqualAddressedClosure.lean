import Blotto.GeneralPaperEqualAddressConstruction

/-! The measured sampler closure consumes a measured original budget length
and computes its reference width from retained route/group sizes. The final
budget copy, returned controls and headers have a separate component price. -/
namespace Blotto.GeneralPaperEqualAddressedClosure
open GeneralPaperEqualPreparedCache (Prepared)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def run {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :=
  let compacted := GeneralPaperPreparedSegmentCompaction.run full model A
  let actual := GeneralPaperEqualMeasuredClosure.make routes compacted.1 model A (k + 5) budget
  let boolean := GeneralPaperStoredBooleanCache.run actual.1 model A
  let budgetWord := GeneralPaperStoredRationalWordLength.run model A budget
  let address := GeneralPaperEqualAddressConstruction.run model A routes.table.data.size groupSize k budgetWord.1
  let hAddress : address.1 = GeneralPaperEqualBitDrawRates.address n m k (rationalWordWidth actual.1.budget) := by
    dsimp only [address]
    rw [GeneralPaperEqualAddressConstruction.data, GeneralPaperStoredRationalWordLength.data, routes.table.size, hGroupSize]
    rfl
  let sampler : GeneralPaperEqualStoredBitSampler.Sampler G l :=
    ⟨actual.1, boolean.1, k, rfl, address.1, hAddress⟩
  let work : GeneralPaperEqualMeasuredClosure.Work :=
    ⟨compacted.2, actual.2.1, actual.2.2.1, actual.2.2.2.1, actual.2.2.2.2, boolean.2⟩
  (sampler, (work, budgetWord.2, address.2, 128 * (A + budgetWord.1 + 1)))

theorem data {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :
    (run routes full groupSize hGroupSize model A k budget).1 =
      GeneralPaperEqualStoredBitSampler.prepare (GeneralPaperEqualPreparedCache.prepare G l (k + 5) budget) k rfl := by
  unfold run
  dsimp only
  rw [GeneralPaperStoredBooleanCache.data]
  apply Eq.trans (GeneralPaperEqualMeasuredClosure.canonical_close _ _ rfl _ _)
  exact GeneralPaperEqualCachedPreparation.sampler_eq _ _ k rfl rfl
    (GeneralPaperEqualMeasuredClosure.make_data routes _ model A (k + 5) budget)

theorem previous {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :
    let result := run routes full groupSize hGroupSize model A k budget
    (result.1, result.2.1) = GeneralPaperEqualMeasuredClosure.run routes full groupSize hGroupSize model A k budget := by
  dsimp only
  apply Prod.ext
  · exact (data routes full groupSize hGroupSize model A k budget).trans
      (GeneralPaperEqualMeasuredClosure.data routes full groupSize hGroupSize model A k budget).symm
  · rfl

theorem closure_work {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (groupSize : ℕ) (hGroupSize : groupSize = m)
    (model : RationalCostModel) (A k : ℕ) (budget : ℚ) :
    let result := (run routes full groupSize hGroupSize model A k budget).2
    let b := rationalWordWidth budget
    result.2.1 + result.2.2.1 + result.2.2.2 ≤
      4096 * (b + A + model.rat (GeneralPaperEqualAddressConstruction.operandWidth n m k b) + 1) := by
  dsimp only
  have hBudget := GeneralPaperStoredRationalWordLength.work model A budget
  have hAddress := GeneralPaperEqualAddressConstruction.work model A routes.table.data.size groupSize k
    (GeneralPaperStoredRationalWordLength.run model A budget).1
  rw [GeneralPaperStoredRationalWordLength.data, routes.table.size, hGroupSize] at hAddress
  have hArg : binaryWordWidth (rationalWordWidth budget) + 3 ≤
      GeneralPaperEqualAddressConstruction.operandWidth n m k (rationalWordWidth budget) := by
    unfold GeneralPaperEqualAddressConstruction.operandWidth
    omega
  have hRat := model.monotone hArg
  unfold run
  dsimp only
  rw [GeneralPaperStoredRationalWordLength.data, routes.table.size, hGroupSize]
  omega

end Blotto.GeneralPaperEqualAddressedClosure
