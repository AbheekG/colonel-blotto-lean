import Blotto.GeneralPaperEqualCompactedCache

/-! Separate prices for the measured compaction, integer and power stages.
Width discovery and final Boolean/cache closure are not included here. -/
namespace Blotto.GeneralPaperEqualCompactedCost
open GeneralPaperEqualPreparedCache (Prepared)
open GeneralPaperPositiveSegmentCompaction (compact count)
set_option autoImplicit false
set_option maxHeartbeats 1400000

theorem compaction {n m r s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ)
    (hs : 2 ≤ s) (h : ∀ i, RationalHeight (l.weight i) s) :
    (GeneralPaperEqualCompactedCache.run routes full model A K budget).2.1 ≤
      GeneralPaperPreparedSegmentCompaction.bound model A r s :=
  GeneralPaperPreparedSegmentCompaction.work full model A hs h

theorem integer {n m r s : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ)
    (h : ∀ i, RationalHeight (l.weight i) s) :
    (GeneralPaperEqualCompactedCache.run routes full model A K budget).2.2.1 ≤
      count l * GeneralPaperStoredCategoricalProduct.stepBound model A (count l) s + 64 * A + 64 ∧
    (GeneralPaperEqualCompactedCache.run routes full model A K budget).2.2.2.1 ≤
      count l * GeneralPaperStoredCategoricalCounts.stepBound model A (count l) s +
        PaperIndexedArrayConstruction.overhead id A (count l) (count l) + 64 * A + 64 := by
  let p := (GeneralPaperPreparedSegmentCompaction.run full model A).1
  have hp : ∀ i, RationalHeight (p.weights.read i) s := by
    intro i
    rw [p.weight_correct]
    exact h _
  exact GeneralPaperStoredCategoricalCounts.work p model A hp

theorem power {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (routes : PreparedGroupOutput G) (full : PreparedSegmentDescriptor l)
    (model : RationalCostModel) (A K : ℕ) (budget : ℚ) :
    (GeneralPaperEqualCompactedCache.run routes full model A K budget).2.2.2.2 ≤
      64 * (binaryWordWidth K + 1) * (A + model.rat (GeneralPaperNatPowerOperands.width 2 K)) + 128 * A + 128 := by
  have hp := GeneralPaperNatPowerBits.work model.rat model.monotone A 2 K (by decide)
  exact Nat.add_le_add_right (Nat.add_le_add_right hp (128 * A)) 128

theorem integer_headline (model : RationalCostModel) (A c s : ℕ) (hc : c ≤ 7) :
    c * GeneralPaperStoredCategoricalProduct.stepBound model A c s + 64 * A + 64 +
      (c * GeneralPaperStoredCategoricalCounts.stepBound model A c s +
        PaperIndexedArrayConstruction.overhead id A c c + 64 * A + 64) ≤
      1048576 * (model.rat (7 * s + 2) + A + 1) := by
  have hArg : s * c + 2 ≤ 7 * s + 2 := by nlinarith only [hc]
  have hRat := model.monotone hArg
  have hS := model.word_le (7 * s + 2)
  have hWord : binaryWordWidth (c + 1) ≤ 4 := by
    have hw := binaryWordWidth_mono (show c + 1 ≤ 8 by omega)
    have he : binaryWordWidth 8 = 4 := by decide
    omega
  have hOver := PaperIndexedArrayConstruction.overhead_bound id 1
    (fun w => by change w ≤ 1 * w; omega) A c c le_rfl
  have hOver' : PaperIndexedArrayConstruction.overhead id A c c ≤ 8 * (6 * A + 68) := by
    have hm := Nat.mul_le_mul (show c + 1 ≤ 8 by omega)
      (show 6 * A + 10 * 1 * binaryWordWidth (c + 1) + 28 ≤ 6 * A + 68 by omega)
    exact hOver.trans hm
  have hP := Nat.mul_le_mul_right (GeneralPaperStoredCategoricalProduct.stepBound model A c s) hc
  have hC := Nat.mul_le_mul_right (GeneralPaperStoredCategoricalCounts.stepBound model A c s) hc
  simp only [GeneralPaperStoredCategoricalProduct.stepBound, GeneralPaperStoredCategoricalCounts.stepBound] at hP hC ⊢
  nlinarith only [hRat, hS, hWord, hOver', hP, hC]

end Blotto.GeneralPaperEqualCompactedCost
