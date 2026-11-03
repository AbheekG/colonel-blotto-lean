import Blotto.GeneralPaperEqualFirstMeasuredLayout

/-! The existing actual dominant installer and reader satisfy their
capacity and source contracts for the corrected selected branch. -/
namespace Blotto.GeneralPaperFirstStoredDominantContract
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option maxRecDepth 8192

theorem bounds {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) :
    0 < a.address ∧ (GeneralPaperStoredDominantCursor.plan model S a.address chosen.val row).sizes.sum < 2 ^ a.address ∧
      (GeneralPaperStoredDominantCursor.plan model S a.address chosen.val row).sizes.sum +
        (GeneralPaperEqualMeasuredSelectedPlan.header model S a.address).sizes.sum < 2 ^ a.address := by
  have hI := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget a
  have hT := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget a
  dsimp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredLayout.innerWidth,
    GeneralPaperEqualMeasuredLayout.outer] at hI hT
  rw [hBranch] at hI hT
  exact ⟨(GeneralPaperEqualMeasuredLayout.widths_positive a).2,hI,hT⟩

theorem every_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct)
    (returned : Installed a.address)
    (hReturn : (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned) :
    (GeneralPaperStoredDominantOuterDraw.run model a.address returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).count = n := by
  obtain ⟨hA,hI,hT⟩ := bounds model W S k values v hv budget a chosen heavy row correct hBranch
  exact GeneralPaperStoredDominantOuterConstruction.every_returned model S a.address chosen.val row hA hI hT returned hReturn

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (a : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (chosen : Fin n) (heavy : 1 / 2 ≤ (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv).weight chosen)
    (row : RationalResourceArray n) (correct : row.realAllocation = PureBoundaryEquilibria.vertex (budget : ℝ) chosen)
    (hBranch : a.branch = .dominant chosen heavy row correct) :
    ∃ returned : Installed a.address,
      (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).values = some returned ∧
      (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).remaining = [] ∧
      returned.work = (GeneralPaperStoredDominantOuterConstruction.run model S a.address chosen.val row).work ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).values = some row.data ∧
      (GeneralPaperStoredDominantOuterDraw.run model a.address returned).count = n := by
  obtain ⟨hA,hI,hT⟩ := bounds model W S k values v hv budget a chosen heavy row correct hBranch
  exact GeneralPaperStoredDominantOuterConstruction.source model S a.address chosen.val row hA hI hT


end Blotto.GeneralPaperFirstStoredDominantContract
