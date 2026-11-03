import Blotto.GeneralPaperMeasuredDirectoryStorageRates

/-! Actual selected temporary data owners: both size plans, both region
lists, and the extracted inner directory coexisting with its count-expanded
copy. Native source contracts derive positivity/capacity internally. These
windows cover these simultaneous owners; recursive cursor/primitive frames,
the caller's retained source and installed memory remain separate joins. -/
namespace Blotto.GeneralPaperSelectedTemporaryOwners
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperMeasuredLayoutStorage
open GeneralPaperUnifiedDirectoryInstallation (Installed)
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def directory {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : Directory (innerWidth source) :=
  match source with
  | ⟨.dominant chosen _ row _,A,_⟩ => GeneralPaperStoredDominantCursor.expected model S A chosen.val row 0
  | ⟨.grouped _ sampler _ _,_,_⟩ => GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0

theorem directory_safe {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    Safe (GeneralPaperMeasuredBlockLayout.run model S (innerWidth source) 0 (inner model S source)).1
      (directory model S source) := by
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact (GeneralPaperStoredDominantCursor.success model S A 0 chosen.val row []).2.2.1
    | grouped small sampler hK hB =>
      exact (GeneralPaperSamplerRecordCursor.success model S sampler.address 0 sampler []).2.2.1

theorem inner_good {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    Good model S (innerWidth source) 1909 (inner model S source) := by
  have hWidths := widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact mono model S A 34 1909 _
        (GeneralPaperTwoPoolPreparationWork.dominant_plan model S A chosen.val row hWidths.2) (by decide)
    | grouped small sampler hK hB =>
      exact GeneralPaperMeasuredRetainedPlanWork.sampler model S sampler.address sampler hWidths.1

theorem plan_prices_le_layout {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    (inner model S source).work ≤ (run model S source).work ∧
      (outer model S source).work ≤ (run model S source).work := by
  dsimp only [run,GeneralPaperMeasuredTwoPoolLayout.run,GeneralPaperMeasuredBlockLayout.run]
  omega

theorem layout_price {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (run model S source).work ≤ GeneralPaperCompleteSelectedPreparationWork.bound model S source := by
  have hWidths := widths_positive source
  have hLayout := GeneralPaperTwoPoolPreparationWork.layout_work model S (innerWidth source) source.address
    (inner model S source) (inner_good model S source) hWidths.1 hWidths.2
    (inner_capacity model W S k values v hv budget source) (total_capacity model W S k values v hv budget source)
  change (run model S source).work ≤ _ at hLayout
  have hInnerPrice := Nat.mul_le_mul_right (unit model S (innerWidth source))
    (Nat.mul_le_mul_left ((inner model S source).sizes.sum + 1) (show 1909 ≤ 2077 by decide))
  unfold GeneralPaperCompleteSelectedPreparationWork.bound GeneralPaperTwoPoolPreparationWork.bound
  dsimp only [outer]
  omega

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  twoPoolFoot model S (innerWidth source) source.address (inner model S source) (outer model S source) +
    GeneralPaperFieldDirectoryStorage.countWindow model S (innerWidth source) (directory model S source)

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  let P := GeneralPaperCompleteSelectedPreparationWork.bound model S source
  twoPoolBound S (innerWidth source) source.address (inner model S source).sizes.sum (outer model S source).sizes.sum P P P +
    GeneralPaperFieldDirectoryStorage.countBound model S (innerWidth source) (inner model S source).sizes.sum

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  have hInnerCap := inner_capacity model W S k values v hv budget source
  have hTotalCap := total_capacity model W S k values v hv budget source
  have hInner := inner_good model S source
  have hOuter := GeneralPaperMeasuredRetainedPlanWork.header model S source.address hWidths.2
  have hLayout := layout_price model W S k values v hv budget source
  have hPlans := plan_prices_le_layout model S source
  have hPools := two_pool_bound model S (innerWidth source) source.address
    (inner model S source) (outer model S source) hInner.1 hOuter.1 hWidths.1 hWidths.2 hInnerCap hTotalCap
    _ _ _ (hPlans.1.trans hLayout) (hPlans.2.trans hLayout) hLayout
  have hDirectory := GeneralPaperFieldDirectoryStorage.count_window_bound model S (innerWidth source) 0
    (inner model S source) (directory model S source) (directory_safe model S source) hInner.1 hWidths.1
    (by simpa only [Nat.zero_add] using hInnerCap)
  exact Nat.add_le_add hPools hDirectory

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed source.address,
      (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedConstruction.run model S source).2 ∧
      returned.work ≤ GeneralPaperCompleteSelectedPreparationWork.bound model S source ∧
      window model S source ≤ bound model S source ∧
      GeneralPaperStoredSelectedConstruction.Contract model source.address returned source.branch := by
  obtain ⟨returned,hReturn,hWork,hPrice,hContract⟩ :=
    GeneralPaperCompleteSelectedPreparationWork.constructed model W S k values v hv budget source
  exact ⟨returned,hReturn,hWork,hPrice,window_bound model W S k values v hv budget source,hContract⟩

end Blotto.GeneralPaperSelectedTemporaryOwners
