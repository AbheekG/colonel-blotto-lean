import Blotto.GeneralPaperFirstStoredWork

/-! Complete existing constructor windows for the corrected selected
source: measurement, layout, counts, directory/scalar installation, reference
collection, nested cursor and outer/result frames. All capacities and actual
prices are discharged from that same source. -/
namespace Blotto.GeneralPaperFirstStoredWindows
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 8192

namespace Temporary
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperFieldDirectory (Directory)
open GeneralPaperFieldDirectorySafety (Safe)
open GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperMeasuredLayoutStorage
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSelectedTemporaryOwners

theorem layout_price {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    (run model S source).work ≤ GeneralPaperCompleteSelectedPreparationWork.bound model S source := by
  have hWidths := widths_positive source
  have hLayout := GeneralPaperTwoPoolPreparationWork.layout_work model S (innerWidth source) source.address
    (inner model S source) (inner_good model S source) hWidths.1 hWidths.2
    (GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source) (GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source)
  change (run model S source).work ≤ _ at hLayout
  have hInnerPrice := Nat.mul_le_mul_right (unit model S (innerWidth source))
    (Nat.mul_le_mul_left ((inner model S source).sizes.sum + 1) (show 1909 ≤ 2077 by decide))
  unfold GeneralPaperCompleteSelectedPreparationWork.bound GeneralPaperTwoPoolPreparationWork.bound
  dsimp only [outer]
  omega


theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  have hInnerCap := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hTotalCap := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source
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


end Temporary

namespace Layout
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSelectedLayoutLifetime

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hOwners := GeneralPaperFirstStoredWindows.Temporary.window_bound model W S k values v hv budget source
  have hWidths := widths_positive source
  have hInner := GeneralPaperSelectedTemporaryOwners.inner_good model S source
  have hOuter := GeneralPaperMeasuredRetainedPlanWork.header model S source.address hWidths.2
  have hFrames := GeneralPaperTwoPoolLayoutLifetime.window_bound model S (innerWidth source) source.address
    (GeneralPaperCompleteSelectedPreparationWork.bound model S source)
    (inner model S source) (outer model S source) hInner.1 hOuter.1 hWidths.1 hWidths.2
    (GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source) (GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source)
    (GeneralPaperFirstStoredWindows.Temporary.layout_price model W S k values v hv budget source)
  exact Nat.add_le_add hOwners hFrames


end Layout

namespace Installation
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperPayloadMemoryOwnership (Bounded cellSize)
open GeneralPaperUnifiedFieldValue (Value encode)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
open GeneralPaperSelectedInstallationLifetime

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  exact GeneralPaperDirectoryInstallationLifetime.count_expanded_window model S (innerWidth source) 0 (inner model S source)
    (GeneralPaperSelectedTemporaryOwners.directory model S source) (GeneralPaperPayloadMemory.empty Value)
    (GeneralPaperSelectedTemporaryOwners.directory_safe model S source) (directory_covered model S source)
    (GeneralPaperSelectedTemporaryOwners.inner_good model S source).1 hWidths.1
    (by simpa only [Nat.zero_add] using GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source)


end Installation

namespace Count
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
open GeneralPaperSelectedCountPreparationLifetime

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  exact GeneralPaperHeaderCountDirectoryLifetime.window_bound model S (innerWidth source) 0 (inner model S source)
    (GeneralPaperSelectedTemporaryOwners.directory model S source)
    (GeneralPaperSelectedTemporaryOwners.directory_safe model S source)
    (GeneralPaperSelectedTemporaryOwners.inner_good model S source).1 (widths_positive source).1
    (by simpa only [Nat.zero_add] using GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source)


end Count

namespace Collection
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperPayloadMemoryOwnership (cellSize)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open scoped BigOperators
open GeneralPaperSelectedReferenceCollectionLifetime

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  exact GeneralPaperDirectoryReferenceCollectionLifetime.count_expanded_window model S (innerWidth source) 0 (inner model S source)
    (GeneralPaperSelectedTemporaryOwners.directory model S source)
    (GeneralPaperSelectedTemporaryOwners.directory_safe model S source)
    (GeneralPaperSelectedTemporaryOwners.inner_good model S source).1 (widths_positive source).1
    (by simpa only [Nat.zero_add] using GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source)


end Collection

namespace Measurement
open GeneralPaperMeasuredPlanLifetimeAlgebra
open GeneralPaperMeasuredScalarPlanLifetime
open GeneralPaperMeasuredRecordPlanLifetime
open GeneralPaperMeasuredLeafRecordLifetime
open GeneralPaperMeasuredRetainedPlanLifetime
open GeneralPaperEqualMeasuredLeafPlans
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout
open GeneralPaperSelectedMeasurementLifetime

theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source := by
  have hWidths := widths_positive source
  have hInner := (inner_good model S source).2 _ (GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source) le_rfl
  have hTotal := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source
  have hOuter := (header_good model S source.address hWidths.2).2
    (outer model S source).work (show (outer model S source).sizes.sum < 2 ^ source.address by omega) le_rfl
  exact Nat.add_le_add hInner hOuter


end Measurement

namespace Outer
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperSelectedOuterLifetime

theorem dispatch_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    dispatchWindow model S source ≤ unit model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source) := by
  have hPrice := GeneralPaperFirstStoredConstruction.work model W S k values v hv budget source
  have hFields := fields_bound S (natBits (cap S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)))
    [S,source.address,(GeneralPaperStoredSelectedConstruction.run model S source).2] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 3 * (natBits (cap S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S source.address (GeneralPaperCompleteSelectedPreparationWork.bound model S source)
  unfold dispatchWindow
  omega


theorem branch_window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    branchWindow model S source ≤ GeneralPaperOuterConstructionLifetime.profile model S source.address
      (GeneralPaperCompleteSelectedPreparationWork.bound model S source) := by
  have hInner := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hTotal := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      exact GeneralPaperOuterConstructionLifetime.dominant_bound model S A chosen.val row hWidths.2 hInner hTotal
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      exact GeneralPaperOuterConstructionLifetime.grouped_bound model S sampler hInner hTotal


theorem window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source :=
  Nat.add_le_add (branch_window_bound model W S k values v hv budget source) (dispatch_bound model W S k values v hv budget source)


end Outer

open GeneralPaperEqualSelectedSampler (Sampler)

theorem combined {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget) :
    GeneralPaperSelectedOuterInputLifetime.combinedWindow model S source ≤
      GeneralPaperSelectedOuterInputLifetime.combinedBound model S source := by
  have hLayout := Layout.window_bound model W S k values v hv budget source
  have hCount := Count.window_bound model W S k values v hv budget source
  have hInstall := Installation.window_bound model W S k values v hv budget source
  have hCollect := Collection.window_bound model W S k values v hv budget source
  have hMeasure := Measurement.window_bound model W S k values v hv budget source
  have hCursor := GeneralPaperSelectedCursorLifetime.window_bound model S source
    (GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source)
  have hOuter := Outer.window_bound model W S k values v hv budget source
  dsimp only [GeneralPaperSelectedOuterInputLifetime.combinedWindow,GeneralPaperSelectedOuterInputLifetime.combinedBound,
    GeneralPaperSelectedCursorInputLifetime.combinedWindow,GeneralPaperSelectedCursorInputLifetime.combinedBound,
    GeneralPaperSelectedMeasurementInputLifetime.combinedWindow,GeneralPaperSelectedMeasurementInputLifetime.combinedBound,
    GeneralPaperSelectedMeasurementInputLifetime.window,GeneralPaperSelectedMeasurementInputLifetime.bound,
    GeneralPaperSelectedReferenceCollectionLifetime.combinedWindow,GeneralPaperSelectedReferenceCollectionLifetime.combinedBound,
    GeneralPaperSelectedCountPreparationLifetime.combinedWindow,GeneralPaperSelectedCountPreparationLifetime.combinedBound]
  omega

end Blotto.GeneralPaperFirstStoredWindows
