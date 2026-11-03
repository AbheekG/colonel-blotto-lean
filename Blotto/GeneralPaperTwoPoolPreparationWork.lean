import Blotto.GeneralPaperCompleteSamplerCursorWorkRates

/-! Complete measured two-pool and outer-field preparation components.
Each plan/layout is executed once; inner prefixes are priced separately from
the parent layout. All mixed-width terms retain their actual address widths. -/
namespace Blotto.GeneralPaperTwoPoolPreparationWork
open GeneralPaperMeasuredBlockPlan GeneralPaperMeasuredPlanWorkAlgebra
open GeneralPaperSequentialLayout GeneralPaperDirectoryCopyWork
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def bound (model : RationalCostModel) (S I A Bi Bo : ℕ) : ℕ :=
  (Bi + 1) * 2077 * unit model S I + (Bo + 1) * 12 * unit model S A +
    (Bi + 1) * stepPrice model S I + (Bo + 1) * stepPrice model S A +
    GeneralPaperStoredDirectoryPreparationWork.bound model S I Bi +
    GeneralPaperStoredPreparationConstructorWork.outerBound model S I A Bo +
    4 * unit model S A + 192 * (S + I + A + 1)

theorem extract_work (model : RationalCostModel) (S A start : ℕ) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperEqualOuterFieldLayout.extract S A
      (GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).1).2 ≤
      4 * unit model S A := by
  have hRegions := layout_region_work model S A start (GeneralPaperEqualMeasuredSelectedPlan.header model S A) hA hCap
  rw [GeneralPaperEqualOuterFieldLayout.regions] at hRegions
  have hControl := hRegions (GeneralPaperEqualOuterFieldLayout.canonical A start).control (by simp)
  have hValue := hRegions (GeneralPaperEqualOuterFieldLayout.canonical A start).value (by simp)
  have hRecord := hRegions (GeneralPaperEqualOuterFieldLayout.canonical A start).record (by simp)
  have hMeta := metadata model S A
  rw [GeneralPaperEqualOuterFieldLayout.regions]
  change GeneralPaperEncodedScalarStorage.natBits _ + GeneralPaperEncodedScalarStorage.natBits _ +
    GeneralPaperEncodedScalarStorage.natBits _ + GeneralPaperEncodedScalarStorage.natBits _ +
    GeneralPaperEncodedScalarStorage.natBits _ + GeneralPaperEncodedScalarStorage.natBits _ + 6 * A + 256 * (S + A + 1) ≤ _
  unfold GeneralPaperLastRegionSelection.price at hControl hValue hRecord
  omega

theorem dominant_plan {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (row : RationalResourceArray n) (hA : 0 < A) :
    Good model S A 34 (GeneralPaperStoredDominantCursor.plan model S A chosen row) := by
  apply sequence_work model S A 9 _ hA
  intro p hp
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hp
  rcases hp with rfl|rfl|rfl
  · exact GeneralPaperMeasuredArrayPlanWork.array model S A 1 _ (GeneralPaperStoredDominantCursor.rowTable row) hA
      (fun j => GeneralPaperMeasuredLeafPlanWork.rational model S A ((GeneralPaperStoredDominantCursor.rowTable row).read j) hA)
  · exact mono model S A 1 9 _ (GeneralPaperMeasuredLeafPlanWork.natural model S A chosen hA) (by decide)
  · exact mono model S A 1 9 _ (GeneralPaperMeasuredLeafPlanWork.reserve model S A 32 hA (by decide) (by decide)) (by decide)

theorem layout_work (model : RationalCostModel) (S I A : ℕ) (inner : Plan)
    (hInner : Good model S I 1909 inner) (hI : 0 < I) (hA : 0 < A)
    (hInnerCap : inner.sizes.sum < 2 ^ I)
    (hOuterCap : inner.sizes.sum + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    (GeneralPaperMeasuredTwoPoolLayout.run model S I A inner (GeneralPaperEqualMeasuredSelectedPlan.header model S A)).work ≤
      (inner.sizes.sum + 1) * 1909 * unit model S I +
        ((GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum + 1) * 12 * unit model S A +
        (inner.sizes.sum + 1) * stepPrice model S I +
        ((GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum + 1) * stepPrice model S A + 192 * (S + I + A + 1) := by
  have hOuter := GeneralPaperMeasuredRetainedPlanWork.header model S A hA
  have hHeaderCap : (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A := by omega
  have hInnerWork := hInner.2 hInnerCap
  have hOuterWork := hOuter.2 hHeaderCap
  have hInnerCount := GeneralPaperMeasuredPlanPositive.block_count inner hInner.1
  have hOuterCount := GeneralPaperMeasuredPlanPositive.block_count _ hOuter.1
  have hIC := Nat.mul_le_mul_right (stepPrice model S I) (Nat.add_le_add_right hInnerCount 1)
  have hOC := Nat.mul_le_mul_right (stepPrice model S A) (Nat.add_le_add_right hOuterCount 1)
  have h := GeneralPaperMeasuredTwoPoolLayout.work model S I A inner _ hI hA hInnerCap hOuterCap
  omega

@[fun_prop]
theorem rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S I A Bi Bo r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hI : Tight I L) (hA : Tight A L) (hBi : Bound Bi r L) (hBo : Bound Bo r L) :
    Bound (fun x => bound model (S x) (I x) (A x) (Bi x) (Bo x)) r L := by
  have hSP := polylog_of_tight hS
  have hIP := polylog_of_tight hI
  have hAP := polylog_of_tight hA
  have hUI := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S I L hL hS hI
  have hUA := GeneralPaperMeasuredPlanWorkRates.unit_rate model hFast S A L hL hS hA
  have hSI := GeneralPaperStoredPreparationWorkRates.layout_step_rate model hFast S I L hL hS hI
  have hSA := GeneralPaperStoredPreparationWorkRates.layout_step_rate model hFast S A L hL hS hA
  have hInnerDir := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S I Bi r L hL hr hS hI hBi
  have hOuterDir := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A Bo r L hL hr hS hA hBo
  have hEncode := GeneralPaperStoredPreparationWorkRates.encode_rate model hFast S A L hL hS hA
  have hInstall : Bound (fun x => GeneralPaperStoredDirectoryPreparationWork.installBound model (S x) (A x) (Bo x)) r L :=
    dominated hOuterDir (fun x => by unfold GeneralPaperStoredDirectoryPreparationWork.bound; omega)
  unfold bound GeneralPaperStoredPreparationConstructorWork.outerBound
  fun_prop (config := {maxSteps := 30000})

end Blotto.GeneralPaperTwoPoolPreparationWork
