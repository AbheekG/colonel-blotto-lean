import Blotto.GeneralPaperFirstStoredFamilies

/-! Actual installed and returned finite RAM for the corrected source.
Every field prefix and final memory is bounded by the complete mixed-width
sampler description. Result attachment shares that memory and root. -/
namespace Blotto.GeneralPaperFirstStoredResident
open GeneralPaperStoredConstructorMemoryOwnership (grouped_returned dominant_returned)
open GeneralPaperPayloadMemoryOwnership (Bounded)
open GeneralPaperUnifiedFieldValue (encode)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualInputDomain
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

theorem selected_returned {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualFirstNativeFacts.rounded true model W k values v hv) k budget)
    (returned : Installed source.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned) :
    Bounded encode returned.memory (GeneralPaperEqualSelectedDescription.footprint source) := by
  have hInnerCap := GeneralPaperEqualFirstMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hTotalCap := GeneralPaperEqualFirstMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  have hExtent : (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum +
      (GeneralPaperEqualMeasuredLayout.outer model S source).sizes.sum = GeneralPaperEqualSelectedDescription.footprint source := by
    dsimp only [GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredLayout.outer]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum,GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    rfl
  rw [← hExtent]
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).values = some returned at hReturn
      exact dominant_returned model S A chosen.val row hWidths.2 hInnerCap returned hReturn
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      obtain ⟨actual,hActual,_,_,_⟩ := GeneralPaperStoredGroupedOuterConstruction.source model S sampler hInnerCap hTotalCap
      have hMemory := grouped_returned model S sampler hInnerCap actual hActual
      simp only [GeneralPaperStoredSelectedConstruction.run,hActual,Option.map_some,
        GeneralPaperStoredSelectedConstruction.recast] at hReturn
      have hEq := Option.some.inj hReturn
      rw [← hEq]
      exact hMemory

theorem pipeline_returned (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (returned : Installed (GeneralPaperFirstStoredPipeline.width model A K p))
    (hReturn : (GeneralPaperFirstStoredPipeline.run model A K p).1 = some returned) :
    Bounded encode returned.memory (GeneralPaperEqualSelectedDescription.footprint (GeneralPaperEqualFirstInputPipeline.run model A K p).1) := by
  let a := (GeneralPaperEqualFirstInputPipeline.run model A K p).1
  obtain ⟨inner,hBuilt,_,_⟩ := GeneralPaperFirstStoredConstruction.source model (word K p) (word K p)
    p.k p.values p.selector p.correct p.budget a
  dsimp only [a] at hBuilt
  have hMemory := selected_returned model (word K p) (word K p) p.k p.values p.selector p.correct p.budget _ inner hBuilt
  simp only [GeneralPaperFirstStoredPipeline.run,hBuilt] at hReturn
  have hEq := Option.some.inj hReturn
  rw [← hEq]
  exact hMemory


end Blotto.GeneralPaperFirstStoredResident
