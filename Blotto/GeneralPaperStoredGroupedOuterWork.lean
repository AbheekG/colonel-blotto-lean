import Blotto.GeneralPaperStoredOuterWorkRates

/-! The complete mixed-width outer grouped draw adds its actual dispatch
work to one complete inner allocation draw in the same extended memory.
The inner owner/readback contract is preserved by the actual outer writes. -/
namespace Blotto.GeneralPaperStoredGroupedOuterWork
open MeasureTheory
open scoped ENNReal
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperHeaderCountInstallation (Contract)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperStoredReadContext (Context)
open GeneralPaperEqualRejectionTraceMeasure
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def bound (model : RationalCostModel) (s b c : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  GeneralPaperStoredDispatchLoadWork.groupedBound model (sampler.address + 1) +
    GeneralPaperStoredAllocationWork.expectedBound model sampler.address s b c sampler + 256 * (sampler.address + 1)

theorem attached_expected (model : RationalCostModel) (S prefixWork s b c : ℕ)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) (inner : Installed sampler.address)
    (hContract : Contract model sampler.address inner (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0))
    (hRoot : inner.root = (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0).root.reference)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c) :
    let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1) prefixWork
      (canonical (sampler.address + 1) (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum) inner 1
    (∫⁻ trace, ((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) outer sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤ (bound model s b c sampler : ℝ≥0∞) := by
  dsimp only
  let plan := GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler
  let fields := canonical (sampler.address + 1) plan.sizes.sum
  let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1) prefixWork fields inner 1
  let loaded := GeneralPaperStoredScalarRead.atRoot outer inner.root
  have hI := GeneralPaperStoredNativeConstruction.address_positive sampler
  have hSafe := (GeneralPaperSamplerRecordCursor.success model S sampler.address 0 sampler []).2.2.1
  have hNew := GeneralPaperStoredOuterAttachment.inner_contract model S sampler.address (sampler.address + 1) prefixWork plan _ inner 1
    hSafe hI hInnerCap hContract (by omega) hOuterCap
  have ctx : Context model S sampler.address 0 plan (GeneralPaperSamplerRecordCursor.expected model S sampler.address sampler 0) loaded :=
    ⟨hNew,hSafe,hI,by simpa only [Nat.zero_add] using hInnerCap⟩
  have hExpected := GeneralPaperStoredAllocationWork.expected_work model S sampler.address 0 s b c loaded sampler ctx hRoot hs h hB hc hC
  have hOuterRead := GeneralPaperStoredOuterAttachment.outer_readback model S sampler.address (sampler.address + 1)
    plan.sizes.sum prefixWork inner 1 (by omega) hOuterCap
  have hCapacity := GeneralPaperStoredOuterReadWork.capacity model S (sampler.address + 1) plan.sizes.sum (by omega) hOuterCap
  have hLoadWork := GeneralPaperStoredDispatchLoadWork.grouped_work model sampler.address outer fields inner.root hOuterRead rfl hCapacity.1 hCapacity.2
  have hLoad := GeneralPaperStoredGroupedOuterDraw.attached_load model S sampler.address plan.sizes.sum prefixWork inner hOuterCap
  change (GeneralPaperStoredGroupedLoad.load model (sampler.address + 1) outer).1 =
    some (⟨sampler.address,loaded⟩ : GeneralPaperStoredChildRead.Child) at hLoad
  let B := GeneralPaperStoredDispatchLoadWork.groupedBound model (sampler.address + 1) + 256 * (sampler.address + 1)
  have hPoint (trace : Trace sampler.prepared.D sampler.prepared.midpointBits) :
      (GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) outer sampler.prepared.D sampler.prepared.midpointBits trace).work ≤
        (GeneralPaperStoredAllocationLaw.observed model sampler.address loaded sampler.prepared.D sampler.prepared.midpointBits trace).work + B := by
    unfold GeneralPaperStoredGroupedOuterLaw.observed GeneralPaperStoredAllocationLaw.observed
    simp only [GeneralPaperStoredGroupedOuterDraw.run,hLoad]
    unfold B
    omega
  calc
    _ ≤ ∫⁻ trace, (((GeneralPaperStoredAllocationLaw.observed model sampler.address loaded sampler.prepared.D sampler.prepared.midpointBits trace).work + B : ℕ) : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits)) :=
      lintegral_mono (fun trace => (show ((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) outer sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞) ≤
        (((GeneralPaperStoredAllocationLaw.observed model sampler.address loaded sampler.prepared.D sampler.prepared.midpointBits trace).work + B : ℕ) : ℝ≥0∞) by exact_mod_cast hPoint trace))
    _ = (∫⁻ trace, ((GeneralPaperStoredAllocationLaw.observed model sampler.address loaded sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
        ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
          Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) + B := by
      simp only [Nat.cast_add]
      rw [lintegral_add_left (measurable_of_countable _)]
      simp only [lintegral_const,measure_univ,mul_one]
    _ ≤ (GeneralPaperStoredAllocationWork.expectedBound model sampler.address s b c sampler : ℝ≥0∞) + B := add_le_add hExpected le_rfl
    _ = _ := by simp only [bound,B,Nat.cast_add]; ac_rfl

theorem every_returned_expected (model : RationalCostModel) (S s b c : ℕ)
    (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (hs : 2 ≤ s) (h : l.HeightAt s) (hB : RationalHeight sampler.prepared.budget b)
    (hc : 2 ≤ c) (hC : ∀ j,RationalHeight (sampler.prepared.routes.table.read j).2 c)
    (returned : Installed (sampler.address + 1))
    (hReturn : (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).values = some returned) :
    (∫⁻ trace, ((GeneralPaperStoredGroupedOuterLaw.observed model (sampler.address + 1) returned sampler.prepared.D sampler.prepared.midpointBits trace).work : ℝ≥0∞)
      ∂(law sampler.prepared.D sampler.prepared.midpointBits (GeneralPaperEqualPreparedCache.denominator_positive sampler.prepared) :
        Measure (Trace sampler.prepared.D sampler.prepared.midpointBits))) ≤ (bound model s b c sampler : ℝ≥0∞) := by
  have hI := GeneralPaperStoredNativeConstruction.address_positive sampler
  obtain ⟨inner,hInner,_,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S sampler.address 0 sampler [] hI
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner
  have hInnerActual : (GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler
      (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).inner).values = some inner := hInner
  have hBoundary : (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).boundary =
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum := GeneralPaperMeasuredTwoPoolLayout.boundary model S sampler.address (sampler.address + 1) _ _
  have hPrice := attached_expected model S
    ((GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).work +
      (extract S (sampler.address + 1) (GeneralPaperStoredGroupedOuterConstruction.layout model S sampler).outer).2)
    s b c sampler inner hContract hRoot hInnerCap hOuterCap hs h hB hc hC
  simp only [GeneralPaperStoredGroupedOuterConstruction.run,hInnerActual,GeneralPaperStoredGroupedOuterConstruction.fields_source] at hReturn
  rw [← Option.some.inj hReturn]
  simpa only [hBoundary] using hPrice

end Blotto.GeneralPaperStoredGroupedOuterWork
