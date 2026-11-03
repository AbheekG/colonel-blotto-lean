import Blotto.GeneralPaperStoredGroupedOuterDraw

/-! Source-only grouped outer construction lays out both pools once, builds
and initializes the inner sampler once, then extracts and installs outer
fields in that same memory. No regions, sizes or fit certificates execute. -/
namespace Blotto.GeneralPaperStoredGroupedOuterConstruction
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout
open GeneralPaperStoredGroupedOuterDraw (Refines)
set_option autoImplicit false
set_option maxHeartbeats 900000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

structure Result (I A : ℕ) where
  values : Option (Installed A)
  remaining : List (GeneralPaperSequentialLayout.Region I)
  work : ℕ

def layout (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) :=
  GeneralPaperMeasuredTwoPoolLayout.run model S sampler.address (sampler.address + 1)
    (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler)
    (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1))

def run (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) : Result sampler.address (sampler.address + 1) :=
  let regions := layout model S sampler
  let inner := GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler regions.inner
  let fields := extract S (sampler.address + 1) regions.outer
  match inner.values,fields.1 with
  | some actualInner,some actualFields =>
    let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1)
      (regions.work + fields.2) actualFields actualInner 1
    ⟨some outer,inner.remaining,outer.work⟩
  | _,_ => ⟨none,inner.remaining,regions.work + inner.work + fields.2 + 128 * (S + 2 * sampler.address + 2)⟩

theorem fields_source (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    (extract S (sampler.address + 1) (layout model S sampler).outer).1 =
      some (canonical (sampler.address + 1) (layout model S sampler).boundary) :=
  GeneralPaperEqualOuterFieldLayout.extracted model S (sampler.address + 1) _

theorem source (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1)) :
    ∃ returned : Installed (sampler.address + 1),(run model S sampler).values = some returned ∧
      (run model S sampler).remaining = [] ∧ returned.work = (run model S sampler).work ∧
      Refines model (sampler.address + 1) returned sampler := by
  have hI := GeneralPaperStoredNativeConstruction.address_positive sampler
  obtain ⟨inner,hInner,hRemaining,_,hRoot,hContract⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S sampler.address 0 sampler [] hI
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner hRemaining
  have hInnerActual : (GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler (layout model S sampler).inner).values = some inner := hInner
  have hRemainingActual : (GeneralPaperCountedSamplerInstallation.run model S sampler.address sampler (layout model S sampler).inner).remaining = [] := hRemaining
  have hBoundary : (layout model S sampler).boundary = (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S sampler.address (sampler.address + 1) _ _
  let outer := GeneralPaperStoredOuterAttachment.finish model S sampler.address (sampler.address + 1)
    ((layout model S sampler).work + (extract S (sampler.address + 1) (layout model S sampler).outer).2)
    (canonical (sampler.address + 1) (layout model S sampler).boundary) inner 1
  have hReturn : (run model S sampler).values = some outer := by simp only [run,hInnerActual,fields_source,outer]
  have hRest : (run model S sampler).remaining = [] := by simp only [run,hInnerActual,fields_source,hRemainingActual]
  have hWork : outer.work = (run model S sampler).work := by simp only [run,hInnerActual,fields_source,outer]
  refine ⟨outer,hReturn,hRest,hWork,?_⟩
  have hRefines := GeneralPaperStoredGroupedOuterDraw.attached_source model S
    ((layout model S sampler).work + (extract S (sampler.address + 1) (layout model S sampler).outer).2)
    sampler inner hContract hRoot hInnerCap hOuterCap
  simpa only [Refines,outer,hBoundary] using hRefines

theorem every_returned (model : RationalCostModel) (S : ℕ) (sampler : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (sampler.address + 1)).sizes.sum < 2 ^ (sampler.address + 1))
    (returned : Installed (sampler.address + 1)) (hReturn : (run model S sampler).values = some returned) :
    Refines model (sampler.address + 1) returned sampler := by
  obtain ⟨actual,hActual,_,_,hRefines⟩ := source model S sampler hInnerCap hOuterCap
  have hEq : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hEq]
  exact hRefines

end Blotto.GeneralPaperStoredGroupedOuterConstruction
