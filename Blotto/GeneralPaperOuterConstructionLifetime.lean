import Blotto.GeneralPaperOuterAttachmentLifetime

/-! Actual source-only outer constructors join extraction, attachment and
their enclosing parent fields. The successful inner return and all saved
prices are derived from the executed constructors, not supplied oracles. -/
namespace Blotto.GeneralPaperOuterConstructionLifetime
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperEqualOuterFieldLayout (canonical extract)
open GeneralPaperEncodedScalarStorage
open GeneralPaperPayloadInstallationLifetime (cap)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit unit_bounds)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def parentWindow (S I A layoutWork childWork fieldWork totalWork : ℕ) : ℕ :=
  fields S [S,I,A,layoutWork,childWork,fieldWork,layoutWork + fieldWork,totalWork] + I + A + 256 * S

theorem parent_bound (model : RationalCostModel) (S I A P layoutWork childWork fieldWork totalWork : ℕ)
    (hI : I ≤ A) (hTotal : totalWork ≤ P) (hPrices : layoutWork + childWork + fieldWork ≤ totalWork) :
    parentWindow S I A layoutWork childWork fieldWork totalWork ≤ unit model S A P := by
  have hFields := fields_bound S (natBits (cap S A P)) [S,I,A,layoutWork,childWork,fieldWork,layoutWork + fieldWork,totalWork] (by
    intro x hx
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hx
    unfold cap
    rcases hx with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields S _ ≤ 8 * (natBits (cap S A P) + S) + 32 * S at hFields
  have hUnit := unit_bounds model S A P
  unfold parentWindow
  omega

def profile (model : RationalCostModel) (S A P : ℕ) : ℕ :=
  GeneralPaperOuterAttachmentLifetime.profile model S A (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum P +
    GeneralPaperOuterFieldCursorLifetime.profile model S A + unit model S A P

def groupedWindow {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) : ℕ :=
  let regions := GeneralPaperStoredGroupedOuterConstruction.layout model S source
  let child := GeneralPaperCountedSamplerInstallation.run model S source.address source regions.inner
  let fieldWork := (extract S (source.address + 1) regions.outer).2
  child.values.elim 0 (fun inner => GeneralPaperOuterAttachmentLifetime.window model S source.address (source.address + 1)
      (regions.work + fieldWork) (canonical (source.address + 1) regions.boundary) inner 1) +
    GeneralPaperOuterFieldCursorLifetime.window model S (source.address + 1) regions.boundary +
    parentWindow S source.address (source.address + 1) regions.work child.work fieldWork
      (GeneralPaperStoredGroupedOuterConstruction.run model S source).work

theorem grouped_bound {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
    (model : RationalCostModel) (S : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (hInnerCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum < 2 ^ source.address)
    (hOuterCap : (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum < 2 ^ (source.address + 1)) :
    groupedWindow model S source ≤ profile model S (source.address + 1) (GeneralPaperCompleteOuterPreparationWork.groupedBound model S source) := by
  let regions := GeneralPaperStoredGroupedOuterConstruction.layout model S source
  let fieldWork := (extract S (source.address + 1) regions.outer).2
  let P := GeneralPaperCompleteOuterPreparationWork.groupedBound model S source
  have hI := GeneralPaperStoredNativeConstruction.address_positive source
  have hA : 0 < source.address + 1 := by omega
  have hPrice := GeneralPaperCompleteOuterPreparationWork.grouped_work model S source hInnerCap hOuterCap
  obtain ⟨inner,hInner,_,hChildWork,_,_⟩ := GeneralPaperCountedSamplerInstallation.sampler_prefix model S source.address 0 source [] hI
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner hChildWork
  have hActual : (GeneralPaperCountedSamplerInstallation.run model S source.address source
      (GeneralPaperStoredGroupedOuterConstruction.layout model S source).inner).values = some inner := hInner
  have hChild : inner.work = (GeneralPaperCountedSamplerInstallation.run model S source.address source regions.inner).work := hChildWork
  have hRun : (GeneralPaperStoredGroupedOuterConstruction.run model S source).work =
      (GeneralPaperStoredOuterAttachment.finish model S source.address (source.address + 1)
        (regions.work + fieldWork) (canonical (source.address + 1) regions.boundary) inner 1).work := by
    dsimp only [regions,fieldWork]
    simp only [GeneralPaperStoredGroupedOuterConstruction.run,hActual,GeneralPaperStoredGroupedOuterConstruction.fields_source]
  have hBound : (GeneralPaperStoredOuterAttachment.finish model S source.address (source.address + 1)
      (regions.work + fieldWork) (canonical (source.address + 1) regions.boundary) inner 1).work ≤ P := by rw [← hRun]; exact hPrice
  have hBoundary : regions.boundary = (GeneralPaperEqualMeasuredRetainedPlan.sampler model S source.address source).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S source.address (source.address + 1) _ _
  have hCap : regions.boundary + (GeneralPaperEqualMeasuredSelectedPlan.header model S (source.address + 1)).sizes.sum < 2 ^ (source.address + 1) := by
    rw [hBoundary]; exact hOuterCap
  have hTag : 1 < 2 ^ (source.address + 1) := by
    rw [pow_succ]
    have h : 0 < 2 ^ source.address := by positivity
    omega
  have hAttach := GeneralPaperOuterAttachmentLifetime.window_bound model S source.address (source.address + 1) regions.boundary
    (regions.work + fieldWork) 1 P inner hA (Nat.le_succ _) hTag hCap hBound
  have hFields := (GeneralPaperOuterFieldCursorLifetime.constructed model S (source.address + 1) regions.boundary hA hCap).2
  have hPrices : regions.work + (GeneralPaperCountedSamplerInstallation.run model S source.address source regions.inner).work + fieldWork ≤
      (GeneralPaperStoredGroupedOuterConstruction.run model S source).work := by
    rw [hRun,← hChild]
    change _ ≤ (regions.work + fieldWork) + inner.work + _ + _ + _ + _
    omega
  have hParent := parent_bound model S source.address (source.address + 1) P regions.work
    (GeneralPaperCountedSamplerInstallation.run model S source.address source regions.inner).work fieldWork
    (GeneralPaperStoredGroupedOuterConstruction.run model S source).work (Nat.le_succ _) hPrice hPrices
  dsimp only [groupedWindow]
  rw [hActual]
  simp only [Option.elim_some]
  exact Nat.add_le_add (Nat.add_le_add hAttach hFields) hParent

def dominantWindow {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) : ℕ :=
  let regions := GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source
  let child := GeneralPaperStoredDominantInstallation.run model S A chosen source regions.inner
  let fieldWork := (extract S A regions.outer).2
  child.values.elim 0 (fun inner => GeneralPaperOuterAttachmentLifetime.window model S A A (regions.work + fieldWork)
      (canonical A regions.boundary) inner 0) +
    GeneralPaperOuterFieldCursorLifetime.window model S A regions.boundary +
    parentWindow S A A regions.work child.work fieldWork (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).work

theorem dominant_bound {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n)
    (hA : 0 < A) (hInnerCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A)
    (hOuterCap : (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum +
      (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A) :
    dominantWindow model S A chosen source ≤ profile model S A (GeneralPaperCompleteOuterPreparationWork.dominantBound model S A chosen source) := by
  let regions := GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source
  let fieldWork := (extract S A regions.outer).2
  let P := GeneralPaperCompleteOuterPreparationWork.dominantBound model S A chosen source
  have hPrice := GeneralPaperCompleteOuterPreparationWork.dominant_work model S A chosen source hA hInnerCap hOuterCap
  obtain ⟨inner,hInner,_,hChildWork,_,_⟩ := GeneralPaperStoredDominantInstallation.source model S A 0 chosen source [] hA
    (by simpa only [Nat.zero_add] using hInnerCap)
  simp only [List.append_nil] at hInner hChildWork
  have hActual : (GeneralPaperStoredDominantInstallation.run model S A chosen source
      (GeneralPaperStoredDominantOuterConstruction.layout model S A chosen source).inner).values = some inner := hInner
  have hChild : inner.work = (GeneralPaperStoredDominantInstallation.run model S A chosen source regions.inner).work := hChildWork
  have hRun : (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).work =
      (GeneralPaperStoredOuterAttachment.finish model S A A (regions.work + fieldWork) (canonical A regions.boundary) inner 0).work := by
    dsimp only [regions,fieldWork]
    simp only [GeneralPaperStoredDominantOuterConstruction.run,hActual,GeneralPaperStoredDominantOuterConstruction.fields_source]
  have hBound : (GeneralPaperStoredOuterAttachment.finish model S A A (regions.work + fieldWork)
      (canonical A regions.boundary) inner 0).work ≤ P := by rw [← hRun]; exact hPrice
  have hBoundary : regions.boundary = (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum :=
    GeneralPaperMeasuredTwoPoolLayout.boundary model S A A _ _
  have hCap : regions.boundary + (GeneralPaperEqualMeasuredSelectedPlan.header model S A).sizes.sum < 2 ^ A := by
    rw [hBoundary]; exact hOuterCap
  have hAttach := GeneralPaperOuterAttachmentLifetime.window_bound model S A A regions.boundary (regions.work + fieldWork) 0 P inner
    hA le_rfl (by positivity) hCap hBound
  have hFields := (GeneralPaperOuterFieldCursorLifetime.constructed model S A regions.boundary hA hCap).2
  have hPrices : regions.work + (GeneralPaperStoredDominantInstallation.run model S A chosen source regions.inner).work + fieldWork ≤
      (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).work := by
    rw [hRun,← hChild]
    change _ ≤ (regions.work + fieldWork) + inner.work + _ + _ + _ + _
    omega
  have hParent := parent_bound model S A A P regions.work
    (GeneralPaperStoredDominantInstallation.run model S A chosen source regions.inner).work fieldWork
    (GeneralPaperStoredDominantOuterConstruction.run model S A chosen source).work le_rfl hPrice hPrices
  dsimp only [dominantWindow]
  rw [hActual]
  simp only [Option.elim_some]
  exact Nat.add_le_add (Nat.add_le_add hAttach hFields) hParent

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A P r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hP : Small P L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (P x)) r L := by
  have hHeader : Polylog (fun x => (GeneralPaperEqualMeasuredSelectedPlan.header model (S x) (A x)).sizes.sum) L := by
    simp only [GeneralPaperEqualMeasuredSelectedPlan.header_sum,GeneralPaperEqualSelectedDescription.header,
      GeneralPaperEncodedScalarStorage.fields,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,Nat.one_mul,Nat.zero_add,Nat.add_zero]
    have hAP := polylog_of_tight hA
    have hASmall := small_of_tight hA hL
    fun_prop
  have hAttach := GeneralPaperOuterAttachmentLifetime.profile_rate model hFast S A
    (fun x => (GeneralPaperEqualMeasuredSelectedPlan.header model (S x) (A x)).sizes.sum) P r L hL hr hS hA (rate_mono hHeader hr) hP hrSmall
  have hFields := GeneralPaperOuterFieldCursorLifetime.profile_rate model hFast S A L hL hS hA
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S A P L hL hS hA hP
  have hMeta : Polylog (fun x => GeneralPaperOuterFieldCursorLifetime.profile model (S x) (A x) + unit model (S x) (A x) (P x)) L :=
    polylog_add _ _ L hL hFields hUnit
  unfold profile
  simpa only [Nat.add_assoc] using bound_add _ _ r L hL hAttach (rate_mono hMeta hr)

end Blotto.GeneralPaperOuterConstructionLifetime
