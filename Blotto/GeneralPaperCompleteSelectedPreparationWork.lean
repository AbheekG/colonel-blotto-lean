import Blotto.GeneralPaperCompleteOuterPreparationWork

/-! Both actual selected preparation branches have one complete majorant.
Native selected capacities are derived from the existing source contracts;
rates charge actual retained extent and preserve mixed address widths. -/
namespace Blotto.GeneralPaperCompleteSelectedPreparationWork
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperUnifiedDirectoryInstallation (Installed)
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperTwoPoolPreparationWork.bound model S (GeneralPaperEqualMeasuredLayout.innerWidth source) source.address
    (GeneralPaperEqualMeasuredLayout.inner model S source).sizes.sum
    (GeneralPaperEqualMeasuredLayout.outer model S source).sizes.sum

theorem inner_width_le {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (source : Sampler v k budget) :
    GeneralPaperEqualMeasuredLayout.innerWidth source ≤ source.address := by
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct => exact le_rfl
    | grouped small sampler hK hB =>
      change sampler.address ≤ A
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      omega

theorem work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (GeneralPaperStoredSelectedConstruction.run model S source).2 ≤ bound model S source := by
  have hInnerCap := GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget source
  have hOuterCap := GeneralPaperEqualMeasuredLayout.total_capacity model W S k values v hv budget source
  have hWidths := GeneralPaperEqualMeasuredLayout.widths_positive source
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change (GeneralPaperStoredDominantOuterConstruction.run model S A chosen.val row).work ≤ _
      exact GeneralPaperCompleteOuterPreparationWork.dominant_work model S A chosen.val row hWidths.2 hInnerCap hOuterCap
    | grouped small sampler hK hB =>
      dsimp only [GeneralPaperEqualSelectedSampler.baseReference] at hAddress
      subst A
      change (GeneralPaperStoredGroupedOuterConstruction.run model S sampler).work ≤ _
      exact GeneralPaperCompleteOuterPreparationWork.grouped_work model S sampler hInnerCap hOuterCap

theorem returned_work {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget)
    (returned : Installed source.address) (hReturn : (GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned) :
    returned.work ≤ bound model S source := by
  obtain ⟨actual,hActual,hWork,_⟩ := GeneralPaperStoredSelectedConstruction.source model W S k values v hv budget source
  have hSame : actual = returned := Option.some.inj (hActual.symm.trans hReturn)
  rw [← hSame,hWork]
  exact work model W S k values v hv budget source

theorem constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    ∃ returned : Installed source.address,(GeneralPaperStoredSelectedConstruction.run model S source).1 = some returned ∧
      returned.work = (GeneralPaperStoredSelectedConstruction.run model S source).2 ∧ returned.work ≤ bound model S source ∧
      GeneralPaperStoredSelectedConstruction.Contract model source.address returned source.branch := by
  obtain ⟨returned,hReturn,hWork,hContract⟩ := GeneralPaperStoredSelectedConstruction.source model W S k values v hv budget source
  exact ⟨returned,hReturn,hWork,returned_work model W S k values v hv budget source returned hReturn,hContract⟩

theorem rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S r L n k : α → ℕ) (v : (x : α) → RationalFieldSelector (n x)) (budget : α → ℚ)
    (sources : (x : α) → Sampler (v x) (k x) (budget x))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L)
    (hA : Tight (fun x => (sources x).address) L)
    (hExtent : Bound (fun x => GeneralPaperEqualSelectedDescription.footprint (sources x)) r L) :
    Bound (fun x => bound model (S x) (sources x)) r L := by
  have hI : Tight (fun x => GeneralPaperEqualMeasuredLayout.innerWidth (sources x)) L := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨C,fun x => (inner_width_le (sources x)).trans (hC x)⟩
  have hBi : Bound (fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum) r L := by
    apply dominated hExtent
    intro x
    dsimp only [GeneralPaperEqualMeasuredLayout.inner]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  have hBo : Bound (fun x => (GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum) r L := by
    apply dominated hExtent
    intro x
    dsimp only [GeneralPaperEqualMeasuredLayout.outer]
    rw [GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  exact GeneralPaperTwoPoolPreparationWork.rate model hFast S
    (fun x => GeneralPaperEqualMeasuredLayout.innerWidth (sources x)) (fun x => (sources x).address)
    (fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum)
    (fun x => (GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum) r L hL hr hS hI hA hBi hBo

end Blotto.GeneralPaperCompleteSelectedPreparationWork
