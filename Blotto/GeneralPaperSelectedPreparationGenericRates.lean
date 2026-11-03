import Blotto.GeneralPaperUniformSmallComposition

/-! The complete selected stored-construction reserve has a rate on any
parameter domain. The preparation word and native source may vary together;
no hidden constant is allowed to depend on the chosen coefficient. -/
namespace Blotto.GeneralPaperSelectedPreparationGenericRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout (innerWidth)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

theorem combined_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S r L n k : α → ℕ) (v : (x : α) → RationalFieldSelector (n x)) (budget : α → ℚ)
    (sources : (x : α) → Sampler (v x) (k x) (budget x))
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L)
    (hA : Tight (fun x => (sources x).address) L)
    (hExtent : Bound (fun x => GeneralPaperEqualSelectedDescription.footprint (sources x)) r L)
    (hrSmall : Small r L)
    (hInnerCap : ∀ x,(GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum < 2 ^ innerWidth (sources x))
    (hOuterCap : ∀ x,(GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum < 2 ^ (sources x).address) :
    Bound (fun x => GeneralPaperSelectedOuterInputLifetime.combinedBound model (S x) (sources x)) r L := by
  let I := fun x => innerWidth (sources x)
  let A := fun x => (sources x).address
  let Bi := fun x => (GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)).sizes.sum
  let Bo := fun x => (GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)).sizes.sum
  let P := fun x => GeneralPaperCompleteSelectedPreparationWork.bound model (S x) (sources x)
  have hI : Tight I L := by
    obtain ⟨C,hC⟩ := hA
    exact ⟨C,fun x => (GeneralPaperCompleteSelectedPreparationWork.inner_width_le (sources x)).trans (hC x)⟩
  have hBi : Bound Bi r L := by
    apply dominated hExtent
    intro x
    dsimp only [Bi,GeneralPaperEqualMeasuredLayout.inner]
    rw [GeneralPaperEqualMeasuredSelectedPlan.branch_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  have hBo : Bound Bo r L := by
    apply dominated hExtent
    intro x
    dsimp only [Bo,GeneralPaperEqualMeasuredLayout.outer]
    rw [GeneralPaperEqualMeasuredSelectedPlan.header_sum]
    unfold GeneralPaperEqualSelectedDescription.footprint
    omega
  have hWork : Bound P r L := GeneralPaperCompleteSelectedPreparationWork.rate model hFast S r L n k v budget sources hL hr hS hA hExtent
  have hP := bound_small hL hWork hrSmall
  have hLayout := GeneralPaperSelectedLayoutLifetimeRates.rate model hFast S r L n k v budget sources hL hr hS hA hExtent hrSmall
  have hCount := GeneralPaperHeaderCountLifetimeRates.profile_rate model hFast S I Bi r L hL hr hS hI hBi hrSmall
  have hInstall := GeneralPaperDirectoryInstallationLifetime.profile_rate model hFast S I Bi r L hL hr hS hI hBi hrSmall
  have hCollection := GeneralPaperReferenceCollectionLifetimeRates.profile_rate model hFast S I Bi r L hL hr hS hI hBi hrSmall
  have hInner := GeneralPaperMeasuredPlanLifetimeRates.bound_rate model hFast S I r L 1909 7578
    (fun x => GeneralPaperEqualMeasuredLayout.inner model (S x) (sources x)) hL hr hS hI
    (fun x => GeneralPaperSelectedTemporaryOwners.inner_good model (S x) (sources x)) hInnerCap hBi hrSmall
  have hOuter := GeneralPaperMeasuredPlanLifetimeRates.bound_rate model hFast S A r L 12 40
    (fun x => GeneralPaperEqualMeasuredLayout.outer model (S x) (sources x)) hL hr hS hA
    (fun x => GeneralPaperMeasuredRetainedPlanWork.header model (S x) _
      (GeneralPaperEqualMeasuredLayout.widths_positive (sources x)).2) hOuterCap hBo hrSmall
  have hCursor := GeneralPaperSamplerCursorLifetime.profile_rate model hFast S I Bi r L 168 496 hL hr hS hI hBi hrSmall
  have hAttach := GeneralPaperOuterConstructionLifetime.profile_rate model hFast S A P r L hL hr hS hA hP hrSmall
  have hUnit := GeneralPaperMeasuredPlanLifetimeRates.unit_rate model hFast S A P L hL hS hA hP
  exact bound_add _ _ r L hL
    (bound_add _ _ r L hL
      (bound_add _ _ r L hL
        (bound_add _ _ r L hL
          (bound_add _ _ r L hL (bound_add _ _ r L hL hLayout hCount) hInstall) hCollection)
        (bound_add _ _ r L hL hInner hOuter)) hCursor)
    (bound_add _ _ r L hL hAttach (rate_mono hUnit hr))

end Blotto.GeneralPaperSelectedPreparationGenericRates
