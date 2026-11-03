import Blotto.GeneralPaperFieldDirectoryStorage

/-! Uniform storage rates for the actual temporary layout/directory owners.
Extent is linear; address factors and saved price encodings are logarithmic.
The count-expanded directory can coexist with its source without multiplying
the largest scalar width by the number of blocks. -/
namespace Blotto.GeneralPaperMeasuredDirectoryStorageRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
open GeneralPaperMeasuredLayoutStorage
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem plan_rate {α : Type*} (S A B P r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hB : Bound B r L) (hP : Small P L) :
    Bound (fun x => planBound (S x) (A x) (B x) (P x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  unfold planBound
  fun_prop

@[fun_prop]
theorem regions_rate {α : Type*} (S A B r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hB : Bound B r L) : Bound (fun x => regionsBound (S x) (A x) (B x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  unfold regionsBound regionBound
  fun_prop

@[fun_prop]
theorem two_pool_rate {α : Type*} (S I A Bi Bo Pi Po P r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hI : Tight I L) (hA : Tight A L)
    (hBi : Bound Bi r L) (hBo : Bound Bo r L) (hPi : Small Pi L) (hPo : Small Po L) (hP : Small P L) :
    Bound (fun x => twoPoolBound (S x) (I x) (A x) (Bi x) (Bo x) (Pi x) (Po x) (P x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hiPlan := plan_rate S I Bi Pi r L hL hr hS hI hBi hPi
  have hoPlan := plan_rate S A Bo Po r L hL hr hS hA hBo hPo
  have hiRegions := regions_rate S I Bi r L hL hr hS hI hBi
  have hoRegions := regions_rate S A Bo r L hL hr hS hA hBo
  unfold twoPoolBound
  fun_prop

@[fun_prop]
theorem directory_rate {α : Type*} (S A B r L : α → ℕ)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hB : Bound B r L) :
    Bound (fun x => GeneralPaperFieldDirectoryStorage.bound (S x) (A x) (B x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  unfold GeneralPaperFieldDirectoryStorage.bound
  fun_prop

@[fun_prop]
theorem count_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperFieldDirectoryStorage.countBound model (S x) (A x) (B x)) r L := by
  have hSP := polylog_of_tight hS
  have hDirectory := directory_rate S A B r L hL hr hS hA hB
  have hAllWork := GeneralPaperStoredPreparationWorkRates.directory_rate model hFast S A B r L hL hr hS hA hB
  have hCountWork : Bound (fun x => GeneralPaperStoredDirectoryPreparationWork.countBound model (S x) (A x) (B x)) r L := by
    apply dominated hAllWork
    intro x
    unfold GeneralPaperStoredDirectoryPreparationWork.bound
    omega
  have hCountSmall := bound_small hL hCountWork hrSmall
  unfold GeneralPaperFieldDirectoryStorage.countBound
  fun_prop

end Blotto.GeneralPaperMeasuredDirectoryStorageRates
