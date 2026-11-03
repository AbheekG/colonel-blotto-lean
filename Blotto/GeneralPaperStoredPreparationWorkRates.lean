import Blotto.GeneralPaperStoredDirectoryPreparationWork

/-! Uniform rates for the complete count/installation passes and the
existing executed layout bound. Metadata widths contribute only logarithmic
factors; measured scalar area contributes once. These component rates do
not assert the still-open source-mapping or cursor price. -/
namespace Blotto.GeneralPaperStoredPreparationWorkRates
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

@[fun_prop]
theorem scalar_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredHeaderPreparationWork.scalarBound model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold GeneralPaperStoredHeaderPreparationWork.scalarBound
  fun_prop

@[fun_prop]
theorem encode_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredHeaderPreparationWork.encodeBound model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold GeneralPaperStoredHeaderPreparationWork.encodeBound GeneralPaperStoredWordEncoding.stepBound
  fun_prop

@[fun_prop]
theorem header_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredHeaderPreparationWork.perElement model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  unfold GeneralPaperStoredHeaderPreparationWork.perElement
  fun_prop

@[fun_prop]
theorem reference_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperStoredReferencePreparationWork.perElement model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  dsimp only [GeneralPaperStoredReferencePreparationWork.perElement,GeneralPaperStoredReferencePreparationWork.batchElement,
    GeneralPaperStoredReferenceReadWork.slotBound,GeneralPaperStoredReferenceReadWork.envelope,
    GeneralPaperStoredWordEncoding.stepBound]
  fun_prop (config := {maxSteps := 30000})

@[fun_prop]
theorem directory_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) :
    Bound (fun x => GeneralPaperStoredDirectoryPreparationWork.bound model (S x) (A x) (B x)) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hHeader : Polylog (fun x => GeneralPaperStoredHeaderPreparationWork.perElement model (S x) (A x)) L :=
    header_rate model hFast S A L hL hS hA
  have hReference : Polylog (fun x => GeneralPaperStoredReferencePreparationWork.perElement model (S x) (A x)) L :=
    reference_rate model hFast S A L hL hS hA
  unfold GeneralPaperStoredDirectoryPreparationWork.bound GeneralPaperStoredDirectoryPreparationWork.countBound
    GeneralPaperStoredDirectoryPreparationWork.installBound
  fun_prop (config := {maxSteps := 30000})

@[fun_prop]
theorem layout_step_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hS : Tight S L) (hA : Tight A L) :
    Polylog (fun x => GeneralPaperSequentialLayout.stepPrice model (S x) (A x)) L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hAS := small_of_tight hA hL
  unfold GeneralPaperSequentialLayout.stepPrice GeneralPaperStoredWordEncoding.stepBound
  fun_prop

theorem layout_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A start r L : α → ℕ) (plans : α → GeneralPaperMeasuredBlockPlan.Plan)
    (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x) (hS : Tight S L) (hA : Tight A L)
    (hWork : Bound (fun x => (plans x).work) r L)
    (hExtent : Bound (fun x => (plans x).sizes.sum) r L)
    (hPos : ∀ x,GeneralPaperMeasuredPlanPositive.Positive (plans x))
    (hAPos : ∀ x,0 < A x) (hCap : ∀ x,start x + (plans x).sizes.sum < 2 ^ A x) :
    Bound (fun x => (GeneralPaperMeasuredBlockLayout.run model (S x) (A x) (start x) (plans x)).2.2) r L := by
  have hSP := polylog_of_tight hS
  have hAP := polylog_of_tight hA
  have hStep := layout_step_rate model hFast S A L hL hS hA
  have hMajor : Bound (fun x => (plans x).work + ((plans x).sizes.sum + 1) * GeneralPaperSequentialLayout.stepPrice model (S x) (A x) + 64 * (S x + A x + 1)) r L := by fun_prop
  apply dominated hMajor
  intro x
  have h := GeneralPaperMeasuredBlockLayout.work model (S x) (A x) (start x) (plans x) (hAPos x) (hCap x)
  have hCount := GeneralPaperMeasuredPlanPositive.block_count (plans x) (hPos x)
  have hm := Nat.mul_le_mul_right (GeneralPaperSequentialLayout.stepPrice model (S x) (A x)) (Nat.add_le_add_right hCount 1)
  omega

end Blotto.GeneralPaperStoredPreparationWorkRates
