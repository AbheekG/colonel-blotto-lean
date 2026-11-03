import Blotto.GeneralPaperFrontRecordCursorLifetime

/-! Concrete endpoint-matrix extraction: every row lifetime is discharged
by the existing rational-array parser. Actual execution supplies the saved
price bound, and the same return preserves its directory and following stream. -/
namespace Blotto.GeneralPaperMatrixCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def window {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (rest : List (Region A)) : ℕ :=
  GeneralPaperFrontRecordCursorLifetime.window model S A 64 1 (GeneralPaperFieldDirectoryParsers.rational S A)
    (GeneralPaperMatrixFieldCursor.rowSchema model S A) (GeneralPaperMatrixFieldCursor.rowExpected model S A)
    (fun row start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational row rest)
    start source.data.toList rest

theorem window_bound {m r : ℕ} (model : RationalCostModel) (S A start Q : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperMatrixFieldCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum + 1) * 112 * unit model S A Q := by
  rw [GeneralPaperMatrixFieldCursor.plan,List.sum_cons] at hCap ⊢
  exact GeneralPaperFrontRecordCursorLifetime.array_bound model S A 48 Q (GeneralPaperFieldDirectoryParsers.rational S A)
    (GeneralPaperMatrixFieldCursor.rowSchema model S A) (GeneralPaperMatrixFieldCursor.rowExpected model S A)
    (fun row start rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational row rest)
    (GeneralPaperMappedCursorChildLifetime.rational_correct model S A)
    (GeneralPaperMappedCursorChildLifetime.rational_lifetime model S A hA)
    (fun row => GeneralPaperMeasuredPlanPositive.array model S A _ row hA
      (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)) hA start source.data.toList rest hCap
    (by simpa only [GeneralPaperMatrixFieldCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperMatrixFieldCursor.plan] using hWork)

theorem lifetime {m r : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 112
      (fun source : FixedArrayTable r (FixedArrayTable m ℚ) => (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes)
      (GeneralPaperMatrixFieldCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

def profile (model : RationalCostModel) (S A B : ℕ) : ℕ :=
  (B + 1) * 112 * unit model S A ((B + 1) * 40 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A)

theorem actual {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) :
    window model S A start source rest ≤ profile model S A
      (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum :=
  window_bound model S A start _ source rest hA hCap
    (GeneralPaperPreparedCursorWork.matrix model S A start source rest hA hCap)

theorem constructed {m r : ℕ} (model : RationalCostModel) (S A start : ℕ)
    (source : FixedArrayTable r (FixedArrayTable m ℚ)) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum < 2 ^ A) :
    let parsed := GeneralPaperMatrixFieldCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source)).1 ++ rest)
    parsed.values = some (GeneralPaperMatrixFieldCursor.expected model S A start source) ∧ parsed.remaining = rest ∧
      window model S A start source rest ≤ profile model S A (GeneralPaperEqualMeasuredRetainedPlan.matrix model S A source).sizes.sum := by
  have h := GeneralPaperMatrixFieldCursor.success model S A start source rest
  exact ⟨h.1,h.2.1,actual model S A start source rest hA hCap⟩

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => profile model (S x) (A x) (B x)) r L :=
  GeneralPaperScalarCursorLifetimeRates.generic_profile_rate model hFast S A B r L 40 112 hL hr hS hA hB hrSmall

end Blotto.GeneralPaperMatrixCursorLifetime
