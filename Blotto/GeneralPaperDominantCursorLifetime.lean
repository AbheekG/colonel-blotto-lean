import Blotto.GeneralPaperSamplerCursorLifetime

/-! Complete dominant-branch cursor. Its rational row and chosen-label
leaf discharge every scalar lifetime condition before the trailing record.
Actual executed work derives saved prices for the same directory return. -/
namespace Blotto.GeneralPaperDominantCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperStoredDominantCursor (Field)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def childSpace {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) :
    Field → ℕ → List (Region A) → ℕ
  | .row,start,rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational
      (GeneralPaperStoredDominantCursor.rowTable source) rest
  | .chosen,start,rest => GeneralPaperScalarComponentLifetime.leafWindow model S A start (.natural chosen) rest

theorem child_lifetime {n : ℕ} (model : RationalCostModel) (S A chosen : ℕ) (source : RationalResourceArray n) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 48 (GeneralPaperStoredDominantCursor.schema model S A chosen source)
      (GeneralPaperStoredDominantCursor.parser S A chosen source) (childSpace model S A chosen source) := by
  intro field start rest Q hCap hWork
  cases field with
  | row =>
    exact GeneralPaperMappedCursorChildLifetime.rational_lifetime model S A hA
      (GeneralPaperStoredDominantCursor.rowTable source) start rest Q hCap hWork
  | chosen =>
    simp only [GeneralPaperStoredDominantCursor.schema,GeneralPaperMeasuredBlockPlan.natural_data,
      List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
    simp only [GeneralPaperStoredDominantCursor.schema,GeneralPaperStoredDominantCursor.parser,
      GeneralPaperMeasuredBlockPlan.natural_data] at hWork
    have h := GeneralPaperScalarComponentLifetime.leaf_bound model S A start Q (.natural chosen) rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 16 ≤ 48 by decide)))

def window {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 32 (GeneralPaperStoredDominantCursor.parser S A chosen source)
    (GeneralPaperStoredDominantCursor.schema model S A chosen source) (GeneralPaperStoredDominantCursor.child model S A chosen source)
    (childSpace model S A chosen source) GeneralPaperStoredDominantCursor.fields rest

theorem window_bound {n : ℕ} (model : RationalCostModel) (S A start chosen Q : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperStoredDominantCursor.run S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)).work ≤ Q) :
    window model S A start chosen source rest ≤
      ((GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum + 1) * 144 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperStoredDominantCursor.schema model S A chosen source)
      (GeneralPaperStoredDominantCursor.child model S A chosen source) (GeneralPaperStoredDominantCursor.parser S A chosen source) := by
    intro field start rest
    have h := GeneralPaperStoredDominantCursor.field_success model S A chosen source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperStoredDominantCursor.schema model S A chosen source field,0 < size := by
    intro field
    cases field with
    | row =>
      exact GeneralPaperMeasuredPlanPositive.array model S A _ (GeneralPaperStoredDominantCursor.rowTable source) hA
        (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
    | chosen => exact GeneralPaperMeasuredPlanPositive.natural model S chosen
  rw [GeneralPaperStoredDominantCursor.plan_data,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  exact GeneralPaperTrailingRecordCursorLifetime.window_bound model S A 48 Q
    (GeneralPaperStoredDominantCursor.parser S A chosen source) (GeneralPaperStoredDominantCursor.schema model S A chosen source)
    (GeneralPaperStoredDominantCursor.child model S A chosen source) (childSpace model S A chosen source)
    hCorrect (child_lifetime model S A chosen source hA) hPos hA start 32 GeneralPaperStoredDominantCursor.fields rest (by decide) hCap
    (by simpa only [GeneralPaperStoredDominantCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperStoredDominantCursor.plan_data] using hWork)

theorem actual {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A) :
    window model S A start chosen source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
      (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum 48 144 :=
  window_bound model S A start chosen _ source rest hA hCap
    (GeneralPaperCompleteSamplerCursorWork.dominant model S A start chosen source rest hA hCap)

theorem constructed {n : ℕ} (model : RationalCostModel) (S A start chosen : ℕ) (source : RationalResourceArray n)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum < 2 ^ A) :
    let parsed := GeneralPaperStoredDominantCursor.run S A chosen source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperStoredDominantCursor.plan model S A chosen source)).1 ++ rest)
    parsed.values = some (GeneralPaperStoredDominantCursor.expected model S A chosen source start) ∧ parsed.remaining = rest ∧
      window model S A start chosen source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
        (GeneralPaperStoredDominantCursor.plan model S A chosen source).sizes.sum 48 144 := by
  have h := GeneralPaperStoredDominantCursor.success model S A start chosen source rest
  exact ⟨h.1,h.2.1,actual model S A start chosen source rest hA hCap⟩

end Blotto.GeneralPaperDominantCursorLifetime
