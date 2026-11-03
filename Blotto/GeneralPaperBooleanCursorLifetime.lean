import Blotto.GeneralPaperRulerCursorLifetime

/-! Complete concrete Boolean-cache cursor. The full pointer encoder
overhead is carried explicitly; all denominator, row-list and ruler child
conditions are discharged on actual measured streams. -/
namespace Blotto.GeneralPaperBooleanCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperRulerCursorLifetime (encoding)
open GeneralPaperBooleanRecordCursor (Field)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}
variable {prepared : GeneralPaperEqualPreparedCache.Prepared G l}

def childSpace (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) :
    Field → ℕ → List (Region A) → ℕ
  | .denominator,start,rest => GeneralPaperBooleanWordCursorLifetime.window model S A start source.denominator rest
  | .rows,start,rest => GeneralPaperBooleanRowCursorLifetime.rowsWindow model S A start source.rows rest
  | .ruler,start,rest => GeneralPaperRulerCursorLifetime.window model S A start source.ruler rest

theorem child_lifetime (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A (304 + encoding model S A)
      (GeneralPaperBooleanRecordCursor.schema model S A source) (GeneralPaperBooleanRecordCursor.parser model S A source)
      (childSpace model S A source) := by
  intro field start rest Q hCap hWork
  cases field with
  | denominator =>
    have h := GeneralPaperBooleanWordCursorLifetime.window_bound model S A start Q source.denominator rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 144 ≤ 304 + encoding model S A by omega)))
  | rows =>
    have h := GeneralPaperBooleanRowCursorLifetime.rows_bound model S A start Q source.rows rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 304 ≤ 304 + encoding model S A by omega)))
  | ruler =>
    have h := GeneralPaperRulerCursorLifetime.window_bound model S A start Q source.ruler rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 32 + encoding model S A ≤ 304 + encoding model S A by omega)))

def window (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared)
    (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 64 (GeneralPaperBooleanRecordCursor.parser model S A source)
    (GeneralPaperBooleanRecordCursor.schema model S A source) (GeneralPaperBooleanRecordCursor.child model S A source)
    (childSpace model S A source) GeneralPaperBooleanRecordCursor.fields rest

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperBooleanRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum + 1) * (400 + encoding model S A) * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperBooleanRecordCursor.schema model S A source)
      (GeneralPaperBooleanRecordCursor.child model S A source) (GeneralPaperBooleanRecordCursor.parser model S A source) := by
    intro field start rest
    have h := GeneralPaperBooleanRecordCursor.field_success model S A source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperBooleanRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | denominator => exact GeneralPaperEqualMeasuredPlanPositive.word model S A source.denominator hA
    | rows =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ _ hA (by omega)
        (fun row _ => GeneralPaperEqualMeasuredPlanPositive.row model S A row hA)
    | ruler =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ _ hA (by omega)
        (fun _ _ => GeneralPaperEqualMeasuredPlanPositive.empty S)
  have hCap' := hCap
  rw [GeneralPaperBooleanRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap'
  have h := GeneralPaperTrailingRecordCursorLifetime.window_bound model S A (304 + encoding model S A) Q
    (GeneralPaperBooleanRecordCursor.parser model S A source) (GeneralPaperBooleanRecordCursor.schema model S A source)
    (GeneralPaperBooleanRecordCursor.child model S A source) (childSpace model S A source)
    hCorrect (child_lifetime model S A source hA) hPos hA start 64 GeneralPaperBooleanRecordCursor.fields rest (by decide) hCap'
    (by simpa only [GeneralPaperBooleanRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanRecordCursor.plan] using hWork)
  have hCoeff : 304 + encoding model S A + 96 = 400 + encoding model S A := by omega
  rw [hCoeff] at h
  simpa only [window,GeneralPaperBooleanRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem lifetime (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A (400 + encoding model S A)
      (fun source : GeneralPaperEqualBooleanCache.Cache prepared => (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes)
      (GeneralPaperBooleanRecordCursor.run model S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

theorem actual (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualBooleanCache.Cache prepared)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum < 2 ^ A) :
    window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
      (GeneralPaperEqualMeasuredRetainedPlan.boolean model S A source).sizes.sum 136 (400 + encoding model S A) :=
  window_bound model S A start _ source rest hA hCap (GeneralPaperBooleanCacheCursorWork.boolean model S A start source rest hA hCap)

end Blotto.GeneralPaperBooleanCursorLifetime
