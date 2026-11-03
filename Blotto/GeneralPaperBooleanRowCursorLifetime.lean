import Blotto.GeneralPaperBooleanWordCursorLifetime

/-! Concrete labelled Boolean rows and their front-header list. Scalar
labels and complete stored words instantiate every child lifetime. -/
namespace Blotto.GeneralPaperBooleanRowCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperBooleanRowCursor (Field)
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192

def childSpace {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) :
    Field → ℕ → List (Region A) → ℕ
  | .label,start,rest => GeneralPaperScalarComponentLifetime.leafWindow model S A start (.natural source.1.val) rest
  | .word,start,rest => GeneralPaperBooleanWordCursorLifetime.window model S A start source.2 rest

theorem child_lifetime {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (source : Fin r × FixedBinaryWord w) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 144 (GeneralPaperBooleanRowCursor.schema model S A source)
      (GeneralPaperBooleanRowCursor.parser S A source) (childSpace model S A source) := by
  intro field start rest Q hCap hWork
  cases field with
  | label =>
    simp only [GeneralPaperBooleanRowCursor.schema,GeneralPaperMeasuredBlockPlan.natural_data,
      List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
    simp only [GeneralPaperBooleanRowCursor.schema,GeneralPaperBooleanRowCursor.parser,
      GeneralPaperMeasuredBlockPlan.natural_data] at hWork
    have h := GeneralPaperScalarComponentLifetime.leaf_bound model S A start Q (.natural source.1.val) rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 16 ≤ 144 by decide)))
  | word => exact GeneralPaperBooleanWordCursorLifetime.window_bound model S A start Q source.2 rest hA hCap hWork

def window {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : Fin r × FixedBinaryWord w) (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 16 (GeneralPaperBooleanRowCursor.parser S A source)
    (GeneralPaperBooleanRowCursor.schema model S A source) (GeneralPaperBooleanRowCursor.child model S A source)
    (childSpace model S A source) GeneralPaperBooleanRowCursor.fields rest

theorem window_bound {r w : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (source : Fin r × FixedBinaryWord w)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperBooleanRowCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.row model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes.sum + 1) * 240 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperBooleanRowCursor.schema model S A source)
      (GeneralPaperBooleanRowCursor.child model S A source) (GeneralPaperBooleanRowCursor.parser S A source) := by
    intro field start rest
    have h := GeneralPaperBooleanRowCursor.field_success model S A source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperBooleanRowCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | label => exact GeneralPaperMeasuredPlanPositive.natural model S source.1.val
    | word => exact GeneralPaperEqualMeasuredPlanPositive.word model S A source.2 hA
  rw [GeneralPaperBooleanRowCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  exact GeneralPaperTrailingRecordCursorLifetime.window_bound model S A 144 Q
    (GeneralPaperBooleanRowCursor.parser S A source) (GeneralPaperBooleanRowCursor.schema model S A source)
    (GeneralPaperBooleanRowCursor.child model S A source) (childSpace model S A source)
    hCorrect (child_lifetime model S A source hA) hPos hA start 16 GeneralPaperBooleanRowCursor.fields rest (by decide) hCap
    (by simpa only [GeneralPaperBooleanRowCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanRowCursor.plan] using hWork)

theorem lifetime {r w : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 240
      (fun source : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A source).sizes)
      (GeneralPaperBooleanRowCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

def rowsWindow {r w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : List (Fin r × FixedBinaryWord w))
    (rest : List (Region A)) : ℕ :=
  GeneralPaperFrontRecordCursorLifetime.window model S A 32 2 (GeneralPaperBooleanRowCursor.run S A)
    (fun row => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes) (GeneralPaperBooleanRowCursor.expected model S A)
    (fun row start rest => window model S A start row rest) start source rest

theorem rows_bound {r w : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (source : List (Fin r × FixedBinaryWord w))
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperBooleanRowCursor.rowsRun S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start
        (GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source)).1 ++ rest)).work ≤ Q) :
    rowsWindow model S A start source rest ≤
      ((GeneralPaperMeasuredListBlockPlan.run model S A 2 32 (GeneralPaperEqualMeasuredLeafPlans.row model S A) source).sizes.sum + 1) * 304 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A
      (fun row : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
      (GeneralPaperBooleanRowCursor.expected model S A) (GeneralPaperBooleanRowCursor.run S A) := by
    intro row start rest
    have h := GeneralPaperBooleanRowCursor.success model S A start row rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  rw [GeneralPaperMeasuredListBlockPlan.data,List.singleton_append,List.sum_cons] at hCap ⊢
  exact GeneralPaperFrontRecordCursorLifetime.list_bound model S A 240 Q
    (GeneralPaperBooleanRowCursor.run S A)
    (fun row : Fin r × FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.row model S A row).sizes)
    (GeneralPaperBooleanRowCursor.expected model S A) (fun row start rest => window model S A start row rest)
    hCorrect (lifetime model S A hA) (fun row => GeneralPaperEqualMeasuredPlanPositive.row model S A row hA) hA start source rest hCap
    (by simpa only [GeneralPaperBooleanRowCursor.rowsRun,GeneralPaperMeasuredBlockLayout.run,
      GeneralPaperMeasuredListBlockPlan.data,List.singleton_append] using hWork)

end Blotto.GeneralPaperBooleanRowCursorLifetime
