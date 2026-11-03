import Blotto.GeneralPaperBooleanBitCursorLifetime

/-! The existing stored-word cursor composes a complete bit-list cursor
and its trailing record; every child condition is discharged. -/
namespace Blotto.GeneralPaperBooleanWordCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 8192

def window {w : ℕ} (model : RationalCostModel) (S A start : ℕ) (source : FixedBinaryWord w) (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 16
    (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsRun S A source.bits)
    (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
    (fun _ start => GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits)
    (fun _ start rest => GeneralPaperBooleanBitCursorLifetime.window model S A start source.bits rest) [()] rest

theorem window_bound {w : ℕ} (model : RationalCostModel) (S A start Q : ℕ) (source : FixedBinaryWord w)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperBooleanWordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredLeafPlans.word model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes.sum + 1) * 144 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A
      (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
      (fun _ start => GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits)
      (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsRun S A source.bits) := by
    intro value start rest
    have h := GeneralPaperBooleanWordCursor.bits_success model S A start source.bits rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hLife : GeneralPaperChildDirectoryLifetime.Lifetime model S A 48
      (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
      (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsRun S A source.bits)
      (fun _ start rest => GeneralPaperBooleanBitCursorLifetime.window model S A start source.bits rest) := by
    intro value start rest Q hCap hWork
    exact GeneralPaperBooleanBitCursorLifetime.window_bound model S A start Q source.bits rest hA hCap hWork
  have hPos : ∀ value : Unit,∀ size ∈ GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits,0 < size := by
    intro value
    exact GeneralPaperMeasuredPlanPositive.list model S A 2 32 _ source.bits hA (by omega)
      (fun _ _ => GeneralPaperEqualMeasuredPlanPositive.tag S)
  rw [GeneralPaperBooleanWordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  exact GeneralPaperTrailingRecordCursorLifetime.window_bound model S A 48 Q
    (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsRun S A source.bits)
    (fun _ : Unit => GeneralPaperBooleanWordCursor.bitsSchema model S A source.bits)
    (fun _ start => GeneralPaperBooleanWordCursor.bitsExpected model S A start source.bits)
    (fun _ start rest => GeneralPaperBooleanBitCursorLifetime.window model S A start source.bits rest)
    hCorrect hLife hPos hA start 16 [()] rest (by decide) hCap
    (by simpa only [GeneralPaperBooleanWordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperBooleanWordCursor.plan] using hWork)

theorem lifetime {w : ℕ} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 144
      (fun source : FixedBinaryWord w => (GeneralPaperEqualMeasuredLeafPlans.word model S A source).sizes)
      (GeneralPaperBooleanWordCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

end Blotto.GeneralPaperBooleanWordCursorLifetime
