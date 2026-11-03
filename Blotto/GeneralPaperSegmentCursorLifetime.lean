import Blotto.GeneralPaperRecordCursorLifetimeRates

/-! Actual segment-record lifetime, with its scalar weight-array and two
matrix children instantiated. The trailing record, copied headers and all
parent prices coexist with complete child windows. -/
namespace Blotto.GeneralPaperSegmentCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperSegmentRecordCursor (Field)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 8192

def childSpace {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) : Field → ℕ → List (Region A) → ℕ
  | .weights,start,rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.rational source.weights rest
  | .left,start,rest => GeneralPaperMatrixCursorLifetime.window model S A start source.left rest
  | .right,start,rest => GeneralPaperMatrixCursorLifetime.window model S A start source.right rest

theorem child_lifetime {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ)
    (source : PreparedSegmentDescriptor l) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 112 (GeneralPaperSegmentRecordCursor.schema model S A source)
      (GeneralPaperSegmentRecordCursor.parser S A source) (childSpace model S A source) := by
  intro field start rest Q hCap hWork
  cases field with
  | weights =>
    exact (GeneralPaperRecordCursorLifetimeRates.raise model S A 48 112 _ _ _
      (GeneralPaperMappedCursorChildLifetime.rational_lifetime model S A hA) (by decide)) source.weights start rest Q hCap hWork
  | left => exact GeneralPaperMatrixCursorLifetime.window_bound model S A start Q source.left rest hA hCap hWork
  | right => exact GeneralPaperMatrixCursorLifetime.window_bound model S A start Q source.right rest hA hCap hWork

def window {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 32 (GeneralPaperSegmentRecordCursor.parser S A source)
    (GeneralPaperSegmentRecordCursor.schema model S A source) (GeneralPaperSegmentRecordCursor.child model S A source)
    (childSpace model S A source) GeneralPaperSegmentRecordCursor.fields rest

theorem window_bound {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start Q : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperSegmentRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum + 1) * 208 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperSegmentRecordCursor.schema model S A source)
      (GeneralPaperSegmentRecordCursor.child model S A source) (GeneralPaperSegmentRecordCursor.parser S A source) := by
    intro field start rest
    have h := GeneralPaperSegmentRecordCursor.field_success model S A source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperSegmentRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | weights =>
      exact GeneralPaperMeasuredPlanPositive.array model S A _ source.weights hA
        (fun j => GeneralPaperMeasuredPlanPositive.rational model S _)
    | left => exact GeneralPaperEqualMeasuredPlanPositive.matrix model S A source.left hA
    | right => exact GeneralPaperEqualMeasuredPlanPositive.matrix model S A source.right hA
  rw [GeneralPaperSegmentRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  exact GeneralPaperTrailingRecordCursorLifetime.window_bound model S A 112 Q
    (GeneralPaperSegmentRecordCursor.parser S A source) (GeneralPaperSegmentRecordCursor.schema model S A source)
    (GeneralPaperSegmentRecordCursor.child model S A source) (childSpace model S A source)
    hCorrect (child_lifetime model S A source hA) hPos hA start 32 GeneralPaperSegmentRecordCursor.fields rest (by decide) hCap
    (by simpa only [GeneralPaperSegmentRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperSegmentRecordCursor.plan] using hWork)

theorem lifetime {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 208
      (fun source : PreparedSegmentDescriptor l => (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes)
      (GeneralPaperSegmentRecordCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

theorem actual {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum < 2 ^ A) :
    window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
      (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum 72 208 :=
  window_bound model S A start _ source rest hA hCap (GeneralPaperPreparedCursorWork.segments model S A start source rest hA hCap)

theorem constructed {m r : ℕ} {l : RationalSegmentLottery m r} (model : RationalCostModel) (S A start : ℕ)
    (source : PreparedSegmentDescriptor l) (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum < 2 ^ A) :
    let parsed := GeneralPaperSegmentRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source)).1 ++ rest)
    parsed.values = some (GeneralPaperSegmentRecordCursor.expected model S A source start) ∧ parsed.remaining = rest ∧
      window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
        (GeneralPaperEqualMeasuredRetainedPlan.segments model S A source).sizes.sum 72 208 := by
  have h := GeneralPaperSegmentRecordCursor.success model S A start source rest
  exact ⟨h.1,h.2.1,actual model S A start source rest hA hCap⟩

end Blotto.GeneralPaperSegmentCursorLifetime
