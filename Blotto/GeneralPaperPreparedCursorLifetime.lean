import Blotto.GeneralPaperRouteCursorLifetime

/-! Complete prepared-cache cursor with every concrete child lifetime
discharged. Exact existing return/suffix and executed work join its full
record window, preserving the single original-budget leaf. -/
namespace Blotto.GeneralPaperPreparedCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperRetainedScalarValue (Scalar)
open GeneralPaperPreparedRecordCursor (Field)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def childSpace (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) :
    Field → ℕ → List (Region A) → ℕ
  | .routes,start,rest => GeneralPaperRouteCursorLifetime.arrayWindow model S A start source.routes.table rest
  | .segments,start,rest => GeneralPaperSegmentCursorLifetime.window model S A start source.segments rest
  | .counts,start,rest => GeneralPaperScalarCursorLifetimeRates.window model S A start Scalar.natural source.counts rest
  | .controls,start,rest => GeneralPaperScalarComponentLifetime.naturalWindow model S A start (GeneralPaperPreparedRecordCursor.controls source) rest
  | .budget,start,rest => GeneralPaperScalarComponentLifetime.leafWindow model S A start (.rational source.budget) rest

theorem child_lifetime (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 208 (GeneralPaperPreparedRecordCursor.schema model S A source)
      (GeneralPaperPreparedRecordCursor.parser S A source) (childSpace model S A source) := by
  intro field start rest Q hCap hWork
  cases field with
  | routes =>
    have h := GeneralPaperRouteCursorLifetime.array_bound model S A start Q source.routes.table rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 128 ≤ 208 by decide)))
  | segments => exact GeneralPaperSegmentCursorLifetime.window_bound model S A start Q source.segments rest hA hCap hWork
  | counts =>
    exact (GeneralPaperRecordCursorLifetimeRates.raise model S A 48 208 _ _ _
      (GeneralPaperMappedCursorChildLifetime.natural_lifetime model S A hA) (by decide)) source.counts start rest Q hCap hWork
  | controls =>
    have h := GeneralPaperScalarComponentLifetime.natural_bound model S A start Q (GeneralPaperPreparedRecordCursor.controls source) rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 48 ≤ 208 by decide)))
  | budget =>
    simp only [GeneralPaperPreparedRecordCursor.schema,GeneralPaperMeasuredBlockPlan.rational_data,
      List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
    simp only [GeneralPaperPreparedRecordCursor.parser,GeneralPaperPreparedRecordCursor.schema,
      GeneralPaperMeasuredBlockPlan.rational_data] at hWork
    have h := GeneralPaperScalarComponentLifetime.leaf_bound model S A start Q (.rational source.budget) rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 16 ≤ 208 by decide)))

def window (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 64 (GeneralPaperPreparedRecordCursor.parser S A source)
    (GeneralPaperPreparedRecordCursor.schema model S A source) (GeneralPaperPreparedRecordCursor.child model S A source)
    (childSpace model S A source) GeneralPaperPreparedRecordCursor.fields rest

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperPreparedRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum + 1) * 304 * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperPreparedRecordCursor.schema model S A source)
      (GeneralPaperPreparedRecordCursor.child model S A source) (GeneralPaperPreparedRecordCursor.parser S A source) := by
    intro field start rest
    have h := GeneralPaperPreparedRecordCursor.field_success model S A source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperPreparedRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | routes =>
      exact GeneralPaperMeasuredPlanPositive.array model S A _ source.routes.table hA
        (fun j => GeneralPaperEqualMeasuredPlanPositive.route model S A _ hA)
    | segments => exact GeneralPaperEqualMeasuredPlanPositive.segments model S A source.segments hA
    | counts =>
      exact GeneralPaperMeasuredPlanPositive.array model S A _ source.counts hA
        (fun j => GeneralPaperMeasuredPlanPositive.natural model S _)
    | controls =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
        (fun value _ => GeneralPaperMeasuredPlanPositive.natural model S value)
    | budget => exact GeneralPaperMeasuredPlanPositive.rational model S source.budget
  rw [GeneralPaperPreparedRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap ⊢
  exact GeneralPaperTrailingRecordCursorLifetime.window_bound model S A 208 Q
    (GeneralPaperPreparedRecordCursor.parser S A source) (GeneralPaperPreparedRecordCursor.schema model S A source)
    (GeneralPaperPreparedRecordCursor.child model S A source) (childSpace model S A source)
    hCorrect (child_lifetime model S A source hA) hPos hA start 64 GeneralPaperPreparedRecordCursor.fields rest (by decide) hCap
    (by simpa only [GeneralPaperPreparedRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperPreparedRecordCursor.plan] using hWork)

theorem lifetime (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A 304
      (fun source : GeneralPaperEqualPreparedCache.Prepared G l => (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes)
      (GeneralPaperPreparedRecordCursor.run S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

theorem actual (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
      (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum 104 304 :=
  window_bound model S A start _ source rest hA hCap (GeneralPaperPreparedCursorWork.prepared model S A start source rest hA hCap)

theorem constructed (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualPreparedCache.Prepared G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum < 2 ^ A) :
    let parsed := GeneralPaperPreparedRecordCursor.run S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source)).1 ++ rest)
    parsed.values = some (GeneralPaperPreparedRecordCursor.expected model S A source start) ∧ parsed.remaining = rest ∧
      window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
        (GeneralPaperEqualMeasuredRetainedPlan.prepared model S A source).sizes.sum 104 304 := by
  have h := GeneralPaperPreparedRecordCursor.success model S A start source rest
  exact ⟨h.1,h.2.1,actual model S A start source rest hA hCap⟩

end Blotto.GeneralPaperPreparedCursorLifetime
