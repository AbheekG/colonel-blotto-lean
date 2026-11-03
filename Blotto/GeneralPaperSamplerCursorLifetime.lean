import Blotto.GeneralPaperBooleanCursorLifetime

/-! Complete grouped-sampler cursor lifetime: prepared cache, Boolean
cache, exponent/address controls and final record. Actual execution derives
all saved-price bounds. The pointer encoder overhead has a uniform polylog
rate and does not multiply original scalar precision. -/
namespace Blotto.GeneralPaperSamplerCursorLifetime
open GeneralPaperSequentialLayout (Region)
open GeneralPaperMeasuredPlanLifetimeAlgebra (unit)
open GeneralPaperRulerCursorLifetime (encoding)
open GeneralPaperSamplerRecordCursor (Field)
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192
variable {n m r : ℕ} {G : RationalProportionalGroups n m} {l : RationalSegmentLottery m r}

def childSpace (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) :
    Field → ℕ → List (Region A) → ℕ
  | .prepared,start,rest => GeneralPaperPreparedCursorLifetime.window model S A start source.prepared rest
  | .boolean,start,rest => GeneralPaperBooleanCursorLifetime.window model S A start source.categorical rest
  | .controls,start,rest => GeneralPaperScalarComponentLifetime.naturalWindow model S A start (GeneralPaperSamplerRecordCursor.controls source) rest

theorem child_lifetime (model : RationalCostModel) (S A : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A (400 + encoding model S A)
      (GeneralPaperSamplerRecordCursor.schema model S A source) (GeneralPaperSamplerRecordCursor.parser model S A source)
      (childSpace model S A source) := by
  intro field start rest Q hCap hWork
  cases field with
  | prepared =>
    have h := GeneralPaperPreparedCursorLifetime.window_bound model S A start Q source.prepared rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 304 ≤ 400 + encoding model S A by omega)))
  | boolean => exact GeneralPaperBooleanCursorLifetime.window_bound model S A start Q source.categorical rest hA hCap hWork
  | controls =>
    have h := GeneralPaperScalarComponentLifetime.natural_bound model S A start Q (GeneralPaperSamplerRecordCursor.controls source) rest hA hCap hWork
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 48 ≤ 400 + encoding model S A by omega)))

def window (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) : ℕ :=
  GeneralPaperTrailingRecordCursorLifetime.window model S A start 64 (GeneralPaperSamplerRecordCursor.parser model S A source)
    (GeneralPaperSamplerRecordCursor.schema model S A source) (GeneralPaperSamplerRecordCursor.child model S A source)
    (childSpace model S A source) GeneralPaperSamplerRecordCursor.fields rest

theorem window_bound (model : RationalCostModel) (S A start Q : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A)
    (hWork : (GeneralPaperSamplerRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)).work ≤ Q) :
    window model S A start source rest ≤
      ((GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum + 1) * (496 + encoding model S A) * unit model S A Q := by
  have hCorrect : GeneralPaperChildCursorWork.Correct model S A (GeneralPaperSamplerRecordCursor.schema model S A source)
      (GeneralPaperSamplerRecordCursor.child model S A source) (GeneralPaperSamplerRecordCursor.parser model S A source) := by
    intro field start rest
    have h := GeneralPaperSamplerRecordCursor.field_success model S A source field start rest
    exact ⟨h.1,h.2.1,h.2.2.1⟩
  have hPos : ∀ field,∀ size ∈ GeneralPaperSamplerRecordCursor.schema model S A source field,0 < size := by
    intro field
    cases field with
    | prepared => exact GeneralPaperEqualMeasuredPlanPositive.prepared model S A source.prepared hA
    | boolean => exact GeneralPaperEqualMeasuredPlanPositive.boolean model S A source.categorical hA
    | controls =>
      exact GeneralPaperMeasuredPlanPositive.list model S A 1 32 _ _ hA (by omega)
        (fun value _ => GeneralPaperMeasuredPlanPositive.natural model S value)
  have hCap' := hCap
  rw [GeneralPaperSamplerRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] at hCap'
  have h := GeneralPaperTrailingRecordCursorLifetime.window_bound model S A (400 + encoding model S A) Q
    (GeneralPaperSamplerRecordCursor.parser model S A source) (GeneralPaperSamplerRecordCursor.schema model S A source)
    (GeneralPaperSamplerRecordCursor.child model S A source) (childSpace model S A source)
    hCorrect (child_lifetime model S A source hA) hPos hA start 64 GeneralPaperSamplerRecordCursor.fields rest (by decide) hCap'
    (by simpa only [GeneralPaperSamplerRecordCursor.run,GeneralPaperMeasuredBlockLayout.run,GeneralPaperSamplerRecordCursor.plan] using hWork)
  have hCoeff : 400 + encoding model S A + 96 = 496 + encoding model S A := by omega
  rw [hCoeff] at h
  simpa only [window,GeneralPaperSamplerRecordCursor.plan,List.sum_append,List.sum_cons,List.sum_nil,Nat.add_zero] using h

theorem lifetime (model : RationalCostModel) (S A : ℕ) (hA : 0 < A) :
    GeneralPaperChildDirectoryLifetime.Lifetime model S A (496 + encoding model S A)
      (fun source : GeneralPaperEqualStoredBitSampler.Sampler G l => (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes)
      (GeneralPaperSamplerRecordCursor.run model S A) (fun source start rest => window model S A start source rest) := by
  intro source start rest Q hCap hWork
  exact window_bound model S A start Q source rest hA hCap hWork

theorem actual (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
      (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum 168 (496 + encoding model S A) :=
  window_bound model S A start _ source rest hA hCap (GeneralPaperCompleteSamplerCursorWork.sampler model S A start source rest hA hCap)

theorem constructed (model : RationalCostModel) (S A start : ℕ) (source : GeneralPaperEqualStoredBitSampler.Sampler G l)
    (rest : List (Region A)) (hA : 0 < A)
    (hCap : start + (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum < 2 ^ A) :
    let parsed := GeneralPaperSamplerRecordCursor.run model S A source
      ((GeneralPaperMeasuredBlockLayout.run model S A start (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source)).1 ++ rest)
    parsed.values = some (GeneralPaperSamplerRecordCursor.expected model S A source start) ∧ parsed.remaining = rest ∧
      window model S A start source rest ≤ GeneralPaperRecordCursorLifetimeRates.profile model S A
        (GeneralPaperEqualMeasuredRetainedPlan.sampler model S A source).sizes.sum 168 (496 + encoding model S A) := by
  have h := GeneralPaperSamplerRecordCursor.success model S A start source rest
  exact ⟨h.1,h.2.1,actual model S A start source rest hA hCap⟩

theorem profile_rate {α : Type*} (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model)
    (S A B r L : α → ℕ) (Cw Cs : ℕ) (hL : ∀ x,1 ≤ L x) (hr : ∀ x,1 ≤ r x)
    (hS : Tight S L) (hA : Tight A L) (hB : Bound B r L) (hrSmall : Small r L) :
    Bound (fun x => GeneralPaperRecordCursorLifetimeRates.profile model (S x) (A x) (B x) Cw (Cs + encoding model (S x) (A x))) r L := by
  have hBase := GeneralPaperScalarCursorLifetimeRates.generic_profile_rate model hFast S A B r L Cw 1 hL hr hS hA hB hrSmall
  have hEncoding := GeneralPaperHeaderCountLifetimeRates.encoding_rate model hFast S A L hL hS hA
  have hFactor : Polylog (fun x => Cs + encoding model (S x) (A x)) L := by
    dsimp only [encoding]
    fun_prop
  have h := bound_mul_polylog _ _ r L hBase hFactor
  convert h using 1
  funext x
  dsimp only [GeneralPaperRecordCursorLifetimeRates.profile]
  ring

end Blotto.GeneralPaperSamplerCursorLifetime
