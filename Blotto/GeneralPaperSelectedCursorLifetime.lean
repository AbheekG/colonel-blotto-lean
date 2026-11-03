import Blotto.GeneralPaperDominantCursorLifetime

/-! Erased observers of the actual selected inner cursor. Its input is
the executed two-pool layout's inner stream, at the branch's own reference
width. Both concrete branches derive every child and saved-price bound. -/
namespace Blotto.GeneralPaperSelectedCursorLifetime
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualMeasuredLayout (innerWidth inner)
open GeneralPaperRulerCursorLifetime (encoding)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 8192

def parsed {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : GeneralPaperFieldDirectoryParsers.Result (innerWidth source) :=
  match source with
  | ⟨.dominant chosen heavy row correct,A,hAddress⟩ =>
    GeneralPaperStoredDominantCursor.run S A chosen.val row
      (GeneralPaperEqualMeasuredLayout.run model S
        (⟨.dominant chosen heavy row correct,A,hAddress⟩ : Sampler v k budget)).inner
  | ⟨.grouped small sampler hK hB,A,hAddress⟩ =>
    GeneralPaperSamplerRecordCursor.run model S sampler.address sampler
      (GeneralPaperEqualMeasuredLayout.run model S
        (⟨.grouped small sampler hK hB,A,hAddress⟩ : Sampler v k budget)).inner

def window {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  match source with
  | ⟨.dominant chosen _ row _,A,_⟩ => GeneralPaperDominantCursorLifetime.window model S A 0 chosen.val row []
  | ⟨.grouped _ sampler _ _,_,_⟩ => GeneralPaperSamplerCursorLifetime.window model S sampler.address 0 sampler []

def bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperRecordCursorLifetimeRates.profile model S (innerWidth source) (inner model S source).sizes.sum
    168 (496 + encoding model S (innerWidth source))

theorem inner_stream {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    (GeneralPaperEqualMeasuredLayout.run model S source).inner =
      (GeneralPaperMeasuredBlockLayout.run model S (innerWidth source) 0 (inner model S source)).1 := rfl

theorem same_return {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget) :
    (parsed model S source).values = some (GeneralPaperSelectedTemporaryOwners.directory model S source) ∧
      (parsed model S source).remaining = [] := by
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      have h := GeneralPaperStoredDominantCursor.success model S A 0 chosen.val row []
      have hPair := And.intro h.1 h.2.1
      simpa only [parsed,inner_stream,GeneralPaperSelectedTemporaryOwners.directory,List.append_nil,
        innerWidth,GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredSelectedPlan.branch,
        GeneralPaperStoredDominantCursor.plan,GeneralPaperStoredDominantCursor.rowTable] using hPair
    | grouped small sampler hK hB =>
      have h := GeneralPaperSamplerRecordCursor.success model S sampler.address 0 sampler []
      have hPair := And.intro h.1 h.2.1
      simpa only [parsed,inner_stream,GeneralPaperSelectedTemporaryOwners.directory,List.append_nil,
        innerWidth,GeneralPaperEqualMeasuredLayout.inner,GeneralPaperEqualMeasuredSelectedPlan.branch] using hPair

theorem window_bound {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ}
    (model : RationalCostModel) (S : ℕ) (source : Sampler v k budget)
    (hCap : (inner model S source).sizes.sum < 2 ^ innerWidth source) :
    window model S source ≤ bound model S source := by
  have hI := (GeneralPaperEqualMeasuredLayout.widths_positive source).1
  cases source with
  | mk branch A hAddress =>
    cases branch with
    | dominant chosen heavy row correct =>
      change (GeneralPaperStoredDominantCursor.plan model S A chosen.val row).sizes.sum < 2 ^ A at hCap
      change 1 ≤ A at hI
      let B := (GeneralPaperStoredDominantCursor.plan model S A chosen.val row).sizes.sum
      let Q := (B + 1) * 168 * GeneralPaperMeasuredPlanWorkAlgebra.unit model S A
      have hPrice := GeneralPaperCompleteSamplerCursorWork.dominant model S A 0 chosen.val row [] hI (by simpa only [Nat.zero_add] using hCap)
      have hCost : (GeneralPaperStoredDominantCursor.run S A chosen.val row
          ((GeneralPaperMeasuredBlockLayout.run model S A 0 (GeneralPaperStoredDominantCursor.plan model S A chosen.val row)).1 ++ [])).work ≤ Q :=
        hPrice.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 48 ≤ 168 by decide)))
      have h := GeneralPaperDominantCursorLifetime.window_bound model S A 0 chosen.val Q row [] hI
        (by simpa only [Nat.zero_add] using hCap) hCost
      change GeneralPaperDominantCursorLifetime.window model S A 0 chosen.val row [] ≤
        (B + 1) * (496 + encoding model S A) * GeneralPaperMeasuredPlanLifetimeAlgebra.unit model S A Q
      exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (show 144 ≤ 496 + encoding model S A by omega)))
    | grouped small sampler hK hB =>
      change (GeneralPaperEqualMeasuredRetainedPlan.sampler model S sampler.address sampler).sizes.sum < 2 ^ sampler.address at hCap
      exact GeneralPaperSamplerCursorLifetime.actual model S sampler.address 0 sampler [] hI
        (by simpa only [Nat.zero_add] using hCap)

theorem native_window_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    window model S source ≤ bound model S source :=
  window_bound model S source (GeneralPaperEqualMeasuredLayout.inner_capacity model W S k values v hv budget source)

theorem native_constructed {n : ℕ} (model : RationalCostModel) (W S k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    (parsed model S source).values = some (GeneralPaperSelectedTemporaryOwners.directory model S source) ∧
      (parsed model S source).remaining = [] ∧ window model S source ≤ bound model S source := by
  have h := same_return model S source
  exact ⟨h.1,h.2,native_window_bound model W S k values v hv budget source⟩

end Blotto.GeneralPaperSelectedCursorLifetime
