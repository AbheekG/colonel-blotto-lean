import Blotto.GeneralPaperEqualFirstRealDispatch

/-! Actual current-paper equal-budget bit producer. Original input values
are rounded once at scale 256*n*2^k. The retained length array feeds exactly
one dominant/grouped continuation, with midpoint exponent k+5. Complete
storage/word/resource and all-branch joins remain subsequent obligations. -/
namespace Blotto.GeneralPaperEqualFirstBitDispatch
open GeneralPaperEqualFirstRounding (rounded)
open GeneralPaperEqualBitBranch (Prepared outputLaw)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def run {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) : Prepared (rounded true model W k values v hv) k budget × ℕ :=
  let raw := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity true model W 256 k (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values)
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = 2 * r.weight j := by
    intro j; rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]; rfl
  let actual := GeneralPaperEqualBitBranch.prepare model A k r budget lengths.1 hL
  (actual.1, raw.2 + lengths.2 + actual.2 + 128 * A + 128)

theorem original_regret {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hB : 0 < budget) :
    let p := (run model W A k values v hv budget).1
    Supported (budget : ℝ) (outputLaw model p) ∧
      regret v.values (budget : ℝ) (outputLaw model p) (outputLaw model p) ≤ 3 * (1 / (2 : ℝ) ^ k) / 64 := by
  let p := (run model W A k values v hv budget).1
  have h := GeneralPaperEqualBitBranch.rounded_regret model p hB
  have hd := GeneralPaperEqualFirstRounding.distance true model W k values v hv
  change GeneralPaperValuePerturbation.distance v.values (rounded true model W k values v hv).values ≤ _ at hd
  have ht := GeneralPaperValuePerturbation.regret_le_shift v.values (rounded true model W k values v hv).values
    (budget : ℝ) (by exact_mod_cast hB.le) (outputLaw model p) (outputLaw model p)
  have he : (0 : ℝ) ≤ 1 / (2 : ℝ) ^ k := by positivity
  change Supported (budget : ℝ) (outputLaw model p) ∧
    regret v.values (budget : ℝ) (outputLaw model p) (outputLaw model p) ≤ 3 * (1 / (2 : ℝ) ^ k) / 64
  exact ⟨h.1, by linarith only [h.2, hd, ht, he]⟩

theorem epsilon {n : ℕ} (model : RationalCostModel) (W A : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1) (budget : ℚ) (hB : 0 < budget) :
    let p := (run model W A (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv budget).1
    Supported (budget : ℝ) (outputLaw model p) ∧ regret v.values (budget : ℝ) (outputLaw model p) (outputLaw model p) ≤ (eps : ℝ) := by
  have h := original_regret model W A (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv budget hB
  have he := (GeneralPaperDyadicAccuracy.accuracy_bounds eps hp hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power] at he
  have he' : (1 / (2 : ℝ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent) ≤ (eps : ℝ) := by
    have hc : (((1 / (2 : ℚ) ^ (GeneralPaperDyadicAccuracy.prepare eps).exponent : ℚ) : ℝ)) ≤ (eps : ℝ) := by exact_mod_cast he
    simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_pow, Rat.cast_ofNat] using hc
  have hp' : (0 : ℝ) < eps := by exact_mod_cast hp
  dsimp only at h ⊢
  exact ⟨h.1, by linarith only [h.2, he', hp']⟩

end Blotto.GeneralPaperEqualFirstBitDispatch
