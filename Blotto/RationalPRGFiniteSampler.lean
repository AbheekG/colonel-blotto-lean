import Blotto.RationalPRGPrograms
import Blotto.RationalLottoPaperProgram

/-! Both players have native rational, bounded fair-bit draws from normalized
PRG input. Independent player bit vectors define independent whole laws.
Final continuous-regret and full computational contracts are not asserted. -/

namespace Blotto.RationalPRGInput
open MeasureTheory

def richSample {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  i.richNativeSystem.paperSample K bits

def poorSample {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  i.poorNativeSystem.paperSample K bits

noncomputable def richSampleLaw {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : Mixed n := i.richNativeSystem.paperSampleLaw K
noncomputable def poorSampleLaw {n : ℕ} (i : RationalPRGInput n) (K : ℕ) : Mixed n := i.poorNativeSystem.paperSampleLaw K

theorem richSample_fullBudget {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget 1 (fun j => (i.richSample K bits j : ℝ)) := by
  have h := i.richNativeSystem.paperSample_fullBudget K bits
  have he : (i.richNativeSystem.B : ℝ) = 1 := by
    change ((1 : ℚ) : ℝ) = 1
    norm_num
  rw [he] at h
  exact h

theorem poorSample_fullBudget {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.b : ℝ) (fun j => (i.poorSample K bits j : ℝ)) := i.poorNativeSystem.paperSample_fullBudget K bits

theorem richSampleLaw_fullBudget {n : ℕ} (i : RationalPRGInput n) (K : ℕ) :
    ∀ᵐ x ∂(i.richSampleLaw K : Measure (Allocation n)), FullBudget 1 x := by
  have h := i.richNativeSystem.paperSampleLaw_fullBudget K
  have he : (i.richNativeSystem.B : ℝ) = 1 := by
    change ((1 : ℚ) : ℝ) = 1
    norm_num
  rw [he] at h
  exact h

theorem poorSampleLaw_fullBudget {n : ℕ} (i : RationalPRGInput n) (K : ℕ) :
    ∀ᵐ x ∂(i.poorSampleLaw K : Measure (Allocation n)), FullBudget (i.b : ℝ) x := i.poorNativeSystem.paperSampleLaw_fullBudget K

end Blotto.RationalPRGInput
