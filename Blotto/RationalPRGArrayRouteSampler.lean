import Blotto.RationalLottoArrayRouteSampler
import Blotto.RationalPRGOutputHeight

/-! Both original-budget players use the streamed array route backend.
Exact whole-allocation and whole-law equality transfer hard budgets and
continuous regrets. Complete computational cost/space contracts remain open. -/

namespace Blotto.RationalPRGOriginalInput
open MeasureTheory

def richArrayRouteSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let row := i.normalizedInput.richNativeSystem.arrayRoutePaperSample i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  fun j => i.a * row j

def poorArrayRouteSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let row := i.normalizedInput.poorNativeSystem.arrayRoutePaperSample i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  fun j => i.a * row j

theorem richArrayRouteSample_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : i.richArrayRouteSample K bits = i.richSample K bits := by
  have hp := i.normalizedInput.richNativeSystem.arrayRoutePaperSample_eq i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  exact (congrArg (fun row : Fin n → ℚ => fun j => i.a * row j) hp).trans
    (funext (fun j => (i.richSample_apply K bits j).symm))

theorem poorArrayRouteSample_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : i.poorArrayRouteSample K bits = i.poorSample K bits := by
  have hp := i.normalizedInput.poorNativeSystem.arrayRoutePaperSample_eq i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  exact (congrArg (fun row : Fin n → ℚ => fun j => i.a * row j) hp).trans
    (funext (fun j => (i.poorSample_apply K bits j).symm))

theorem arrayRouteSamples_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.a : ℝ) (fun j => (i.richArrayRouteSample K bits j : ℝ)) ∧
      FullBudget (i.b : ℝ) (fun j => (i.poorArrayRouteSample K bits j : ℝ)) := by
  rw [i.richArrayRouteSample_eq, i.poorArrayRouteSample_eq]
  exact ⟨i.richSample_fullBudget K bits, i.poorSample_fullBudget K bits⟩

noncomputable def richArrayRouteLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.richArrayRouteSample K bits j : ℝ))

noncomputable def poorArrayRouteLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.poorArrayRouteSample K bits j : ℝ))

theorem arrayRouteLaws_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.richArrayRouteLaw K = i.richSampleLaw K ∧ i.poorArrayRouteLaw K = i.poorSampleLaw K := by
  constructor
  · unfold richArrayRouteLaw richSampleLaw
    simp only [i.richArrayRouteSample_eq]
  · unfold poorArrayRouteLaw poorSampleLaw
    simp only [i.poorArrayRouteSample_eq]

theorem arrayRouteSample_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    regret i.realValues (i.a : ℝ) (i.richArrayRouteLaw K) (i.poorArrayRouteLaw K) ≤ 5 / (2 : ℝ) ^ K ∧
      regret i.realValues (i.b : ℝ) (i.poorArrayRouteLaw K) (i.richArrayRouteLaw K) ≤ 5 / (2 : ℝ) ^ K := by
  rw [(i.arrayRouteLaws_eq K).1, (i.arrayRouteLaws_eq K).2]
  exact i.sample_regrets K

end Blotto.RationalPRGOriginalInput
