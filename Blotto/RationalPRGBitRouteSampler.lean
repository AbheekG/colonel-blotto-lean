import Blotto.RationalLottoBitRouteSampler
import Blotto.RationalPRGOutputHeight

/-! Both original-budget PRG players run the integrated binary-route source
sampler. The input supplies every length-lattice/width promise. Exact whole-row
and whole-law equality preserve independence, budgets and continuous regrets.
Complete computational time/space contracts remain separate. -/

namespace Blotto.RationalPRGOriginalInput
open MeasureTheory

def richBitRouteSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let row := i.normalizedInput.richNativeSystem.bitRoutePaperSample i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  fun j => i.a * row j

def poorBitRouteSample {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  let row := i.normalizedInput.poorNativeSystem.bitRoutePaperSample i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  fun j => i.a * row j

theorem richBitRouteSample_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : i.richBitRouteSample K bits = i.richSample K bits := by
  have hp := i.normalizedInput.richNativeSystem.bitRoutePaperSample_eq i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos (le_refl _) i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  exact (congrArg (fun row : Fin n → ℚ => fun j => i.a * row j) hp).trans
    (funext (fun j => (i.richSample_apply K bits j).symm))

theorem poorBitRouteSample_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : i.poorBitRouteSample K bits = i.poorSample K bits := by
  have hp := i.normalizedInput.poorNativeSystem.bitRoutePaperSample_eq i.normalizedInput.latticeDenominator
    (3 + i.originalInputWordWidth) i.normalizedInput.latticeDenominator_pos i.normalizedInput.b_le i.normalizedInput.lengths_on_lattice
    (by omega) (i.normalized_lattice_wordWidth_original.trans (by omega)) K bits
  exact (congrArg (fun row : Fin n → ℚ => fun j => i.a * row j) hp).trans
    (funext (fun j => (i.poorSample_apply K bits j).symm))

theorem bitRouteSamples_fullBudget {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    FullBudget (i.a : ℝ) (fun j => (i.richBitRouteSample K bits j : ℝ)) ∧
      FullBudget (i.b : ℝ) (fun j => (i.poorBitRouteSample K bits j : ℝ)) := by
  rw [i.richBitRouteSample_eq, i.poorBitRouteSample_eq]
  exact ⟨i.richSample_fullBudget K bits, i.poorSample_fullBudget K bits⟩

noncomputable def richBitRouteLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.richBitRouteSample K bits j : ℝ))

noncomputable def poorBitRouteLaw {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) : Mixed n :=
  (fairBitLaw (RationalLottoResourceSystem.sampleBitBudget n K)).map (fun bits j => (i.poorBitRouteSample K bits j : ℝ))

theorem bitRouteLaws_eq {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    i.richBitRouteLaw K = i.richSampleLaw K ∧ i.poorBitRouteLaw K = i.poorSampleLaw K := by
  constructor
  · unfold richBitRouteLaw richSampleLaw
    simp only [i.richBitRouteSample_eq]
  · unfold poorBitRouteLaw poorSampleLaw
    simp only [i.poorBitRouteSample_eq]

theorem bitRouteSample_regrets {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ) :
    regret i.realValues (i.a : ℝ) (i.richBitRouteLaw K) (i.poorBitRouteLaw K) ≤ 5 / (2 : ℝ) ^ K ∧
      regret i.realValues (i.b : ℝ) (i.poorBitRouteLaw K) (i.richBitRouteLaw K) ≤ 5 / (2 : ℝ) ^ K := by
  rw [(i.bitRouteLaws_eq K).1, (i.bitRouteLaws_eq K).2]
  exact i.sample_regrets K

end Blotto.RationalPRGOriginalInput
