import Blotto.RationalLottoProgram
import Blotto.FairBitBlocks
import Blotto.AveragedBitCDF

/-! One flat fair-bit vector supplies the adaptive global coin cap and two
fresh scalar blocks. Its cap contribution is closed; identification of the
averaged ideal law with the global marginal approximation is still separate. -/

namespace Blotto.RationalLottoResourceSystem
open MeasureTheory

def coinBitBudget (n K : ℕ) : ℕ := 3 * (n + 1000 + K)
def innerBitBudget (n K : ℕ) : ℕ := coinBitBudget n K + K
def sampleBitBudget (n K : ℕ) : ℕ := innerBitBudget n K + K

theorem sampleBitBudget_eq (n K : ℕ) : sampleBitBudget n K = 5 * K + 3 * (n + 1000) := by
  unfold sampleBitBudget innerBitBudget coinBitBudget
  omega

def innerSample {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool)
    (innerBits : Fin (innerBitBudget n K) → Bool) : Fin n → ℚ :=
  (i.program K outerBits (secondBitBlock (coinBitBudget n K) K innerBits)).sample (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K innerBits)

def sample {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  i.innerSample K (secondBitBlock (innerBitBudget n K) K bits) (firstBitBlock (innerBitBudget n K) K bits)

noncomputable def innerLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool) : Mixed n :=
  (fairBitLaw (innerBitBudget n K)).map (fun bits j => (i.innerSample K outerBits bits j : ℝ))

noncomputable def sampleLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) : Mixed n :=
  (fairBitLaw (sampleBitBudget n K)).map (fun bits j => (i.sample K bits j : ℝ))

noncomputable def averagedIdealLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) : Mixed n :=
  averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
    (fun scalarBits => (i.program K outerBits scalarBits).idealLaw) (measurable_of_countable _)) (measurable_of_countable _)

theorem sample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.sample K bits j : ℝ)) :=
  i.program_sample_fullBudget K _ _ _ _

theorem sampleLaw_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    ∀ᵐ x ∂(i.sampleLaw K : Measure (Allocation n)), FullBudget (i.B : ℝ) x := by
  change ∀ᵐ x ∂Measure.map (fun bits j => (i.sample K bits j : ℝ))
    (fairBitLaw (sampleBitBudget n K) : Measure (Fin (sampleBitBudget n K) → Bool)), FullBudget (i.B : ℝ) x
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurable_fullBudget _)]
  exact Filter.Eventually.of_forall (i.sample_fullBudget K)

theorem innerLaw_average {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool) :
    i.innerLaw K outerBits = averagedLaw (fairBitLaw K)
      (fun scalarBits => (i.program K outerBits scalarBits).sampleLaw (coinBitBudget n K)) (measurable_of_countable _) := by
  unfold innerLaw innerSample innerBitBudget
  convert! fairBitBlocks_law (n := n) (coinBitBudget n K) K
    (fun choiceBits scalarBits j => ((i.program K outerBits scalarBits).sample (coinBitBudget n K) choiceBits j : ℝ)) using 1

theorem sampleLaw_average {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    i.sampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => (i.program K outerBits scalarBits).sampleLaw (coinBitBudget n K)) (measurable_of_countable _))
        (measurable_of_countable _) := by
  calc
    i.sampleLaw K = averagedLaw (fairBitLaw K) (i.innerLaw K) (measurable_of_countable _) := by
      unfold sampleLaw sample sampleBitBudget innerLaw
      convert! fairBitBlocks_law (n := n) (innerBitBudget n K) K
        (fun innerBits outerBits j => (i.innerSample K outerBits innerBits j : ℝ)) using 1
    _ = _ := by
      apply averaged_fairBit_congr
      exact i.innerLaw_average K

theorem sampleLaw_cap_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    CDFClose (i.sampleLaw K) (i.averagedIdealLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.sampleLaw_average]
  unfold averagedIdealLaw
  apply averaged_fairBit_CDFClose
  intro outerBits
  apply averaged_fairBit_CDFClose
  intro scalarBits
  exact i.program_cap_CDF_error K outerBits scalarBits

end Blotto.RationalLottoResourceSystem
