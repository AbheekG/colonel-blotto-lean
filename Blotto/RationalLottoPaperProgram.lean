import Blotto.RationalLottoFallback
import Blotto.RationalLottoIdealLaw
import Blotto.RationalLottoSharedOutput

/-! The bounded global sampler uses the manuscript's direct budget fallback.
Generic deterministic-leaf sampler statements remain available unchanged. -/

namespace Blotto.RationalLottoResourceSystem
open MeasureTheory

def paperFixedSampleReference {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin n → ℚ :=
  (i.machine K outerBits scalarBits).output R (i.samplingStart K outerBits scalarBits) i.fallbackAllocation choiceBits

def paperFixedSample {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) : Fin n → ℚ :=
  i.sharedFixedSample K R outerBits scalarBits choiceBits

theorem paperFixedSample_refines {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    i.paperFixedSample K R outerBits scalarBits choiceBits =
      i.paperFixedSampleReference K R outerBits scalarBits choiceBits :=
  i.sharedFixedSample_refines K R outerBits scalarBits choiceBits

noncomputable def paperFixedLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) : Mixed n :=
  (i.machine K outerBits scalarBits).rationalCappedLaw R (i.samplingStart K outerBits scalarBits) i.fallbackAllocation

theorem paperFixedSample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) (choiceBits : Fin R → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.paperFixedSample K R outerBits scalarBits choiceBits j : ℝ)) := by
  rw [paperFixedSample_refines, paperFixedSampleReference, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (i.program_leavesBudget K outerBits scalarBits) i.fallbackAllocation_fullBudget

theorem paperFixedLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    CDFClose (i.paperFixedLaw K (coinBitBudget n K) outerBits scalarBits)
      (i.program K outerBits scalarBits).idealLaw (1 / (2 : ℝ) ^ K) :=
  (i.machine K outerBits scalarBits).rationalCappedLaw_CDF_error (n + 1000) K
    (i.samplingStart K outerBits scalarBits) (i.program_rank_paper_bound K outerBits scalarBits) i.fallbackAllocation

def paperInnerSample {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool)
    (innerBits : Fin (innerBitBudget n K) → Bool) : Fin n → ℚ :=
  i.paperFixedSample K (coinBitBudget n K) outerBits (secondBitBlock (coinBitBudget n K) K innerBits)
    (firstBitBlock (coinBitBudget n K) K innerBits)

def paperSample {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : Fin n → ℚ :=
  i.paperInnerSample K (secondBitBlock (innerBitBudget n K) K bits) (firstBitBlock (innerBitBudget n K) K bits)

noncomputable def paperInnerLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool) : Mixed n :=
  (fairBitLaw (innerBitBudget n K)).map (fun bits j => (i.paperInnerSample K outerBits bits j : ℝ))

noncomputable def paperSampleLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) : Mixed n :=
  (fairBitLaw (sampleBitBudget n K)).map (fun bits j => (i.paperSample K bits j : ℝ))

theorem paperSample_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.paperSample K bits j : ℝ)) := i.paperFixedSample_fullBudget K _ _ _ _

theorem paperSampleLaw_fullBudget {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    ∀ᵐ x ∂(i.paperSampleLaw K : Measure (Allocation n)), FullBudget (i.B : ℝ) x := by
  change ∀ᵐ x ∂Measure.map (fun bits j => (i.paperSample K bits j : ℝ))
    (fairBitLaw (sampleBitBudget n K) : Measure (Fin (sampleBitBudget n K) → Bool)), FullBudget (i.B : ℝ) x
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurable_fullBudget _)]
  exact Filter.Eventually.of_forall (i.paperSample_fullBudget K)

theorem paperInnerLaw_average {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) (outerBits : Fin K → Bool) :
    i.paperInnerLaw K outerBits = averagedLaw (fairBitLaw K)
      (fun scalarBits => i.paperFixedLaw K (coinBitBudget n K) outerBits scalarBits) (measurable_of_countable _) := by
  unfold paperInnerLaw paperInnerSample innerBitBudget
  convert! fairBitBlocks_law (n := n) (coinBitBudget n K) K
    (fun choiceBits scalarBits j => (i.paperFixedSample K (coinBitBudget n K) outerBits scalarBits choiceBits j : ℝ)) using 1
  simp only [paperFixedSample_refines, paperFixedSampleReference]
  rfl

theorem paperSampleLaw_average {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    i.paperSampleLaw K = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.paperFixedLaw K (coinBitBudget n K) outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) := by
  calc
    i.paperSampleLaw K = averagedLaw (fairBitLaw K) (i.paperInnerLaw K) (measurable_of_countable _) := by
      unfold paperSampleLaw paperSample sampleBitBudget paperInnerLaw
      convert! fairBitBlocks_law (n := n) (innerBitBudget n K) K
        (fun innerBits outerBits j => (i.paperInnerSample K outerBits innerBits j : ℝ)) using 1
    _ = _ := by
      apply averaged_fairBit_congr
      exact i.paperInnerLaw_average K

theorem paperSampleLaw_cap_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    CDFClose (i.paperSampleLaw K) (i.averagedIdealLaw K) (1 / (2 : ℝ) ^ K) := by
  rw [i.paperSampleLaw_average]
  unfold averagedIdealLaw
  apply averaged_fairBit_CDFClose
  intro outerBits
  apply averaged_fairBit_CDFClose
  exact i.paperFixedLaw_CDF_error K outerBits

theorem paperSampleLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    CDFClose (i.paperSampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  have h := i.paperSampleLaw_cap_CDF_error K
  rw [i.averagedIdealLaw_eq_midpoint K] at h
  have he := h.triangle (i.midpointLaw_CDF_error K)
  have hsum : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at he
  exact he

end Blotto.RationalLottoResourceSystem
