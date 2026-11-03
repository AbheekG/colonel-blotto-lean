import Blotto.RationalThreeSpec
import Blotto.RationalSegmentFlat

/-! The three-variable rational compiler and bounded fair-bit sampler are
linked to the exact real coupling. This closes local distributional access;
the global PRG controller and full bit-operation ledger remain separate. -/

namespace Blotto.RationalThreeSpec
open MeasureTheory

def sampleBitBudget (K : ℕ) : ℕ := 3 * (8 + K) + K

theorem sampleBitBudget_eq (K : ℕ) : sampleBitBudget K = 4 * K + 24 := by
  unfold sampleBitBudget
  omega

def sample (i : RationalThreeSpec) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) : Fin 3 → ℚ :=
  i.segmentLottery.flatSample 0 (3 * (8 + K)) K bits

noncomputable def sampleLaw (i : RationalThreeSpec) (K : ℕ) : Mixed 3 :=
  i.segmentLottery.flatLaw 0 (3 * (8 + K)) K

theorem sampleLaw_actual (i : RationalThreeSpec) (K : ℕ) : i.sampleLaw K =
    (fairBitLaw (sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ)) := rfl

theorem sample_fullBudget (i : RationalThreeSpec) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.sample K bits j : ℝ)) := by
  apply i.segmentLottery.flatSample_fullBudget
  intro slot
  rw [i.segmentLottery_real]
  exact ⟨i.real.segmentLottery_endpoints.1 slot, i.real.segmentLottery_endpoints.2 slot⟩

theorem sampleLaw_CDF_error (i : RationalThreeSpec) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := i.segmentLottery.flatLaw_CDF_error 0 K
  rw [i.segmentLottery_real] at h
  have hl : i.real.segmentLottery.law = i.real.law :=
    ProbabilityMeasure.toMeasure_injective i.real.segmentLottery_law
  rw [hl] at h
  exact h

end Blotto.RationalThreeSpec
