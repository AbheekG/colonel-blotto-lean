import Blotto.RationalMergeFourBoxes

/-! The native merged four-uniform descriptor has an actual bounded fair-bit
sampler with every-path budget/box and a verified CDF error. -/

namespace Blotto.RationalMergeFourInput
open MeasureTheory

def sample (i : RationalMergeFourInput) (K : ℕ) (bits : Fin (RationalThreeSpec.sampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  i.segmentLottery.flatSample 0 (3 * (8 + K)) K bits

noncomputable def sampleLaw (i : RationalMergeFourInput) (K : ℕ) : Mixed 4 :=
  i.segmentLottery.flatLaw 0 (3 * (8 + K)) K

theorem sample_fullBudget (i : RationalMergeFourInput) (K : ℕ) (bits : Fin (RationalThreeSpec.sampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.sample K bits j : ℝ)) :=
  i.segmentLottery.flatSample_fullBudget 0 _ K i.segmentLottery_endpoints bits

theorem sample_inBox (i : RationalMergeFourInput) (K : ℕ) (bits : Fin (RationalThreeSpec.sampleBitBudget K) → Bool) :
    InBox ![(i.l0 : ℝ), (i.l1 : ℝ), (i.l2 : ℝ), (i.l3 : ℝ)] (fun j => (i.sample K bits j : ℝ)) :=
  i.segmentLottery.flatSample_inBox 0 _ K _ i.segmentLottery_box bits

theorem sampleLaw_actual (i : RationalMergeFourInput) (K : ℕ) :
    i.sampleLaw K = (fairBitLaw (RationalThreeSpec.sampleBitBudget K)).map (fun bits j => (i.sample K bits j : ℝ)) := rfl

theorem sampleLaw_CDF_error (i : RationalMergeFourInput) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := i.segmentLottery.flatLaw_CDF_error 0 K
  rw [i.segmentLottery_law] at h
  exact h

end Blotto.RationalMergeFourInput
