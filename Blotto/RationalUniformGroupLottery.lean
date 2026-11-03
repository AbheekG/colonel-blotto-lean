import Blotto.RationalGroupSpecs
import Blotto.RationalLotteryAssembly
import Blotto.RationalSegmentMachine
import Blotto.RationalMachineIdealTransport

/-! Both all-uniform group cases use one nine-slot native controller. The
pair branch pads a single complementary segment with zero-weight copies. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

def rationalComplementaryPair (B : ℚ) : RationalSegmentLottery 2 1 where
  weight := fun _ => 1
  P := fun _ => ![0, B]
  Q := fun _ => ![B, 0]
  nonnegative := fun _ => by norm_num
  mass := by simp

theorem rationalComplementaryPair_law (B : ℚ) :
    (rationalComplementaryPair B).real.law = complementaryPairLaw (B : ℝ) := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [SegmentLottery.law_measure]
  simp only [rationalComplementaryPair, RationalSegmentLottery.real, Rat.cast_one,
    Measure.sum_fintype, Finset.univ_unique, Finset.sum_singleton, ENNReal.ofReal_one, one_smul]
  change Measure.map (segmentPoint (fun j => ((rationalComplementaryPair B).P 0 j : ℝ))
    (fun j => ((rationalComplementaryPair B).Q 0 j : ℝ))) (unitUniform : Measure ℝ) =
    Measure.map (complementaryPairPoint (B : ℝ)) (unitUniform : Measure ℝ)
  congr 1
  funext t j
  fin_cases j <;> simp [rationalComplementaryPair, segmentPoint, complementaryPairPoint] <;> ring

theorem rationalComplementaryPair_endpoints {B : ℚ} (hB : 0 < B) :
    ∀ slot, FullBudget (B : ℝ) ((rationalComplementaryPair B).real.P slot) ∧
      FullBudget (B : ℝ) ((rationalComplementaryPair B).real.Q slot) := by
  intro slot
  constructor
  · constructor
    · intro j
      fin_cases j
      · simp [RationalSegmentLottery.real, rationalComplementaryPair]
      · simpa [RationalSegmentLottery.real, rationalComplementaryPair] using le_of_lt hB
    · simp [RationalSegmentLottery.real, rationalComplementaryPair, Fin.sum_univ_succ]
  · constructor
    · intro j
      fin_cases j
      · simpa [RationalSegmentLottery.real, rationalComplementaryPair] using le_of_lt hB
      · simp [RationalSegmentLottery.real, rationalComplementaryPair]
    · simp [RationalSegmentLottery.real, rationalComplementaryPair, Fin.sum_univ_succ]

namespace RationalUniformGroupSpec

def lottery {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) : RationalSegmentLottery m 9 := by
  by_cases h2 : m = 2
  · subst m
    exact (rationalComplementaryPair i.B).padRight 8 0
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.threeInput.segmentLottery

theorem lottery_law {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    (i.lottery hm).real.law = i.real.law hm := by
  rcases hm with rfl | rfl
  · change ((rationalComplementaryPair i.B).padRight 8 0).real.law = complementaryPairLaw (i.B : ℝ)
    rw [RationalSegmentLottery.padRight_law, rationalComplementaryPair_law]
  · change i.threeInput.segmentLottery.real.law = i.real.threeInput.law
    rw [i.threeInput.segmentLottery_real, i.threeInput_real]
    exact ProbabilityMeasure.toMeasure_injective i.real.threeInput.segmentLottery_law

theorem lottery_endpoints {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3) :
    ∀ slot, FullBudget (i.B : ℝ) ((i.lottery hm).real.P slot) ∧ FullBudget (i.B : ℝ) ((i.lottery hm).real.Q slot) := by
  rcases hm with rfl | rfl
  · exact (rationalComplementaryPair i.B).padRight_endpoints 8 0 (rationalComplementaryPair_endpoints i.B_pos)
  · intro slot
    change FullBudget (i.B : ℝ) (i.threeInput.segmentLottery.real.P slot) ∧
      FullBudget (i.B : ℝ) (i.threeInput.segmentLottery.real.Q slot)
    rw [i.threeInput.segmentLottery_real]
    exact ⟨i.threeInput.real.segmentLottery_endpoints.1 slot, i.threeInput.real.segmentLottery_endpoints.2 slot⟩

theorem lottery_point_fullBudget {m : ℕ} (i : RationalUniformGroupSpec m) (hm : m = 2 ∨ m = 3)
    (K : ℕ) (slot : Fin 9) (bits : Fin K → Bool) :
    FullBudget (i.B : ℝ) (fun j => ((i.lottery hm).point K slot bits j : ℝ)) :=
  (i.lottery hm).point_fullBudget K (i.lottery_endpoints hm) slot bits

end RationalUniformGroupSpec
end Blotto
