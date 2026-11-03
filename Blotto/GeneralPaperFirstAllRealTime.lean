import Blotto.GeneralPaperAllBranchRealTimeAlgebra
import Blotto.GeneralPaperFirstAllRealCorrectness

/-! Uniform paper real-RAM preparation time on the actual all-branch return.
No input rational precision or binary accuracy length enters this bound. -/
namespace Blotto.GeneralPaperFirstAllRealTime
open GeneralPaperOriginalRealInput GeneralPaperFirstAllRealDispatch
open GeneralPaperRealHeadlineParameters (timeScale logarithm)
open GeneralPaperAllBranchRealTimeAlgebra
set_option autoImplicit false
set_option maxHeartbeats 3500000
set_option maxRecDepth 16384

theorem one_base (model : RationalCostModel) (p : Input) (hN : p.n = 1) :
    ((one model p hN).2 : ℚ) ≤ 288 * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ 0 := by
  have hn : ((one model p hN).2 : ℚ) ≤ 288 := by
    exact_mod_cast GeneralPaperOneFieldRealPreparation.work 1 p.budget
  have hs := mul_le_mul_of_nonneg_left (scale_positive p) (by norm_num : (0 : ℚ) ≤ 288)
  have hs' : (288 : ℚ) ≤ 288 * timeScale p.n p.epsilon := by simpa using hs
  simpa using hn.trans hs'

theorem equal_base (model : RationalCostModel) (p : Input) :
    ((equal model p).2 : ℚ) ≤ 134217728 * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ 2 := by
  let L := binaryWordWidth p.n + binaryWordWidth ⌈p.epsilon⁻¹⌉₊ + 16
  have hNative := GeneralPaperEqualFirstRealDispatch.accuracy_work model p.epsilon p.values p.selector p.correct p.budget
  have hQ : ((equal model p).2 : ℚ) ≤ 67108864 * ((p.n + 1 : ℕ) : ℚ) * (L : ℚ) ^ 2 := by exact_mod_cast hNative
  have hN : ((p.n + 1 : ℕ) : ℚ) ≤ 2 * timeScale p.n p.epsilon := by
    have hn : (1 : ℚ) ≤ p.n := by exact_mod_cast p.selector.fields_positive
    have hs := scale_ge_fields p
    push_cast
    linarith only [hn, hs]
  have hnWord := binaryWordWidth_mono (show p.n ≤ p.n + 4 by omega)
  have hLog : L ≤ logarithm p.n p.epsilon := by dsimp only [L, logarithm]; omega
  have hPow : (L : ℚ) ^ 2 ≤ (logarithm p.n p.epsilon : ℚ) ^ 2 := by exact_mod_cast Nat.pow_le_pow_left hLog 2
  have hScale : 0 ≤ timeScale p.n p.epsilon := (by norm_num : (0 : ℚ) ≤ 1).trans (scale_positive p)
  have hm := mul_le_mul (mul_le_mul_of_nonneg_left hN (by norm_num : (0 : ℚ) ≤ 67108864)) hPow (by positivity) (by positivity)
  exact (hQ.trans hm).trans_eq (by ring)

theorem preparation_time (model : RationalCostModel) :
    ∃ C d : ℕ, ∀ p : Input, ((run model p).2 : ℚ) ≤
      (C : ℚ) * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ d := by
  obtain ⟨C, d, hUnequal⟩ := GeneralPaperRealPreparationHeadline.arithmetic_time model
  refine ⟨C + 134218176, d + 2, fun p => ?_⟩
  by_cases hN : p.n = 1
  · rw [on_one model p hN]
    exact raise_bound p _ (288 + 64) (C + 134218176) 0 (d + 2) (by omega) (by omega)
      (absorb_overhead p _ 288 0 64 (one_base model p hN))
  · by_cases hB : p.budget = 1
    · rw [on_equal model p hN hB]
      exact raise_bound p _ (134217728 + 96) (C + 134218176) 2 (d + 2) (by omega) (by omega)
        (absorb_overhead p _ 134217728 2 96 (equal_base model p))
    · have hu : ((unequal model p).2 : ℚ) ≤ (C : ℚ) * timeScale p.n p.epsilon *
          (logarithm p.n p.epsilon : ℚ) ^ d :=
        hUnequal p.epsilon p.epsilon_valid.1 p.epsilon_valid.2 p.values p.selector p.correct p.budget
          ⟨p.budget_valid.1, strict_of_ne p hB⟩
      rw [on_unequal model p hN hB]
      exact raise_bound p _ (C + 96) (C + 134218176) d (d + 2) (by omega) (by omega)
        (absorb_overhead p _ C d 96 hu)

theorem time_and_original_game_contract (model : RationalCostModel) :
    ∃ C d : ℕ, ∀ p : Input, ((run model p).2 : ℚ) ≤
      (C : ℚ) * timeScale p.n p.epsilon * (logarithm p.n p.epsilon : ℚ) ^ d ∧
      GeneralPaperFirstAllRealLaw.Guarantee model p (run model p).1 ∧
      GeneralPaperFirstAllRealLaw.Pointwise model p (run model p).1 := by
  obtain ⟨C, d, h⟩ := preparation_time model
  exact ⟨C, d, fun p => ⟨h p, GeneralPaperFirstAllRealCorrectness.actual_contract model p⟩⟩

end Blotto.GeneralPaperFirstAllRealTime
