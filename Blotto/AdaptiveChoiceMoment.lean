import Blotto.AdaptiveChoiceTree

/-! Exponential moment under actual fresh fair inputs for the shared-cap
interpreter. A digit either continues the same coin or completes one choice;
this gives the uniform bound 2^height even for adaptive child probabilities. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory

theorem sample_match {α : Type*} (r : ℕ) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : AdaptiveChoiceTree α) (bits : Fin r → Bool) (h0 : ¬p ≤ 0) (h1 : ¬1 ≤ p) :
    (AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (probabilityDigit p) bits) =
      let result := (AdaptiveChoiceTree.fork (coinResidual p) (coinResidual_bounds hp) upper lower).sample r bits
      (result.1, result.2 + 1) := by
  conv_lhs => unfold sample
  simp only [h0, h1, ite_false, prependBit, Fin.cons_zero, ite_true, Fin.tail_cons]

theorem sample_mismatch {α : Type*} (r : ℕ) (p : ℚ) (hp : 0 ≤ p ∧ p ≤ 1)
    (upper lower : AdaptiveChoiceTree α) (bits : Fin r → Bool) (h0 : ¬p ≤ 0) (h1 : ¬1 ≤ p) :
    (AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (!(probabilityDigit p)) bits) =
      let result := (if probabilityDigit p then upper else lower).sample r bits
      (result.1, result.2 + 1) := by
  conv_lhs => unfold sample
  simp only [h0, h1, ite_false, prependBit, Fin.cons_zero, Fin.tail_cons]
  cases probabilityDigit p <;> simp

theorem mismatch_height_le {α : Type*} (p : ℚ) (upper lower : AdaptiveChoiceTree α) :
    (if probabilityDigit p then upper else lower).height ≤ max upper.height lower.height := by
  split_ifs
  · exact le_max_left _ _
  · exact le_max_right _ _

theorem sample_moment {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) :
    (∫ bits, (4 / 3 : ℝ) ^ (T.sample R bits).2 ∂(fairBitLaw R : Measure (Fin R → Bool))) ≤ (2 : ℝ) ^ T.height := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf x => simp [sample, height]
    | fork p hp upper lower hu hl =>
      by_cases h0 : p ≤ 0
      · have he : (fun bits : Fin R → Bool => (4 / 3 : ℝ) ^ ((AdaptiveChoiceTree.fork p hp upper lower).sample R bits).2) =
          fun bits => (4 / 3 : ℝ) ^ (lower.sample R bits).2 := by
          funext bits
          conv_lhs => unfold sample
          simp only [h0, ite_true]
        rw [he]
        exact hl.trans (pow_le_pow_right₀ (by norm_num) (by simp only [height]; omega))
      by_cases h1 : 1 ≤ p
      · have he : (fun bits : Fin R → Bool => (4 / 3 : ℝ) ^ ((AdaptiveChoiceTree.fork p hp upper lower).sample R bits).2) =
          fun bits => (4 / 3 : ℝ) ^ (upper.sample R bits).2 := by
          funext bits
          conv_lhs => unfold sample
          simp only [h0, h1, ite_false, ite_true]
        rw [he]
        exact hu.trans (pow_le_pow_right₀ (by norm_num) (by simp only [height]; omega))
      cases R with
      | zero =>
        have he : (fun bits : Fin 0 → Bool => (4 / 3 : ℝ) ^ ((AdaptiveChoiceTree.fork p hp upper lower).sample 0 bits).2) =
            fun _ => (1 : ℝ) := by
          funext bits
          conv_lhs => unfold sample
          simp only [h0, h1, ite_false, pow_zero]
        rw [he, integral_const, probReal_univ, one_smul]
        exact one_le_pow₀ (by norm_num)
      | succ r =>
        rw [fairBitLaw_integral_split]
        let residual := AdaptiveChoiceTree.fork (coinResidual p) (coinResidual_bounds hp) upper lower
        let finished := if probabilityDigit p then upper else lower
        have hf : (fun bits : Fin r → Bool => (4 / 3 : ℝ) ^
            ((AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (probabilityDigit p) bits)).2) =
            fun bits => (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ (residual.sample r bits).2 := by
          funext bits
          rw [sample_match r p hp upper lower bits h0 h1]
          dsimp only
          rw [pow_succ]
          ring
        have hg : (fun bits : Fin r → Bool => (4 / 3 : ℝ) ^
            ((AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (!(probabilityDigit p)) bits)).2) =
            fun bits => (4 / 3 : ℝ) * (4 / 3 : ℝ) ^ (finished.sample r bits).2 := by
          funext bits
          rw [sample_mismatch r p hp upper lower bits h0 h1]
          dsimp only
          rw [pow_succ]
          ring
        have hr := ih r (by omega) residual
        have hs := (ih r (by omega) finished).trans
          (pow_le_pow_right₀ (by norm_num : (1 : ℝ) ≤ 2) (mismatch_height_le p upper lower))
        change (∫ bits, (4 / 3 : ℝ) ^ (residual.sample r bits).2 ∂(fairBitLaw r : Measure (Fin r → Bool))) ≤
          (2 : ℝ) ^ (1 + max upper.height lower.height) at hr
        rw [pow_add, pow_one] at hr
        cases hd : probabilityDigit p
        · have hf' := hf
          have hg' := hg
          rw [hd] at hf' hg'
          simp only [Bool.not_false] at hg'
          rw [hf', hg', integral_const_mul, integral_const_mul]
          change _ ≤ (2 : ℝ) ^ (1 + max upper.height lower.height)
          rw [pow_add, pow_one]
          linarith
        · have hf' := hf
          have hg' := hg
          rw [hd] at hf' hg'
          simp only [Bool.not_true] at hg'
          rw [hg', hf', integral_const_mul, integral_const_mul]
          change _ ≤ (2 : ℝ) ^ (1 + max upper.height lower.height)
          rw [pow_add, pow_one]
          linarith

end Blotto.AdaptiveChoiceTree
