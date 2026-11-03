import Blotto.AdaptiveChoiceIdeal

/-! The accepted part of the bounded shared-cap sampler is dominated by its
exact ideal future law. This proves correctness beyond a failure-probability
estimate and permits an arbitrary final fallback without hiding a bias. -/

namespace Blotto.AdaptiveChoiceTree
open MeasureTheory

noncomputable def acceptedValue {α : Type*} (f : α → ℝ) : Option α → ℝ
  | none => 0
  | some x => f x

theorem sample_accepted_le_mean {α : Type*} (R : ℕ) (T : AdaptiveChoiceTree α) (f : α → ℝ)
    (hf : ∀ x, 0 ≤ f x) :
    (∫ bits, acceptedValue f (T.sample R bits).1 ∂(fairBitLaw R : Measure (Fin R → Bool))) ≤ T.mean f := by
  induction R using Nat.strong_induction_on generalizing T with
  | h R ih =>
    induction T with
    | leaf x => simp [sample, acceptedValue, mean]
    | fork p hp upper lower hu hl =>
      by_cases h0 : p ≤ 0
      · have he : p = 0 := le_antisymm h0 hp.1
        subst p
        have hs : (fun bits : Fin R → Bool => acceptedValue f ((AdaptiveChoiceTree.fork 0 hp upper lower).sample R bits).1) =
            fun bits => acceptedValue f (lower.sample R bits).1 := by
          funext bits
          conv_lhs => unfold sample
          simp only [le_rfl, ite_true]
        rw [hs]
        simpa only [mean, Rat.cast_zero, zero_mul, sub_zero, one_mul, zero_add] using hl
      by_cases h1 : 1 ≤ p
      · have he : p = 1 := le_antisymm hp.2 h1
        subst p
        have hs : (fun bits : Fin R → Bool => acceptedValue f ((AdaptiveChoiceTree.fork 1 hp upper lower).sample R bits).1) =
            fun bits => acceptedValue f (upper.sample R bits).1 := by
          funext bits
          conv_lhs => unfold sample
          norm_num
        rw [hs]
        simpa only [mean, Rat.cast_one, sub_self, zero_mul, one_mul, add_zero] using hu
      cases R with
      | zero =>
        have hs : (fun bits : Fin 0 → Bool => acceptedValue f ((AdaptiveChoiceTree.fork p hp upper lower).sample 0 bits).1) =
            fun _ => (0 : ℝ) := by
          funext bits
          conv_lhs => unfold sample
          simp only [h0, h1, ite_false, acceptedValue]
        rw [hs, integral_zero]
        exact (AdaptiveChoiceTree.fork p hp upper lower).mean_nonnegative f hf
      | succ r =>
        rw [fairBitLaw_integral_split]
        let residual := AdaptiveChoiceTree.fork (coinResidual p) (coinResidual_bounds hp) upper lower
        let finished := if probabilityDigit p then upper else lower
        have hres := ih r (by omega) residual
        have hfin := ih r (by omega) finished
        have hm : (fun bits : Fin r → Bool => acceptedValue f
            ((AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (probabilityDigit p) bits)).1) =
            fun bits => acceptedValue f (residual.sample r bits).1 := by
          funext bits
          rw [sample_match r p hp upper lower bits h0 h1]
        have hn : (fun bits : Fin r → Bool => acceptedValue f
            ((AdaptiveChoiceTree.fork p hp upper lower).sample (r + 1) (prependBit (!(probabilityDigit p)) bits)).1) =
            fun bits => acceptedValue f (finished.sample r bits).1 := by
          funext bits
          rw [sample_mismatch r p hp upper lower bits h0 h1]
        have hi := mean_digit_identity p hp upper lower f
        cases hd : probabilityDigit p
        · have hm' := hm
          have hn' := hn
          rw [hd] at hm' hn'
          simp only [Bool.not_false] at hn'
          rw [hm', hn', hi]
          exact add_le_add (mul_le_mul_of_nonneg_left hres (by norm_num)) (mul_le_mul_of_nonneg_left hfin (by norm_num))
        · have hm' := hm
          have hn' := hn
          rw [hd] at hm' hn'
          simp only [Bool.not_true] at hn'
          rw [hn', hm', hi]
          have hsum := add_le_add (mul_le_mul_of_nonneg_left hres (by norm_num : (0 : ℝ) ≤ 1 / 2))
            (mul_le_mul_of_nonneg_left hfin (by norm_num : (0 : ℝ) ≤ 1 / 2))
          linarith

end Blotto.AdaptiveChoiceTree
