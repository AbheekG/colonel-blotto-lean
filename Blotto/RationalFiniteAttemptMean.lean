import Blotto.RationalFiniteAttempt
import Blotto.AdaptiveChoiceBoundedMean

/-! One bounded rational finite attempt controls every [0,1]-test expectation.
A decoder can represent failure, a selected guide label or a whole record. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators Classical
namespace RationalFiniteAttempt

noncomputable def sampleMean {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (f : Option (Fin n) → ℝ) : ℝ :=
  ∫ bits, f (a.sample K bits) ∂(fairBitLaw (a.bitBudget K) : Measure (Fin (a.bitBudget K) → Bool))

noncomputable def idealMean {r n : ℕ} (a : RationalFiniteAttempt r n) (f : Option (Fin n) → ℝ) : ℝ :=
  ∑ i, (a.weight i : ℝ) * f (a.decode i)

theorem sampleMean_error {r n : ℕ} (a : RationalFiniteAttempt r n) (K : ℕ)
    (f : Option (Fin n) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    |a.sampleMean K f - a.idealMean f| ≤ 1 / (2 : ℝ) ^ K := by
  let m := categoricalMachine a.fallbackLabel
  let s := CategoricalState.remaining (rationalWeightList a.weight a.nonnegative)
  have hRank : m.rank s ≤ r - 1 := by simp [m, s, categoricalMachine, categoricalRank, rationalWeightList]
  have hHeight : (m.specification s).decode.height ≤ r - 1 := by
    rw [WordChoiceTree.decode_height]
    exact (m.specification_height s).trans hRank
  have he := (m.specification s).decode.capped_mean_error_precision (r - 1) K hHeight
    a.fallbackLabel (fun i => f (a.decode i)) (fun i => hf _)
  have hOutput : ∀ bits : Fin (a.bitBudget K) → Bool,
      a.sample K bits = a.decode ((m.specification s).decode.output (a.bitBudget K) a.fallbackLabel bits) := by
    intro bits
    unfold sample sampleLabel
    rw [m.output_refines, WordChoiceTree.output_refines]
  unfold sampleMean idealMean
  simp_rw [hOutput]
  have hm := rationalCategorical_mean a.weight a.nonnegative a.sum_one a.fallbackLabel (fun i => f (a.decode i))
  change (m.specification s).decode.mean (fun i => f (a.decode i)) = _ at hm
  rw [hm] at he
  exact he

theorem idealMean_unit {r n : ℕ} (a : RationalFiniteAttempt r n)
    (f : Option (Fin n) → ℝ) (hf : ∀ x, 0 ≤ f x ∧ f x ≤ 1) :
    0 ≤ a.idealMean f ∧ a.idealMean f ≤ 1 := by
  have hn : ∀ i, (0 : ℝ) ≤ (a.weight i : ℝ) := by intro i; exact_mod_cast a.nonnegative i
  have hs : (∑ i, (a.weight i : ℝ)) = 1 := by exact_mod_cast a.sum_one
  constructor
  · exact Finset.sum_nonneg (fun i _ => mul_nonneg (hn i) (hf _).1)
  · calc
      a.idealMean f ≤ ∑ i, (a.weight i : ℝ) := by
        apply Finset.sum_le_sum
        intro i _
        exact mul_le_of_le_one_right (hn i) (hf _).2
      _ = 1 := hs

end RationalFiniteAttempt
end Blotto
