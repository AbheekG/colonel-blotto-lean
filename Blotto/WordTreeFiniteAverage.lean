import Blotto.WordTreeAllocationLaw
import Blotto.AveragedBitMixtures

/-! Event probabilities and fresh finite-parameter averaging commute with
the ideal word-tree allocation law. These identities expose the sequential
law of a serial controller without constructing its support at runtime. -/

namespace Blotto.WordChoiceTree
open MeasureTheory

theorem evalLaw_real_event {α : Type*} {n : ℕ} (T : WordChoiceTree α) (f : α → Mixed n)
    (A : Set (Allocation n)) (hA : MeasurableSet A) :
    (T.evalLaw f : Measure (Allocation n)).real A = T.decode.mean (fun x => (f x : Measure (Allocation n)).real A) := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    rw [evalLaw]
    unfold binaryLaw
    rw [probabilityMixture_real_apply _ _ _ _ _ hA]
    simp only [Fin.sum_univ_succ, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Finset.univ_unique, Finset.sum_singleton, decode, AdaptiveChoiceTree.mean]
    change ((((a : ℚ) / b : ℚ) : ℝ) * (upper.evalLaw f : Measure (Allocation n)).real A +
      (1 - (((a : ℚ) / b : ℚ) : ℝ)) * (lower.evalLaw f : Measure (Allocation n)).real A) = _
    rw [hu, hl]

theorem evalLaw_averaged_fairBits {α : Type*} {n : ℕ} (T : WordChoiceTree α) (K : ℕ)
    (f : α → (Fin K → Bool) → Mixed n) :
    averagedLaw (fairBitLaw K) (fun bits => T.evalLaw (fun x => f x bits)) (measurable_of_countable _) =
      T.evalLaw (fun x => averagedLaw (fairBitLaw K) (f x) (measurable_of_countable _)) := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    have hleft := hu
    have hright := hl
    unfold evalLaw
    rw [averaged_fairBit_binary, hleft, hright]

end Blotto.WordChoiceTree
