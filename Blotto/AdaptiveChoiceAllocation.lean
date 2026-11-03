import Blotto.WordChoiceLaw
import Blotto.Model

/-! The shared-cap contract specialized to whole allocations. Both returned
leaves and final fallback have hard budgets on every bit path. The marginal
CDF perturbation controls all thresholds, including those at atoms. -/

namespace Blotto
open MeasureTheory Set Filter

theorem wordChoice_capped_fullBudget {n : ℕ} (R : ℕ) (T : WordChoiceTree (Allocation n))
    (fallback : Allocation n) {B : ℝ} (hT : T.decode.ForLeaves (FullBudget B)) (hd : FullBudget B fallback) :
    ∀ᵐ x ∂(T.cappedLaw R fallback : Measure (Allocation n)), FullBudget B x := by
  change ∀ᵐ x ∂Measure.map (T.output R fallback) (fairBitLaw R : Measure (Fin R → Bool)), FullBudget B x
  rw [ae_map_iff (measurable_of_countable _).aemeasurable (measurable_fullBudget B)]
  exact Eventually.of_forall (fun bits => T.output_forLeaves R fallback bits (FullBudget B) hT hd)

theorem wordChoice_capped_CDF_error {n : ℕ} (C K : ℕ) (T : WordChoiceTree (Allocation n)) (hC : T.height ≤ C)
    (fallback : Allocation n) : CDFClose (T.cappedLaw (3 * (C + K)) fallback) T.decode.idealLaw (1 / (2 : ℝ) ^ K) := by
  intro j z
  change |(Measure.map (fun x : Allocation n => x j) (T.cappedLaw (3 * (C + K)) fallback : Measure (Allocation n))).real (Iic z) -
    (Measure.map (fun x : Allocation n => x j) (T.decode.idealLaw : Measure (Allocation n))).real (Iic z)| ≤ _
  rw [map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic,
    map_measureReal_apply (measurable_pi_apply j) measurableSet_Iic]
  exact T.cappedLaw_event_error_precision C K hC fallback ((fun x : Allocation n => x j) ⁻¹' Iic z)
    (measurableSet_Iic.preimage (measurable_pi_apply j))

end Blotto
