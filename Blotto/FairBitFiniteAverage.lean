import Blotto.AverageFairBits

/-! Any finite family over a fair bit block has an exact uniform-index
representation. This representation is used for proofs only. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem averaged_fairBit_finite {n : ℕ} (K : ℕ) (law : (Fin K → Bool) → Mixed n) :
    averagedLaw (fairBitLaw K) law (measurable_of_countable _) =
      probabilityMixture (fun _ : Fin (2 ^ K) => 1 / ((2 ^ K : ℕ) : ℝ))
        (fun j => law ((bitIndexEquiv K).symm j)) (fun _ => by positivity)
        (uniformWeights_sum (pow_pos (by decide : 0 < (2 : ℕ)) K)) := by
  have he : (fun bits => law ((bitIndexEquiv K).symm (bitIndex K bits))) = law := by
    funext bits
    change law ((bitIndexEquiv K).symm ((bitIndexEquiv K) bits)) = law bits
    rw [Equiv.symm_apply_apply]
  have h := averaged_fairBit_indices K (fun j => law ((bitIndexEquiv K).symm j))
  simpa only [he] using h

end Blotto
