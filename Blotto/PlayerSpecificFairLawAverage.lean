import Blotto.PlayerSpecificFairAveraging
import Blotto.AveragedBitCDF

/-! Event probabilities of a finite fair average are the exact averages
of its conditional event probabilities. -/
namespace Blotto.PlayerSpecificFairLawAverage
open MeasureTheory
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem event {N : ℕ} (K : ℕ) (l : (Fin K → Bool) → Mixed N) (A : Set (Allocation N))
    (hA : MeasurableSet A) :
    (averagedLaw (fairBitLaw K) l (measurable_of_countable _) : Measure (Allocation N)).real A=
      ∫ bits,(l bits : Measure (Allocation N)).real A ∂(fairBitLaw K : Measure (Fin K → Bool)) := by
  rw [averaged_fairBit_finite,probabilityMixture_real_apply _ _ _ _ _ hA,fairBitLaw_integral_mean]
  simp only [Nat.cast_pow,Nat.cast_ofNat,←Finset.mul_sum]
  congr 1
  simpa only [Equiv.symm_apply_apply] using
    (Equiv.sum_comp (bitIndexEquiv K) (fun j => (l ((bitIndexEquiv K).symm j) : Measure (Allocation N)).real A)).symm

end Blotto.PlayerSpecificFairLawAverage
