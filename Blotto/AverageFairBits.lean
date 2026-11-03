import Blotto.FairBitLaw
import Blotto.ParameterLaw

/-! A fair-bit parameter vector averages a family exactly as uniform finite
indices. This connects sequential scalar sampling to the finite whole laws,
without enumerating any support in the runtime procedure. -/

namespace Blotto
open MeasureTheory
open scoped BigOperators

theorem fairBitLaw_atoms (K : ℕ) :
    (fairBitLaw K : Measure (Fin K → Bool)) =
      Measure.sum (fun bits => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • Measure.dirac bits) := by
  calc
    _ = Measure.sum (fun bits => (fairBitLaw K : Measure (Fin K → Bool)) {bits} • Measure.dirac bits) :=
      (Measure.sum_smul_dirac _).symm
    _ = _ := by
      congr 1
      funext bits
      rw [fairBitLaw_singleton_realWeight]

theorem averaged_fairBit_indices {n : ℕ} (K : ℕ) (law : Fin (2 ^ K) → Mixed n) :
    averagedLaw (fairBitLaw K) (fun bits => law (bitIndex K bits)) (measurable_of_countable _) =
      probabilityMixture (fun _ : Fin (2 ^ K) => 1 / ((2 ^ K : ℕ) : ℝ)) law
        (fun _ => by positivity) (uniformWeights_sum (pow_pos (by decide : 0 < (2 : ℕ)) K)) := by
  apply ProbabilityMeasure.toMeasure_injective
  have hm : Measurable (fun bits : Fin K → Bool => (law (bitIndex K bits) : Measure (Allocation n))) := measurable_of_countable _
  change (fairBitLaw K : Measure (Fin K → Bool)).bind (fun bits => (law (bitIndex K bits) : Measure (Allocation n))) = _
  rw [fairBitLaw_atoms, Measure.bind_sum _ _ hm.aemeasurable]
  have he : Measure.sum (fun bits : Fin K → Bool =>
      (ENNReal.ofReal (1 / (2 : ℝ) ^ K) • Measure.dirac bits).bind (fun bits => (law (bitIndex K bits) : Measure (Allocation n)))) =
      Measure.sum (fun bits : Fin K → Bool => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • (law (bitIndex K bits) : Measure (Allocation n))) := by
    congr 1
    funext bits
    rw [Measure.bind_smul _ _ hm.aemeasurable, Measure.dirac_bind hm]
  rw [he]
  change Measure.sum (fun bits : Fin K → Bool => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • (law (bitIndex K bits) : Measure (Allocation n))) =
    Measure.sum (fun j : Fin (2 ^ K) => ENNReal.ofReal (1 / ((2 ^ K : ℕ) : ℝ)) • (law j : Measure (Allocation n)))
  simp only [Nat.cast_pow, Nat.cast_ofNat]
  rw [Measure.sum_fintype, Measure.sum_fintype]
  exact Equiv.sum_comp (bitIndexEquiv K) (fun j => ENNReal.ofReal (1 / (2 : ℝ) ^ K) • (law j : Measure (Allocation n)))

end Blotto
