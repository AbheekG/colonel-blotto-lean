import Blotto.GeneralPaperNativeDyadicBlocks

/-! Exact uniform law of a fair dyadic index, with no support enumeration
on the data path. All finite sums and the inverse bit equivalence below
are erased probability-law proofs. -/
namespace Blotto.GeneralPaperFairIndexLaw
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem uniform {n : ℕ} (R : ℕ) (rows : Fin (2^R) → Allocation n) :
    (fairBitLaw R).map (fun bits => rows (bitIndex R bits))=
      GeneralPaperUniformRowLaw.law (Nat.two_pow_pos R) rows := by
  apply ProbabilityMeasure.toMeasure_injective
  rw [fairBitLaw_map_atoms]
  change Measure.sum (fun bits : Fin R → Bool => ENNReal.ofReal (1/(2:ℝ)^R) • Measure.dirac (rows (bitIndex R bits)))=
    Measure.sum (fun i : Fin (2^R) => ENNReal.ofReal (1/((2^R:ℕ):ℝ)) • Measure.dirac (rows i))
  simp only [Nat.cast_pow,Nat.cast_ofNat]
  rw [Measure.sum_fintype,Measure.sum_fintype]
  exact Equiv.sum_comp (bitIndexEquiv R) (fun i => ENNReal.ofReal (1/(2:ℝ)^R) • Measure.dirac (rows i))

end Blotto.GeneralPaperFairIndexLaw
