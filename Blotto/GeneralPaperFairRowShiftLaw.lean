import Blotto.GeneralPaperFairIndexLaw

/-! Exact joint row/shift law from consecutive independent fair blocks.
The nested law retains each entire allocation row. Commutation of the two
uniform finite averages is used only in this erased law proof. -/
namespace Blotto.GeneralPaperFairRowShiftLaw
open MeasureTheory
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem commute {n T S : ℕ} (hT : 0<T) (hS : 0<S) (f : Fin T → Fin S → Allocation n) :
    GeneralPaperUniformRowLaw.mixture hT (fun i => GeneralPaperUniformRowLaw.law hS (f i))=
      GeneralPaperUniformRowLaw.mixture hS (fun l => GeneralPaperUniformRowLaw.law hT (fun i => f i l)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.sum (fun i : Fin T => ENNReal.ofReal (1/(T:ℝ)) •
      Measure.sum (fun l : Fin S => ENNReal.ofReal (1/(S:ℝ)) • Measure.dirac (f i l)))=
    Measure.sum (fun l : Fin S => ENNReal.ofReal (1/(S:ℝ)) •
      Measure.sum (fun i : Fin T => ENNReal.ofReal (1/(T:ℝ)) • Measure.dirac (f i l)))
  simp_rw [Measure.sum_fintype,Finset.smul_sum,smul_smul]
  rw [Finset.sum_comm]
  simp only [mul_comm]

theorem indices {n : ℕ} (R L : ℕ) (f : Fin (2^R) → Fin (2^L) → Allocation n) :
    (fairBitLaw (R+L)).map (fun bits => f (bitIndex R (firstBitBlock R L bits)) (bitIndex L (secondBitBlock R L bits)))=
      GeneralPaperUniformRowLaw.mixture (Nat.two_pow_pos R) (fun i => GeneralPaperUniformRowLaw.law (Nat.two_pow_pos L) (f i)) := by
  rw [fairBitBlocks_law R L (fun row shift => f (bitIndex R row) (bitIndex L shift))]
  have hFamily : (fun scalar : Fin L → Bool => (fairBitLaw R).map (fun row => f (bitIndex R row) (bitIndex L scalar)))=
      (fun scalar : Fin L → Bool => (fun l => GeneralPaperUniformRowLaw.law (Nat.two_pow_pos R) (fun i => f i l)) (bitIndex L scalar)) := by
    funext scalar
    exact GeneralPaperFairIndexLaw.uniform R (fun i => f i (bitIndex L scalar))
  simp only [hFamily]
  rw [averaged_fairBit_indices L (fun l => GeneralPaperUniformRowLaw.law (Nat.two_pow_pos R) (fun i => f i l))]
  exact (commute (Nat.two_pow_pos R) (Nat.two_pow_pos L) f).symm

theorem native {n : ℕ} (primitive : ℕ → ℕ) (A R L T S : ℕ) (hT : T=2^R) (hS : S=2^L)
    (f : Fin T → Fin S → Allocation n) :
    (fairBitLaw (R+L)).map (fun bits =>
      let selected := GeneralPaperNativeDyadicBlocks.run primitive A R L T S hT hS (FixedArrayTable.ofFn bits)
      f selected.row selected.shift)=
      GeneralPaperUniformRowLaw.mixture (hT ▸ Nat.two_pow_pos R) (fun i =>
        GeneralPaperUniformRowLaw.law (hS ▸ Nat.two_pow_pos L) (f i)) := by
  subst T
  subst S
  simp only [GeneralPaperNativeDyadicBlocks.row_data,GeneralPaperNativeDyadicBlocks.shift_data,Fin.cast_refl]
  exact indices R L f

end Blotto.GeneralPaperFairRowShiftLaw
