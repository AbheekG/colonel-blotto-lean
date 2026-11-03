import Blotto.GeneralPaperBasisResidualSign

/-! Propagate feasibility of the actual full original basis across a
root-free threshold interval. Constant residuals and identities are
discharged separately; the nonconstant coefficient roots are the only
interval premises and are instantiated by actual classifier bounds next.
-/
namespace Blotto.GeneralPaperBasisIntervalFeasibility
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisSelectedRows GeneralPaperBasisCoordinates GeneralPaperBasisAffineData GeneralPaperBasisAffineSystem
open GeneralPaperBasisResidualSign
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem propagate {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (lo hi : ℝ) (hOrder : lo≤hi)
    (hStart : GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h lo
      (fun a => value (prepare state) lo (index a)))
    (hNonconstant : ∀ extra : Index T m K (score v S) h,
      (GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
        (selected dict v S h N betaN initialGrid state inv) extra).2≠0 →
          ∀ gamma : ℝ,lo≤gamma ∧ gamma<hi →
            ((GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
              (selected dict v S h N betaN initialGrid state inv) extra).1:ℝ)+
                gamma*((GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
                  (selected dict v S h N betaN initialGrid state inv) extra).2:ℝ)≠0) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h hi
      (fun a => value (prepare state) hi (index a)) := by
  intro extra
  apply sub_nonpos.mp
  change residual (constraints dict.label (score v S) h extra) (prepare state) hi≤0
  let coeff := GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
    (selected dict v S h N betaN initialGrid state inv) extra
  by_cases hB : coeff.2=0
  · by_cases hA : coeff.1=0
    · have hh := GeneralPaperBasisAffineOriginal.residual_identity dict v S h N betaN initialGrid state inv hi extra
      change (state.determinant:ℝ)*residual (constraints dict.label (score v S) h extra) (prepare state) hi=
        (coeff.1:ℝ)+hi*(coeff.2:ℝ) at hh
      simp only [hA,hB,Int.cast_zero,mul_zero,add_zero] at hh
      have hd : (state.determinant:ℝ)≠0 := by exact_mod_cast inv.nonzero
      exact ((mul_eq_zero.mp hh).resolve_left hd).le
    · apply preserves _ _ lo hi hOrder (sub_nonpos.mpr (hStart extra))
      intro gamma _
      apply GeneralPaperTransferActualResidualPaths.residual_nonzero dict.label (score v S) h
        (selected dict v S h N betaN initialGrid state inv) extra gamma _
        (GeneralPaperBasisAffineOriginal.selected_system dict v S h N betaN initialGrid state inv gamma)
      change (coeff.1:ℝ)+gamma*(coeff.2:ℝ)≠0
      simp only [hB,Int.cast_zero,mul_zero,add_zero]
      exact_mod_cast hA
  · apply preserves _ _ lo hi hOrder (sub_nonpos.mpr (hStart extra))
    intro gamma hGamma
    apply GeneralPaperTransferActualResidualPaths.residual_nonzero dict.label (score v S) h
      (selected dict v S h N betaN initialGrid state inv) extra gamma _
      (GeneralPaperBasisAffineOriginal.selected_system dict v S h N betaN initialGrid state inv gamma)
    exact hNonconstant extra hB gamma hGamma

end Blotto.GeneralPaperBasisIntervalFeasibility
