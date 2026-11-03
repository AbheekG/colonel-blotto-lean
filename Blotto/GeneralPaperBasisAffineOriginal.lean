import Blotto.GeneralPaperBasisAffineSystem

/-! The cached affine continuation solves the actual selected original
equations, agrees with the feasible auxiliary vertex, and has the exact
bounded integer residual coefficients already used by the classifier.
-/
namespace Blotto.GeneralPaperBasisAffineOriginal
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperStrictScore
open GeneralPaperBasisStoredProducts GeneralPaperBasisState GeneralPaperBasisInvariant
open GeneralPaperBasisSelectedRows GeneralPaperBasisCoordinates GeneralPaperBasisAffineData GeneralPaperBasisAffineSystem
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem selected_system {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (gamma : ℝ) (a : Variable m K) :
    (constraints dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv a)).linear.evaluate
      (fun c => value (prepare state) gamma (index c))=
      (constraints dict.label (score v S) h (selected dict v S h N betaN initialGrid state inv a)).bound gamma := by
  have hh := row_system state inv.nonzero inv.cache gamma (index a)
  rw [selected_row dict v S h N betaN initialGrid state inv a] at hh
  unfold GeneralPaperBasisFreshPointSound.rowValue at hh
  rw [GeneralPaperBasisDenseRow.build_evaluate] at hh
  simpa only [Row.bound,GeneralPaperBasisDenseRow.build_constant,GeneralPaperBasisDenseRow.build_slope] using hh

theorem initial_point {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    value (prepare state) ((betaN:ℝ)/(N:ℝ))=
      GeneralPaperBasisFreshPointSound.values N betaN state.determinant state.adjugate state.rows initialGrid := by
  apply GeneralPaperBasisFull.unique_real_point dict v S h N hN betaN initialGrid state inv
  intro i
  exact row_system state inv.nonzero inv.cache _ i

theorem initial_feasible {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (hN : 0<N) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) :
    GeneralPaperAffineConstraintRows.Feasible dict.label (score v S) h ((betaN:ℝ)/(N:ℝ))
      (fun a => value (prepare state) ((betaN:ℝ)/(N:ℝ)) (index a)) := by
  rw [initial_point dict v S h N hN betaN initialGrid state inv]
  exact inv.feasible

theorem residual_identity {T m K : ℕ} (dict : GeneralPaperDictionary.Dictionary T m K) (v : RationalFieldSelector m)
    (S h N : ℕ) (betaN : ℤ) (initialGrid : Vector (m*(K-1))) (state : State (m*(K-1)) (m*(K-1)))
    (inv : Invariant dict v S h N betaN initialGrid (Nat.le_refl _) state) (gamma : ℝ)
    (extra : Index T m K (score v S) h) :
    (state.determinant:ℝ)*((constraints dict.label (score v S) h extra).linear.evaluate
      (fun a => value (prepare state) gamma (index a))-(constraints dict.label (score v S) h extra).bound gamma)=
      ((GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
        (selected dict v S h N betaN initialGrid state inv) extra).1:ℝ)+
          gamma*((GeneralPaperTransferResidualCoefficients.coefficients dict.label (score v S) h
            (selected dict v S h N betaN initialGrid state inv) extra).2:ℝ) := by
  have hh := GeneralPaperTransferResidualCoefficients.residual_identity dict.label (score v S) h
    (selected dict v S h N betaN initialGrid state inv) extra gamma _ (selected_system dict v S h N betaN initialGrid state inv gamma)
  rwa [determinant_identity dict v S h N betaN initialGrid state inv] at hh

end Blotto.GeneralPaperBasisAffineOriginal
