import Blotto.GeneralPaperTransferResidualMatrix

/-! Exact integer affine residual coefficients of the ACTUAL selected
constraint subsystem. They are negative bordered determinants, hence their
uniform H bounds are derived internally. The identity holds for any actual
solution, including an active vertex on a lower-dimensional feasible face.
-/
namespace Blotto.GeneralPaperTransferResidualCoefficients
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperTransferMatrices GeneralPaperTransferResidualMatrix
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def coefficients {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) : ℤ × ℤ :=
  ⟨-(bordered labels scores h selected extra false).det,-(bordered labels scores h selected extra true).det⟩

theorem residual_identity {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) (x : Variable m K → ℝ)
    (hSystem : ∀ i,(constraints labels scores h (selected i)).linear.evaluate x=
      (constraints labels scores h (selected i)).bound gamma) :
    ((matrix labels scores h selected).det:ℝ)*
      ((constraints labels scores h extra).linear.evaluate x-(constraints labels scores h extra).bound gamma)=
      ((coefficients labels scores h selected extra).1:ℝ)+
        gamma*((coefficients labels scores h selected extra).2:ℝ) := by
  have hs (i : Variable m K) : realBorder labels scores h selected extra gamma (some i) none=
      ∑ j,realBorder labels scores h selected extra gamma (some i) (some j)*x j := by
    change (constraints labels scores h (selected i)).bound gamma=
      ∑ j,((constraints labels scores h (selected i)).linear.coefficient j:ℝ)*x j
    rw [←LinearRow.evaluate_coefficients]
    exact (hSystem i).symm
  have hb := GeneralPaperBorderedDeterminant.determinant_of_solution (realBorder labels scores h selected extra gamma) x hs
  have hMinor : (realBorder labels scores h selected extra gamma).submatrix some some=
      (Int.castRingHom ℝ).mapMatrix (matrix labels scores h selected) := rfl
  rw [determinant_affine,hMinor,←(Int.castRingHom ℝ).map_det] at hb
  have he : (∑ j,((constraints labels scores h extra).coefficient j:ℝ)*x j)=
      (constraints labels scores h extra).linear.evaluate x := by
    exact (LinearRow.evaluate_coefficients (constraints labels scores h extra).linear x).symm
  change ((bordered labels scores h selected extra false).det:ℝ)+
    gamma*((bordered labels scores h selected extra true).det:ℝ)=
      ((matrix labels scores h selected).det:ℝ)*((constraints labels scores h extra).bound gamma-
        ∑ j,((constraints labels scores h extra).coefficient j:ℝ)*x j) at hb
  rw [he] at hb
  simp only [coefficients,Int.cast_neg]
  nlinarith only [hb]

theorem coefficient_bounds {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) :
    (coefficients labels scores h selected extra).1.natAbs<(m+2)^(m*(K-1)+1) ∧
      (coefficients labels scores h selected extra).2.natAbs<(m+2)^(m*(K-1)+1) := by
  simpa only [coefficients,Int.natAbs_neg] using
    And.intro (GeneralPaperTransferDeterminantBounds.bordered_strict hm labels scores h selected extra false)
      (GeneralPaperTransferDeterminantBounds.bordered_strict hm labels scores h selected extra true)

theorem coefficient_H {T m : ℕ} (k : ℕ) (hm : 0<m)
    (labels : Fin T → Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K)
    (scores : Fin m → Fin (GeneralPaperProxyParameters.prepare m k).K → ℕ) (h : ℕ)
    (selected : Variable m (GeneralPaperProxyParameters.prepare m k).K →
      Index T m (GeneralPaperProxyParameters.prepare m k).K scores h)
    (extra : Index T m (GeneralPaperProxyParameters.prepare m k).K scores h) :
    (coefficients labels scores h selected extra).1.natAbs<(GeneralPaperProxyParameters.prepare m k).H ∧
      (coefficients labels scores h selected extra).2.natAbs<(GeneralPaperProxyParameters.prepare m k).H := by
  simpa only [coefficients,Int.natAbs_neg] using
    And.intro (GeneralPaperTransferDeterminantBounds.bordered_H k hm labels scores h selected extra false)
      (GeneralPaperTransferDeterminantBounds.bordered_H k hm labels scores h selected extra true)

end Blotto.GeneralPaperTransferResidualCoefficients
