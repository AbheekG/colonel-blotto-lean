import Blotto.GeneralPaperBorderedDeterminant

/-! Real affine bordered matrices of the actual transfer constraints.
Their determinants are affine in gamma because ONLY the RHS column varies.
Both integer determinant coefficients use the original constraint rows.
-/
namespace Blotto.GeneralPaperTransferResidualMatrix
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperAffineConstraintMass GeneralPaperTransferMatrices
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def realBorder {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) : Matrix (Option (Variable m K)) (Option (Variable m K)) ℝ :=
  fun i j => match j with
    | none => (constraints labels scores h (extended selected extra i)).bound gamma
    | some j => ((constraints labels scores h (extended selected extra i)).coefficient j:ℝ)

noncomputable def integerBorder {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (useSlope : Bool) :=
  (Int.castRingHom ℝ).mapMatrix (bordered labels scores h selected extra useSlope)

theorem rhs_update {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) :
    realBorder labels scores h selected extra gamma=
      (integerBorder labels scores h selected extra false).updateCol none
        (fun i => integerBorder labels scores h selected extra false i none+
          gamma*integerBorder labels scores h selected extra true i none) := by
  ext i j
  cases j <;> rfl

theorem component_update {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) :
    (integerBorder labels scores h selected extra false).updateCol none
      (fun i => integerBorder labels scores h selected extra true i none)=
        integerBorder labels scores h selected extra true := by
  ext i j
  cases j <;> rfl

theorem determinant_affine {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (gamma : ℝ) :
    (realBorder labels scores h selected extra gamma).det=
      ((bordered labels scores h selected extra false).det:ℝ)+
        gamma*((bordered labels scores h selected extra true).det:ℝ) := by
  rw [rhs_update]
  change ((integerBorder labels scores h selected extra false).updateCol none
    ((fun i => integerBorder labels scores h selected extra false i none)+
      gamma • (fun i => integerBorder labels scores h selected extra true i none))).det=_
  rw [Matrix.det_updateCol_add,Matrix.det_updateCol_smul,Matrix.updateCol_eq_self,component_update]
  simp only [integerBorder,←(Int.castRingHom ℝ).map_det]
  rfl

end Blotto.GeneralPaperTransferResidualMatrix
