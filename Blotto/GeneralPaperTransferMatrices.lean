import Blotto.GeneralPaperAffineConstraintMass
import Blotto.FinitePolytopeRationalWitness

/-! Actual defining and augmented integer matrices for every selected
transfer subsystem and every tested constraint. Their dimension is exactly
m(K-1), with fixed zero anchors omitted. These are proof observers of the
original constraints, not matrices supplied as an execution oracle.
-/
namespace Blotto.GeneralPaperTransferMatrices
open RationalOrderCell GeneralPaperAffineConstraintRows GeneralPaperAffineConstraintMass
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def matrix {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h) :
    Matrix (Variable m K) (Variable m K) ℤ :=
  fun i j => (constraints labels scores h (selected i)).coefficient j

def extended {T m K : ℕ} {scores : Fin m → Fin K → ℕ} {h : ℕ}
    (selected : Variable m K → Index T m K scores h) (extra : Index T m K scores h) :
    Option (Variable m K) → Index T m K scores h
  | none => extra
  | some i => selected i

noncomputable def augmentedRow {v : Type*} [DecidableEq v] (r : Row v) (useSlope : Bool) : Option v → ℤ
  | none => rhs r useSlope
  | some j => r.coefficient j

noncomputable def bordered {T m K : ℕ} (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (useSlope : Bool) : Matrix (Option (Variable m K)) (Option (Variable m K)) ℤ :=
  fun i j => augmentedRow (constraints labels scores h (extended selected extra i)) useSlope j

theorem bordered_row_mass {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (useSlope : Bool) (i : Option (Variable m K)) :
    (∑ j,((bordered labels scores h selected extra useSlope) i j).natAbs)≤m+1 := by
  rw [Fintype.sum_option]
  simpa only [bordered,augmentedRow,Nat.add_comm] using augmented_mass hm labels scores h (extended selected extra i) useSlope

theorem bordered_determinant {T m K : ℕ} (hm : 0<m) (labels : Fin T → Fin m → Fin K)
    (scores : Fin m → Fin K → ℕ) (h : ℕ) (selected : Variable m K → Index T m K scores h)
    (extra : Index T m K scores h) (useSlope : Bool) :
    (bordered labels scores h selected extra useSlope).det.natAbs≤(m+1)^(m*(K-1)+1) := by
  apply (FinitePolytopeRationalWitness.det_natAbs_le_rowMass _).trans
  have hp := Finset.prod_le_prod (s:=Finset.univ) (fun i _ => bordered_row_mass hm labels scores h selected extra useSlope i)
  simpa only [Finset.prod_const,Finset.card_univ,Fintype.card_option,variable_card] using hp

end Blotto.GeneralPaperTransferMatrices
