import Blotto.PlayerSpecificAlgebraicNestedTerminalDraw

/-! Native reflection subtracts inside the reached long-length box and
appends literal zero. It adds only one coefficient-height layer. -/
namespace Blotto.PlayerSpecificAlgebraicReflectAppend
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false

def reflect (root : Candidate) (long y : FixedArrayTable 3 Data) : FixedArrayTable 4 Data :=
  FixedArrayTable.ofFn ![PlayerSpecificAlgebraicField.minus root.polynomial (long.read 0) (y.read 0),
    PlayerSpecificAlgebraicField.minus root.polynomial (long.read 1) (y.read 1),
    PlayerSpecificAlgebraicField.minus root.polynomial (long.read 2) (y.read 2),[]]

theorem value (root : Candidate) (long y : FixedArrayTable 3 Data) (x : ℝ) (hx : realEvaluate root.polynomial x=0) :
    values (reflect root long y) x=reflectAppend (values long x) (values y x) := by
  funext j
  fin_cases j <;> simp [reflect,values,FixedArrayTable.read_ofFn,reflectAppend,PlayerSpecificAlgebraicField.minus_value _ _ _ x hx]
  rfl

theorem bounds (root : Candidate) (long y : FixedArrayTable 3 Data) (T : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ [])
    (hLong : ∀ j,Reduced root.polynomial (long.read j) ∧ HasHeight (long.read j) T)
    (hy : ∀ j,Reduced root.polynomial (y.read j) ∧ HasHeight (y.read j) T) :
    ∀ j,Reduced root.polynomial ((reflect root long y).read j) ∧ HasHeight ((reflect root long y).read j) (step T) := by
  have hshort : T+T+1 ≤ step T := by
    have h := calibrate 3 T (by unfold PlayerSpecificAlgebraicHeightEnvelope.coefficient; omega)
    omega
  have hrow : ∀ j,Reduced root.polynomial (PlayerSpecificAlgebraicField.minus root.polynomial (long.read j) (y.read j)) ∧
      HasHeight (PlayerSpecificAlgebraicField.minus root.polynomial (long.read j) (y.read j)) (step T) := by
    intro j
    exact ⟨PlayerSpecificAlgebraicField.minus_reduced _ _ _ hm hm0,
      mono (PlayerSpecificShortReduction.minus_height _ _ _ hm hm0 (hLong j).1 (hy j).1 T T (hLong j).2 (hy j).2) hshort⟩
  intro j
  fin_cases j <;> simp only [reflect,FixedArrayTable.read_ofFn]
  · exact hrow 0
  · exact hrow 1
  · exact hrow 2
  · exact ⟨nil_reduced _ hm0,nil_height _⟩

end Blotto.PlayerSpecificAlgebraicReflectAppend
