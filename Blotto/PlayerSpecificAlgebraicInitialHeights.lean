import Blotto.PlayerSpecificAlgebraicHeightEnvelope

/-! Every initial field uses only three fixed layers of actual algebraic
growth. The number of coordinates never enters this exponent. -/
namespace Blotto.PlayerSpecificAlgebraicInitialHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicInitial
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def height (H : ℕ) : ℕ := iterate 3 H

theorem component_heights (model : RationalCostModel) (candidate : Candidate) (v w : ℚ) (H : ℕ)
    (hm : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) (hml : candidate.polynomial.length≤4)
    (hmH : HasHeight candidate.polynomial H) (hv : RationalHeight v H) (hw : RationalHeight w H) (hH : 1≤H) :
    HasHeight (numerator model candidate v w) (step H) ∧
      HasHeight (probabilityA model candidate v w) (step (step H)) ∧
      HasHeight (probabilityB model candidate v w) (step (step H)) := by
  have hg:=large H
  have hg2:=large (step H)
  have hc:=constant_height candidate.polynomial v H hmH hv hH hml
  have hgw : HasHeight (weighted candidate w) (step H) :=
    reduce_height candidate.polynomial [0,w] H hmH
      (cons_height (zero_height.mono hH) (cons_height hw (nil_height _))) hH hml (by simp)
  have hone:=constant_height candidate.polynomial 1 H hmH (one_height.mono hH) hH hml
  have hcR:=PlayerSpecificAlgebraicField.constant_reduced candidate.polynomial v hm hm0
  have hgwR:=weighted_reduced candidate w hm hm0
  have hmStep:=PlayerSpecificPolynomialHeights.mono hmH (by omega : H≤step H)
  have hdivA:=divide_height candidate.polynomial _ _ (step H) hm hm0 hml hcR hgwR hmStep hc hgw (by omega)
  have hdivB:=divide_height candidate.polynomial _ _ (step H) hm hm0 hml hgwR hcR hmStep hgw hc (by omega)
  refine ⟨?_,?_,?_⟩
  · simp only [numerator]; split <;> assumption
  · simp only [probabilityA]; split
    · exact hdivA
    · exact PlayerSpecificPolynomialHeights.mono hone (by omega)
  · simp only [probabilityB]; split
    · exact PlayerSpecificPolynomialHeights.mono hone (by omega)
    · exact hdivB

theorem result_heights (model : RationalCostModel) (candidate : Candidate) (inverseScale : Data) (v w : ℚ) (H : ℕ)
    (hm : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) (hml : candidate.polynomial.length≤4)
    (hmH : HasHeight candidate.polynomial H) (hv : RationalHeight v H) (hw : RationalHeight w H) (hH : 1≤H)
    (hinv : Reduced candidate.polynomial inverseScale) (hinvH : HasHeight inverseScale (step H)) :
    HasHeight (run model candidate inverseScale v w).length (height H) ∧
      HasHeight (run model candidate inverseScale v w).initialA (height H) ∧
      HasHeight (run model candidate inverseScale v w).initialB (height H) := by
  have hg:=large H
  have hg2:=large (step H)
  have hg3:=large (step (step H))
  have hparts:=component_heights model candidate v w H hm hm0 hml hmH hv hw hH
  have hn : Reduced candidate.polynomial (numerator model candidate v w) := by
    simp only [numerator]
    split
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
    · exact weighted_reduced candidate w hm hm0
  have hpA : Reduced candidate.polynomial (probabilityA model candidate v w) := by
    simp only [probabilityA]
    split
    · exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
  have hpB : Reduced candidate.polynomial (probabilityB model candidate v w) := by
    simp only [probabilityB]
    split
    · exact PlayerSpecificAlgebraicField.constant_reduced _ _ hm hm0
    · exact PlayerSpecificAlgebraicField.divide_reduced _ _ _ hm hm0
  have hlR:=(reduced_result model candidate inverseScale v w hm hm0).1
  have hmStep:=PlayerSpecificPolynomialHeights.mono hmH (by omega : H≤step H)
  have hl : HasHeight (run model candidate inverseScale v w).length (step (step H)) := by
    rw [run_length]
    exact times_height candidate.polynomial _ _ (step H) hm hm0 hml hn hinv hmStep hparts.1 hinvH
  have hmStep2:=PlayerSpecificPolynomialHeights.mono hmH (by omega : H≤step (step H))
  have ha : HasHeight (run model candidate inverseScale v w).initialA (step (step (step H))) := by
    rw [run_initialA]
    exact times_height candidate.polynomial _ _ (step (step H)) hm hm0 hml hpA hlR hmStep2 hparts.2.1 hl
  have hb : HasHeight (run model candidate inverseScale v w).initialB (step (step (step H))) := by
    rw [run_initialB]
    exact times_height candidate.polynomial _ _ (step (step H)) hm hm0 hml hpB hlR hmStep2 hparts.2.2 hl
  exact ⟨PlayerSpecificPolynomialHeights.mono hl ((Nat.le_succ _).trans hg3),ha,hb⟩

theorem linear_height (H : ℕ) : height H≤(PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3*(H+1) := by
  have hh:=iterate_bound 3 H
  unfold height
  omega

end Blotto.PlayerSpecificAlgebraicInitialHeights
