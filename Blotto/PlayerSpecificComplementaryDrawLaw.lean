import Blotto.PlayerSpecificTerminalEmbeddingLaw
import Blotto.DyadicMidpointLaw

/-! The actual two-group complementary draw has exactly the finite
midpoint segment law in its four-slot layout. -/
namespace Blotto.PlayerSpecificComplementaryDrawLaw
open MeasureTheory PlayerSpecificSturmVariations PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

noncomputable def first (B : ℝ) : Allocation 4 := ![0,B,0,0]
noncomputable def second (B : ℝ) : Allocation 4 := ![B,0,0,0]
noncomputable def reference (B : ℝ) : Mixed 4 := segmentLaw (first B) (second B)

noncomputable def law (root : Candidate) (budget : PlayerSpecificDensePolynomial.Data) (K : ℕ) (x : ℝ) : Mixed 4 :=
  (fairBitLaw K).map (fun bits => values (PlayerSpecificAlgebraicComplementaryDraw.draw root budget K bits) x)

theorem law_eq (root : Candidate) (budget : PlayerSpecificDensePolynomial.Data) (K : ℕ) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) :
    law root budget K x=dyadicSegmentLaw K (first (realEvaluate budget x)) (second (realEvaluate budget x)) := by
  apply ProbabilityMeasure.toMeasure_injective
  change Measure.map (fun bits => values (PlayerSpecificAlgebraicComplementaryDraw.draw root budget K bits) x) _=
    Measure.map (dyadicSegmentPoint K (first (realEvaluate budget x)) (second (realEvaluate budget x))) _
  congr 1
  funext bits
  rw [PlayerSpecificAlgebraicComplementaryDraw.value root budget K bits x hx]
  funext j
  fin_cases j <;> simp [PlayerSpecificAlgebraicComplementaryDraw.point,dyadicSegmentPoint,first,second,segmentPoint] <;> ring

theorem CDF_error (root : Candidate) (budget : PlayerSpecificDensePolynomial.Data) (K : ℕ) (x : ℝ)
    (hx : realEvaluate root.polynomial x=0) :
    CDFClose (law root budget K x) (reference (realEvaluate budget x)) (1/(2*(2:ℝ)^K)) := by
  rw [law_eq root budget K x hx]
  exact dyadicSegmentLaw_CDF_error K _ _

theorem first_marginals (B : ℝ) (hB : 0 < B) (j : Fin 2) :
    (marginal (reference B) j.castSucc.castSucc : Measure ℝ)=uniformLaw B := by
  fin_cases j <;> simp [reference,first,second,segmentLaw_marginal,
    affineUniform_reverse B 0,affineUniform_zero_uniformLaw hB]

end Blotto.PlayerSpecificComplementaryDrawLaw
