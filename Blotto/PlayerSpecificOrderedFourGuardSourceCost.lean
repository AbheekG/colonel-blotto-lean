import Blotto.PlayerSpecificOrderedFourDrawExecution

/-! Complete source price of the ordered four-variable threshold and exact
comparison, with the threshold height derived from the executed program. -/
namespace Blotto.PlayerSpecificOrderedFourGuardSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicHeightEnvelope
open PlayerSpecificAlgebraicFourInput
set_option autoImplicit false
set_option maxHeartbeats 2500000

def thresholdHeight (T : ℕ) : ℕ :=
  PlayerSpecificExpressionVectorSourceCost.size (iterate 2 T) 2 1 1

def work (T : ℕ) : ℕ :=
  PlayerSpecificMixtureScalarSourceCost.complementCoefficient*(T+13)^3+
  PlayerSpecificMixtureScalarSourceCost.scaleCoefficient*(iterate 2 T+14)^3+
  PlayerSpecificAlgebraicComparisonCost.comparisonCoefficient*(thresholdHeight T+1)^3+2

theorem cost (r : PlayerSpecificFiniteParameterReturn.Result) (a : Input) (T : ℕ)
    (hm : Normalized r.root.polynomial) (hm0 : r.root.polynomial ≠ [])
    (hml : r.root.polynomial.length ≤ 4) (hmT : HasHeight r.root.polynomial T)
    (he : HasHeight [r.root.interval.lo,r.root.interval.hi] T)
    (hv : r.root.interval.lo < r.root.interval.hi) (hT : 2 ≤ T)
    (ha : Fits r.root a T) :
    (PlayerSpecificOrderedFourDrawExecution.guard r a).2 ≤ work T := by
  let model := RationalCostModel.schoolbook
  let U := iterate 2 T
  let S := thresholdHeight T
  let comp := PlayerSpecificMixtureScalarExecution.complement model r.root a.probability
  let scaled := PlayerSpecificMixtureScalarExecution.scale model r.root comp.1 a.length
  let cmp := PlayerSpecificAlgebraicComparisonExecution.run model r.root scaled.1 a.third
  have hTU : T ≤ U := PlayerSpecificAlgebraicExpressionBudget.initial_le 2 T
  have hUS : U ≤ S := (PlayerSpecificExpressionVectorSourceCost.lower U 2 1 1).1
  have hcomp := PlayerSpecificMixtureScalarSourceCost.complement_bounds model r.root a.probability T
    hm hm0 hml hmT (by omega) ha.probability
  have hc := PlayerSpecificMixtureScalarSourceCost.complement_cost r.root a.probability T
    hm hm0 hml hmT he hv (by omega) ha.probability
  have hs := PlayerSpecificMixtureScalarSourceCost.scale_cost r.root comp.1 a.length U
    hm hm0 hml (mono hmT hTU) (mono he hTU) hv hcomp
    ⟨ha.length.1,mono ha.length.2 hTU⟩
  have henv : ∀ j, Reduced r.root.polynomial
      ((PlayerSpecificMixtureScalarExecution.twoEnvironment comp.1 a.length).read j) ∧
      HasHeight ((PlayerSpecificMixtureScalarExecution.twoEnvironment comp.1 a.length).read j) U := by
    intro j
    fin_cases j
    · simpa [PlayerSpecificMixtureScalarExecution.twoEnvironment,FixedArrayTable.read_ofFn] using hcomp
    · simpa [PlayerSpecificMixtureScalarExecution.twoEnvironment,FixedArrayTable.read_ofFn] using
        (And.intro ha.length.1 (mono ha.length.2 hTU))
  have hscaled := PlayerSpecificExpressionVectorSourceCost.heights model r.root
    (PlayerSpecificMixtureScalarExecution.twoEnvironment comp.1 a.length)
    PlayerSpecificMixtureScalarExecution.scalePrograms U 1 hm hm0 hml (mono hmT hTU)
    henv PlayerSpecificMixtureScalarExecution.scale_depth
    (fun j => PlayerSpecificMixtureScalarExecution.scale_literals j U)
  have hscaled' : Reduced r.root.polynomial scaled.1 ∧ HasHeight scaled.1 S := by
    simpa only [scaled,S,thresholdHeight,U,PlayerSpecificMixtureScalarExecution.scale,
      PlayerSpecificExpressionVectorExecution.read_value,
      PlayerSpecificMixtureScalarExecution.scalePrograms,FixedArrayTable.read_ofFn] using hscaled 0
  have hcmp := PlayerSpecificAlgebraicComparisonCost.comparison r.root scaled.1 a.third S
    hm hm0 hml (mono hmT (hTU.trans hUS)) (mono he (hTU.trans hUS)) hv
    hscaled'.2 (mono ha.third.2 (hTU.trans hUS))
    (by have h := hscaled'.1.2; omega) (by have h := ha.third.1.2; omega) (by omega)
  change comp.2 + scaled.2 + cmp.2 +
    PlayerSpecificRationalTrace.price model [.control 1] ≤ _
  rw [show PlayerSpecificRationalTrace.price model [.control 1] = 2 by rfl]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc hs) hcmp) 2

end Blotto.PlayerSpecificOrderedFourGuardSourceCost
