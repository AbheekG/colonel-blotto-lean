import Blotto.PlayerSpecificAlgebraicFourGluingSizes

/-! Actual four-variable normal-branch table. Parameters and both parent
tables are prepared once, then the finite overlap array is materialized. -/
namespace Blotto.PlayerSpecificAlgebraicFourGluingTable
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicFourInput
open PlayerSpecificAlgebraicFourGluingInputs PlayerSpecificAlgebraicDescriptorBounds PlayerSpecificAlgebraicDescriptorReference
open PlayerSpecificAlgebraicSegment
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def prepare (model : RationalCostModel) (root : Candidate) (a : Input) : Descriptor 4 81 :=
  let p := parameters model root a
  let l := PlayerSpecificAlgebraicUnorderedThree.prepare model root (first root a p)
  let r := PlayerSpecificAlgebraicUnorderedThree.prepare model root (second a p)
  PlayerSpecificAlgebraicOverlapTable.prepare model root l r (p.read 1) a.budget

theorem environment_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) :
    ∀ i j r,Reduced root.polynomial ((PlayerSpecificAlgebraicOverlapEnvironment.environment
      (PlayerSpecificAlgebraicUnorderedThree.prepare model root (first root a (parameters model root a)))
      (PlayerSpecificAlgebraicUnorderedThree.prepare model root (second a (parameters model root a)))
      ((parameters model root a).read 1) a.budget i j).read r) ∧
      HasHeight ((PlayerSpecificAlgebraicOverlapEnvironment.environment
        (PlayerSpecificAlgebraicUnorderedThree.prepare model root (first root a (parameters model root a)))
        (PlayerSpecificAlgebraicUnorderedThree.prepare model root (second a (parameters model root a)))
        ((parameters model root a).read 1) a.budget i j).read r) (iterate 33 T) := by
  have hp := PlayerSpecificAlgebraicFourGluingSizes.parents model root a T ha hm hm0 hml hmT hT
  have hi := parameter_bounds model root a T ha hm hm0 hml hmT hT 1
  have h1333 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 13 ≤ 33)
  have h033 := PlayerSpecificAlgebraicExpressionBudget.initial_le 33 T
  exact PlayerSpecificAlgebraicOverlapEnvironment.bounds root _ _ _ _ (iterate 33 T) hp.1 hp.2
    ⟨hi.1,mono hi.2 h1333⟩ ⟨ha.budget.1,mono ha.budget.2 h033⟩

theorem refines (model : RationalCostModel) (root : Candidate) (a : Input) (i : FourInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo < root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicFourInput.Values a i x) (T : ℕ) (hfit : Fits root a T)
    (hml : root.polynomial.length ≤ 4) (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T)
    (hcase : (1-i.p)*i.ell ≤ i.w) : Refines (prepare model root a) x (i.gluingDescriptor hcase) := by
  have hm0 : root.polynomial ≠ [] := by intro hz; exact hirr.ne_zero (by rw [hz]; rfl)
  let p := parameters model root a
  let l := PlayerSpecificAlgebraicUnorderedThree.prepare model root (first root a p)
  let r := PlayerSpecificAlgebraicUnorderedThree.prepare model root (second a p)
  have hp := parameter_value model root a i hm hirr hv x hx ha T hfit
  have hl := PlayerSpecificAlgebraicNestedSpecInput.three_refines model root (first root a p) (i.gluingFirstSpec hcase)
    hm hirr hv x hx (first_value root a p i x hx.1 ha hp hcase)
  have hr := PlayerSpecificAlgebraicNestedSpecInput.three_refines model root (second a p) (i.gluingSecondSpec hcase)
    hm hirr hv x hx (second_value a p i x ha hp hcase)
  have he := environment_bounds model root a T hfit hm hm0 hml hmT hT
  exact PlayerSpecificAlgebraicOverlapTable.refines model root l r (p.read 1) a.budget hm hirr hv x hx
    (i.overlapData hcase) i.B hl hr (hp 1) ha.budget (fun a b c => (he a b c).1) rfl rfl

theorem bounds (model : RationalCostModel) (root : Candidate) (a : Input) (T : ℕ) (ha : Fits root a T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial ≠ []) (hml : root.polynomial.length ≤ 4)
    (hmT : HasHeight root.polynomial T) (hT : 2 ≤ T) : Bounds root (prepare model root a) (iterate 43 T) := by
  have hp := PlayerSpecificAlgebraicFourGluingSizes.parents model root a T ha hm hm0 hml hmT hT
  have hi := parameter_bounds model root a T ha hm hm0 hml hmT hT 1
  have h1333 := PlayerSpecificAlgebraicExpressionBudget.fuel_mono T (by omega : 13 ≤ 33)
  have h033 := PlayerSpecificAlgebraicExpressionBudget.initial_le 33 T
  have hb := PlayerSpecificAlgebraicOverlapTable.bounds model root _ _ _ _ (iterate 33 T) hp.1 hp.2
    ⟨hi.1,mono hi.2 h1333⟩ ⟨ha.budget.1,mono ha.budget.2 h033⟩ hm hm0 hml (mono hmT h033) (hT.trans h033)
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add] at hb
  exact hb

end Blotto.PlayerSpecificAlgebraicFourGluingTable
