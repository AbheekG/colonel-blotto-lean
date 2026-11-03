import Blotto.PlayerSpecificSegmentAssemblyProperties

/-! Actual fixed-mean nested family parameters. The short length is
replaced by the reached algebraic scalar, and its probability is computed
by the retained exact local program. -/
namespace Blotto.PlayerSpecificAlgebraicNestedFamily
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificSturmVariations PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicHeightEnvelope PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
open PlayerSpecificAlgebraicCandidates (Candidate)
set_option autoImplicit false
set_option maxHeartbeats 2500000

def family (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) : Input :=
  ⟨a.budget,a.first,a.second,a.long,short,scalar model root a short 2⟩

theorem value (model : RationalCostModel) (root : Candidate) (a : Input) (i : NestedInput)
    (hm : Normalized root.polynomial) (hirr : Irreducible (semantics root.polynomial))
    (hv : root.interval.lo<root.interval.hi) (x : ℝ)
    (hx : PlayerSpecificSelectedRefinement.Unique root.polynomial root.interval x)
    (ha : PlayerSpecificAlgebraicNestedInput.Values a i x) (short : Data)
    (hEnv : ∀ j,Reduced root.polynomial ((environment a short).read j))
    (hx0 : 0<realEvaluate short x) (hxuv : realEvaluate short x< i.u+i.v) :
    PlayerSpecificAlgebraicNestedInput.Values (family model root a short) (i.atLength (realEvaluate short x) hx0 hxuv) x := by
  refine ⟨ha.budget,ha.first,ha.second,ha.long,rfl,?_⟩
  have he:=scalar_value model root a i hm hirr hv x hx ha short hEnv 2
  simpa [family,RealNestedParametersCode.scalarValues,NestedInput.atLength] using he

theorem fits (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (T : ℕ)
    (hfit : Fits root a T) (hshort : Reduced root.polynomial short ∧ HasHeight short T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) : Fits root (family model root a short) (iterate 9 T) := by
  have hs:=scalar_bounds model root a short T hfit hshort hm hm0 hml hmT hT 2
  have hinc:=PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T
  exact ⟨⟨hfit.budget.1,mono hfit.budget.2 hinc⟩,⟨hfit.first.1,mono hfit.first.2 hinc⟩,
    ⟨hfit.second.1,mono hfit.second.2 hinc⟩,⟨hfit.long.1,mono hfit.long.2 hinc⟩,
    ⟨hshort.1,mono hshort.2 hinc⟩,hs⟩

def profile (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (K : ℕ) (outer : Fin K → Bool) :
    PlayerSpecificAlgebraicSegment.Descriptor 3 9 :=
  let f:=family model root a short
  let s:=PlayerSpecificAlgebraicNestedFirstDraw.location model root f K outer
  PlayerSpecificAlgebraicNestedFirstTable.prepare model root f s

theorem profile_bounds (model : RationalCostModel) (root : Candidate) (a : Input) (short : Data) (T : ℕ)
    (hfit : Fits root a T) (hshort : Reduced root.polynomial short ∧ HasHeight short T)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmT : HasHeight root.polynomial T) (hT : 2≤T) (K : ℕ) (outer : Fin K → Bool) :
    PlayerSpecificAlgebraicDescriptorBounds.Bounds root (profile model root a short K outer)
      (iterate 32 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base (iterate 9 T) K)) := by
  have hf:=fits model root a short T hfit hshort hm hm0 hml hmT hT
  have hinc:=PlayerSpecificAlgebraicExpressionBudget.initial_le 9 T
  exact PlayerSpecificAlgebraicNestedFirstDrawSizes.table_bounds model root (family model root a short) (iterate 9 T)
    hf hm hm0 hml (mono hmT hinc) (hT.trans hinc) K outer

end Blotto.PlayerSpecificAlgebraicNestedFamily
