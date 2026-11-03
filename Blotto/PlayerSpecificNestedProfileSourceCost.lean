import Blotto.PlayerSpecificNestedProfileExecution

/-! The actual conditional profile has a complete source polynomial
in original row height and midpoint precision, with all reached sizes
derived from the actual family and location. -/
namespace Blotto.PlayerSpecificNestedProfileSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicNestedInput PlayerSpecificAlgebraicNestedParameterSizes PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false
set_option maxHeartbeats 2500000

def locationHeight (H K : ℕ) : ℕ := iterate 10 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base (iterate 9 H) K)
def work (H K : ℕ) : ℕ := PlayerSpecificNestedFamilySourceCost.work H+
  PlayerSpecificNestedLocationSourceCost.work (iterate 9 H) K+
  PlayerSpecificNestedFirstTableSourceCost.work (locationHeight H K)+2

theorem cost (root : Candidate) (a : Input) (short : Data) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hShort : Reduced root.polynomial short ∧ HasHeight short H) :
    (PlayerSpecificNestedProfileExecution.run RationalCostModel.schoolbook root a short K outer).2≤work H K := by
  let model:=RationalCostModel.schoolbook
  let family:=PlayerSpecificAlgebraicNestedFamily.family model root a short
  let location:=PlayerSpecificAlgebraicNestedFirstDraw.location model root family K outer
  let T:=iterate 9 H
  let U:=locationHeight H K
  have hHT : H≤T := PlayerSpecificAlgebraicExpressionBudget.initial_le 9 H
  have hTU : T≤U := by
    have h:=PlayerSpecificAlgebraicExpressionBudget.initial_le 10 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base T K)
    dsimp [PlayerSpecificAlgebraicNestedFirstDrawSizes.base] at h
    change T ≤ iterate 10 (PlayerSpecificAlgebraicNestedFirstDrawSizes.base T K)
    dsimp [PlayerSpecificAlgebraicNestedFirstDrawSizes.base]
    omega
  have hHU:=hHT.trans hTU
  have hfamily:=PlayerSpecificAlgebraicNestedFamily.fits model root a short H ha hShort hm hm0 hml hmH hH
  have hlocation:=PlayerSpecificAlgebraicNestedFirstDrawSizes.location_bounds model root family T hfamily hm hm0 hml
    (mono hmH hHT) (hH.trans hHT) K outer
  have hf:=PlayerSpecificNestedFamilySourceCost.cost root a short H hm hm0 hml hmH he hv hH ha hShort
  have hl:=PlayerSpecificNestedLocationSourceCost.cost root family T K outer hm hm0 hml (mono hmH hHT) (mono he hHT) hv
    (hH.trans hHT) hfamily
  have ht:=PlayerSpecificNestedFirstTableSourceCost.cost root family location U hm hm0 hml (mono hmH hHU) (mono he hHU) hv
    (hH.trans hHU) (PlayerSpecificAlgebraicNestedInputTools.fits_mono root family T U hfamily hTU) hlocation
  rw [PlayerSpecificNestedProfileExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hf hl) ht) 2

theorem same_return_and_cost (root : Candidate) (a : Input) (short : Data) (H K : ℕ) (outer : Fin K → Bool)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hShort : Reduced root.polynomial short ∧ HasHeight short H) :
    (PlayerSpecificNestedProfileExecution.run RationalCostModel.schoolbook root a short K outer).1=
      PlayerSpecificAlgebraicNestedFamily.profile RationalCostModel.schoolbook root a short K outer ∧
    (PlayerSpecificNestedProfileExecution.run RationalCostModel.schoolbook root a short K outer).2≤work H K :=
  ⟨PlayerSpecificNestedProfileExecution.value _ root a short K outer,cost root a short H K outer hm hm0 hml hmH he hv hH ha hShort⟩

end Blotto.PlayerSpecificNestedProfileSourceCost
