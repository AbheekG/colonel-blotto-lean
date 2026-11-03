import Blotto.PlayerSpecificNestedFirstTableExecution

/-! Complete all-branch conditional table source work. Its explicit
polynomial bound uses only original raw height; execution selects one
continuation and supplies no coefficient-size or arithmetic oracle. -/
namespace Blotto.PlayerSpecificNestedFirstTableSourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicNestedInput
open PlayerSpecificAlgebraicNestedParameterSizes
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H : ℕ) : ℕ := PlayerSpecificNestedPositiveSourceCost.work H+
  PlayerSpecificNestedGeometrySourceCost.work H+PlayerSpecificNestedZeroSourceCost.work H+2
theorem positive_profile (U V W : ℕ) : U+V+2≤U+V+W+2 := by omega
theorem zero_profile (U V W : ℕ) : U+W+2≤U+V+W+2 := by omega

theorem cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedFirstTableExecution.run RationalCostModel.schoolbook root a extra).2≤work H := by
  have ht:=PlayerSpecificNestedPositiveSourceCost.cost root a extra H hm hm0 hml hmH he hv hH ha hExtra
  have hg:=PlayerSpecificNestedGeometrySourceCost.cost root a extra H hm hm0 hml hmH he hv hH ha hExtra
  have hz:=PlayerSpecificNestedZeroSourceCost.cost root a extra H hm hm0 hml hmH he hv hH ha hExtra
  simp only [PlayerSpecificNestedFirstTableExecution.run,PlayerSpecificNestedFirstTableExecution.packing]
  split
  · exact (Nat.add_le_add_right (Nat.add_le_add ht hg) 2).trans (positive_profile _ _ _)
  · exact (Nat.add_le_add_right (Nat.add_le_add ht hz) 2).trans (zero_profile _ _ _)

theorem same_return_and_cost (root : Candidate) (a : Input) (extra : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (ha : Fits root a H)
    (hExtra : Reduced root.polynomial extra ∧ HasHeight extra H) :
    (PlayerSpecificNestedFirstTableExecution.run RationalCostModel.schoolbook root a extra).1=
      PlayerSpecificAlgebraicNestedFirstTable.prepare RationalCostModel.schoolbook root a extra ∧
    (PlayerSpecificNestedFirstTableExecution.run RationalCostModel.schoolbook root a extra).2≤work H :=
  ⟨PlayerSpecificNestedFirstTableExecution.value _ root a extra,cost root a extra H hm hm0 hml hmH he hv hH ha hExtra⟩

end Blotto.PlayerSpecificNestedFirstTableSourceCost
