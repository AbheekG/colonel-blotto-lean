import Blotto.PlayerSpecificOverlapEntryExecution

/-! Complete overlap entry source work uses only original parent
bounds, dimensions and scalar rows; all local temporaries are derived. -/
namespace Blotto.PlayerSpecificOverlapEntrySourceCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificAlgebraicReduction PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates
open PlayerSpecificAlgebraicSegment PlayerSpecificAlgebraicDescriptorBounds
set_option autoImplicit false
set_option maxHeartbeats 2500000

def work (H k h : ℕ) : ℕ := PlayerSpecificOverlapIndexSourceCost.work k h+
  PlayerSpecificOverlapEnvironmentSourceCost.work H k h+PlayerSpecificCachedOverlapRowSourceCost.work H+2

theorem cost {k h : ℕ} (root : Candidate) (first : Descriptor 3 k) (second : Descriptor 3 h)
    (interval budget : Data) (slot : Fin (k*h)) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hH : 2≤H) (hf : Bounds root first H) (hs : Bounds root second H)
    (hi : Reduced root.polynomial interval ∧ HasHeight interval H) (hb : Reduced root.polynomial budget ∧ HasHeight budget H) :
    (PlayerSpecificOverlapEntryExecution.run RationalCostModel.schoolbook root first second interval budget slot).2≤work H k h := by
  let pair:=finProdFinEquiv.symm slot
  have hp:=PlayerSpecificOverlapIndexSourceCost.cost k h slot
  have hec:=PlayerSpecificOverlapEnvironmentSourceCost.cost root first second interval budget pair.1 pair.2 H hml hmH he hf hs hi hb
  have henv:=PlayerSpecificAlgebraicOverlapEnvironment.bounds root first second interval budget H hf hs hi hb pair.1 pair.2
  have hr:=PlayerSpecificCachedOverlapRowSourceCost.cost root (PlayerSpecificAlgebraicOverlapEnvironment.environment first second interval budget pair.1 pair.2)
    H hm hm0 hml hmH he hv hH henv
  rw [PlayerSpecificOverlapEntryExecution.price_equation]
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hec) hr) 2

end Blotto.PlayerSpecificOverlapEntrySourceCost
