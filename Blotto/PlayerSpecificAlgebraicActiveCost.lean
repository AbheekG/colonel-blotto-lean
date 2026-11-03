import Blotto.PlayerSpecificAlgebraicComparisonExecution

/-! Both possible short-circuit active-test paths have a uniform bound
derived from the actual retained-root comparison callers. -/
namespace Blotto.PlayerSpecificAlgebraicActiveCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicCandidates PlayerSpecificAlgebraicComparisonExecution
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem control_cost (model : RationalCostModel) (W : ℕ) (hW : 1≤W) :
    price model [.control 1]≤3*model.rat W := by
  have hr:=hW.trans (model.word_le W)
  have he : price model [.control 1]=2 := by rfl
  rw [he]
  omega

theorem profile (A R H : ℕ) :
    A*(H+1)*R+A*(H+1)*R+3*R≤(2*A+3)*(H+1)*R := by
  nlinarith only [Nat.zero_le (H*R)]

theorem cost (model : RationalCostModel) (root : Candidate) (length resource : Data) (H : ℕ)
    (hm : Normalized root.polynomial) (hm0 : root.polynomial≠[]) (hml : root.polynomial.length≤4)
    (hmH : HasHeight root.polynomial H) (he : HasHeight [root.interval.lo,root.interval.hi] H)
    (hv : root.interval.lo<root.interval.hi) (hl : HasHeight length H) (hr : HasHeight resource H)
    (hll : length.length≤3) (hrl : resource.length≤3) (hH : 1≤H) :
    (active model root length resource).2≤(2*PlayerSpecificAlgebraicComparisonExecution.coefficient+3)*(H+1)*model.rat (width H) := by
  have hfirst:=PlayerSpecificAlgebraicComparisonExecution.cost model root resource [] H hm hm0 hml hmH he hv
    hr (nil_height _) hrl (by simp) hH
  have hsecond:=PlayerSpecificAlgebraicComparisonExecution.cost model root length resource H hm hm0 hml hmH he hv
    hl hr hll hrl hH
  have hW : 1≤width H := (by have h:=PlayerSpecificAlgebraicInitialPrimitiveCost.large (2*H+1); change 1≤PlayerSpecificAlgebraicInitialPrimitiveCost.width (2*H+1); omega)
  have hctrl:=control_cost model (width H) hW
  apply le_trans ?_ (profile PlayerSpecificAlgebraicComparisonExecution.coefficient (model.rat (width H)) H)
  dsimp only [active]
  split
  · omega
  · exact Nat.add_le_add (Nat.add_le_add hfirst hsecond) hctrl

end Blotto.PlayerSpecificAlgebraicActiveCost
