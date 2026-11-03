import Blotto.PlayerSpecificCellPolynomialHeights

/-! Actual interior and breakpoint root representations have linear
polynomial/endpoint heights in the encoded rational cell data. -/
namespace Blotto.PlayerSpecificCellCandidateHeights
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates
set_option autoImplicit false
set_option maxHeartbeats 2500000

def coefficient : ℕ := 22*PlayerSpecificCandidateBudget.heightCoefficient+100
def height (H : ℕ) : ℕ := coefficient*(H+1)

theorem large (H : ℕ) : H+2≤height H := by
  have hm:=Nat.mul_le_mul_right (H+1) (show 100≤coefficient by unfold coefficient; omega)
  unfold height
  omega

theorem generated (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hp : semantics (cubic c.state.coefficients b)≠0)
    (candidate : Candidate) (hmem : candidate∈PlayerSpecificFiniteCellSearch.roots model c b) :
    HasHeight candidate.polynomial (height H) ∧ RationalHeight candidate.interval.lo (height H) ∧ RationalHeight candidate.interval.hi (height H) := by
  have he:=PlayerSpecificCellPolynomialHeights.cubic_encoding c b H hc hb
  have hs:=PlayerSpecificCandidateContract.sizes model _ hp (by rfl) candidate hmem
  have hmul:=Nat.mul_le_mul_left PlayerSpecificCandidateBudget.heightCoefficient
    (show PlayerSpecificRationalMagnitude.inputHeight (cubic c.state.coefficients b)+1≤22*(H+1) by omega)
  have hcap : PlayerSpecificCandidateBudget.height (cubic c.state.coefficients b)≤height H := by
    unfold PlayerSpecificCandidateBudget.height height coefficient
    nlinarith only [hmul]
  exact ⟨mono hs.1 hcap,hs.2.1.mono hcap,hs.2.2.mono hcap⟩

theorem breakpoint (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H) (hH : 1≤H)
    (candidate : Candidate) (hresult : PlayerSpecificRationalBreakpoint.run c b=some candidate) :
    HasHeight candidate.polynomial (height H) ∧ RationalHeight candidate.interval.lo (height H) ∧ RationalHeight candidate.interval.hi (height H) := by
  have hlarge:=large H
  cases hu : c.upper with
  | none => simp only [PlayerSpecificRationalBreakpoint.run,hu] at hresult; cases hresult
  | some q =>
    have hq : RationalHeight q H := hc.2.2.1 q (by rw [hu]; exact Option.mem_some_self _)
    by_cases ht : 0<q ∧ c.lower≤q ∧ evaluate (cubic c.state.coefficients b) q=0 ∧ PlayerSpecificRationalBreakpoint.passes c b q
    · simp only [PlayerSpecificRationalBreakpoint.run,hu,ht] at hresult
      have he:=Option.some.inj hresult
      subst candidate
      have hp:=PlayerSpecificFactorHeights.linear_height q H hq hH
      have hlo : RationalHeight (q-1) (H+2) := by simpa only [Nat.add_assoc] using hq.sub one_height
      exact ⟨mono hp (by omega),hlo.mono hlarge,hq.mono (by omega)⟩
    · simp only [PlayerSpecificRationalBreakpoint.run,hu,ht] at hresult
      cases hresult

theorem accepted (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) (hp : semantics (cubic c.state.coefficients b)≠0)
    (candidate : Candidate) (hr : PlayerSpecificFiniteCellSearch.run model c b=some candidate) :
    HasHeight candidate.polynomial (height H) ∧ RationalHeight candidate.interval.lo (height H) ∧ RationalHeight candidate.interval.hi (height H) := by
  cases hi : PlayerSpecificFiniteCellSearch.interior model c b with
  | none =>
    rw [PlayerSpecificFiniteCellSearch.run,hi] at hr
    exact breakpoint c b H hc hH candidate hr
  | some r =>
    rw [PlayerSpecificFiniteCellSearch.run,hi] at hr
    have he:=Option.some.inj hr
    subst r
    exact generated model c b H hc hb hp candidate (List.mem_of_find?_eq_some hi)

end Blotto.PlayerSpecificCellCandidateHeights
