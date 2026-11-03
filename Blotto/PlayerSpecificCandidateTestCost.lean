import Blotto.PlayerSpecificCandidateTestSignCost

/-! The full executed interior test is bounded by a linear number of
rational primitive majorants at a linear encoded cell/root width. -/
namespace Blotto.PlayerSpecificCandidateTestCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificPolynomialNormalization
open PlayerSpecificRationalCells PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates
open PlayerSpecificRationalTrace PlayerSpecificCandidateTestExecution PlayerSpecificCandidateTestBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem total_profile (C S R construction a b upper d e frame : ℕ) (hS : 1≤S)
    (hc : construction≤1000*R) (ha : a≤C*S*R) (hb : b≤C*S*R)
    (hu : upper≤C*S*R+6*R) (hd : d≤C*S*R) (he : e≤C*S*R) (hf : frame≤153*R) :
    construction+a+b+upper+d+e+frame≤(5*C+2000)*S*R := by
  have hm:=Nat.mul_le_mul_right (2000*R) hS
  nlinarith only [hc,ha,hb,hu,hd,he,hf,hm]

theorem run_cost (model : RationalCostModel) (c : Cell) (candidate : Candidate) (H T : ℕ)
    (hc : CellHeight c H) (hH : 1≤H) (hm : HasHeight candidate.polynomial T)
    (he : HasHeight [candidate.interval.lo,candidate.interval.hi] T)
    (hn : Normalized candidate.polynomial) (hm0 : candidate.polynomial≠[]) (hml : candidate.polynomial.length≤4)
    (hv : candidate.interval.lo<candidate.interval.hi) :
    (run model c candidate).2≤workCoefficient*size H T*model.rat (width H T) := by
  have ht:=tests_bounds c H hc hH
  have ha:=PlayerSpecificCandidateTestSignCost.sign_cost model candidate _ H T hm he hn hm0 hml ht.1 hv
  have hb:=PlayerSpecificCandidateTestSignCost.sign_cost model candidate _ H T hm he hn hm0 hml ht.2.1 hv
  have hu:=PlayerSpecificCandidateTestSignCost.upper_cost model candidate _ H T hm he hn hm0 hml ht.2.2.1 hv
  have hd:=PlayerSpecificCandidateTestSignCost.sign_cost model candidate _ H T hm he hn hm0 hml ht.2.2.2.1 hv
  have hec:=PlayerSpecificCandidateTestSignCost.sign_cost model candidate _ H T hm he hn hm0 hml ht.2.2.2.2 hv
  have hconstruction:=PlayerSpecificCellTestConstructionCost.run_cost model c H hc hH
  have hconstructionp:=hconstruction.trans
    (Nat.mul_le_mul_left 1000 (model.monotone (width_large H T).1))
  rw [PlayerSpecificCandidateTestExecution.run]
  dsimp only
  exact total_profile signWorkCoefficient (size H T) (model.rat (width H T)) _ _ _ _ _ _ _
    (by unfold size; omega) hconstructionp ha hb hu hd hec
    (PlayerSpecificCandidateTestCopyCost.frame_cost model candidate H T hm hml he _ _ _ _ _ _)

end Blotto.PlayerSpecificCandidateTestCost
