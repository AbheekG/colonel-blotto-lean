import Blotto.PlayerSpecificCandidateTestCost

/-! Same-return exact acceptance and complete polynomial source cost for
the actual generated irreducible candidates. All height premises come from
the rational cell/input and the executed candidate constructor. -/
namespace Blotto.PlayerSpecificCandidateTestContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def scaleCoefficient : ℕ := PlayerSpecificCellCandidateHeights.coefficient+10
def widthCoefficient : ℕ := PlayerSpecificCandidateTestBudget.widthCoefficient*scaleCoefficient
def workCoefficient : ℕ := PlayerSpecificCandidateTestBudget.workCoefficient*scaleCoefficient
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem size_profile (C H : ℕ) : C*(H+1)+4*H+6≤(C+10)*(H+1) := by nlinarith

theorem source_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H)
    (hp : semantics (cubic c.state.coefficients b)≠0) (candidate : Candidate)
    (hmem : candidate∈PlayerSpecificFiniteCellSearch.roots model c b) :
    (PlayerSpecificCandidateTestExecution.run model c candidate).2≤
      workCoefficient*(H+1)*model.rat (widthCoefficient*(H+1)) := by
  have hf:=PlayerSpecificCandidateFieldInput.field_input model _ hp (by rfl) candidate hmem
  have hs:=PlayerSpecificCellCandidateHeights.generated model c b H hc hb hp candidate hmem
  have hm0 : candidate.polynomial≠[] := by intro hz; exact hf.2.1.ne_zero (by rw [hz]; rfl)
  obtain ⟨x,hx,_⟩:=hf.2.2.2.2
  have hv : candidate.interval.lo<candidate.interval.hi := by exact_mod_cast hx.2.1.trans_le hx.2.2
  have he:=cons_height hs.2.1 (cons_height hs.2.2 (nil_height _))
  have hcost:=PlayerSpecificCandidateTestCost.run_cost model c candidate H (PlayerSpecificCellCandidateHeights.height H)
    hc hH hs.1 he hf.1 hm0 hf.2.2.1 hv
  have hsize : PlayerSpecificCandidateTestBudget.size H (PlayerSpecificCellCandidateHeights.height H)≤scaleCoefficient*(H+1) :=
    size_profile PlayerSpecificCellCandidateHeights.coefficient H
  have hwork:=Nat.mul_le_mul_left PlayerSpecificCandidateTestBudget.workCoefficient hsize
  have hwidth:=Nat.mul_le_mul_left PlayerSpecificCandidateTestBudget.widthCoefficient hsize
  have hwp : PlayerSpecificCandidateTestBudget.workCoefficient*
      PlayerSpecificCandidateTestBudget.size H (PlayerSpecificCellCandidateHeights.height H)≤workCoefficient*(H+1) := by
    exact hwork.trans_eq (by unfold workCoefficient; ring)
  have hwidthp : PlayerSpecificCandidateTestBudget.width H (PlayerSpecificCellCandidateHeights.height H)≤widthCoefficient*(H+1) := by
    exact hwidth.trans_eq (by unfold widthCoefficient; ring)
  exact hcost.trans (Nat.mul_le_mul hwp (model.monotone hwidthp))

theorem actual_contract (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) (hb0 : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) (candidate : Candidate)
    (hmem : candidate∈PlayerSpecificFiniteCellSearch.roots model c b) (x : ℝ)
    (hx : realEvaluate candidate.polynomial x=0 ∧ candidate.interval.Contains x) :
    let result:=PlayerSpecificCandidateTestExecution.run model c candidate
    (result.1=true ↔ PlayerSpecificCellCandidates.Interior (castCell c) x ∧
      PlayerSpecificCellCandidates.Passes (castCell c) (b:ℝ) x) ∧
      result.2≤workCoefficient*(H+1)*model.rat (widthCoefficient*(H+1)) := by
  refine ⟨?_,source_cost model c b H hc hb hH hp candidate hmem⟩
  rw [PlayerSpecificCandidateTestExecution.value]
  exact PlayerSpecificAlgebraicCandidateTest.correct model _ hp (by rfl) candidate hmem c b hb0 x hx

theorem polynomial_cost (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H)
    (hb : RationalHeight b H) (hH : 1≤H) (hp : semantics (cubic c.state.coefficients b)≠0)
    (candidate : Candidate) (hmem : candidate∈PlayerSpecificFiniteCellSearch.roots RationalCostModel.schoolbook c b) :
    (PlayerSpecificCandidateTestExecution.run RationalCostModel.schoolbook c candidate).2≤polynomialCoefficient*(H+1)^3 := by
  have hc:=source_cost RationalCostModel.schoolbook c b H hc hb hH hp candidate hmem
  change (PlayerSpecificCandidateTestExecution.run RationalCostModel.schoolbook c candidate).2≤
    workCoefficient*(H+1)*((widthCoefficient*(H+1))*(widthCoefficient*(H+1))+widthCoefficient*(H+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificCandidateTestContract
