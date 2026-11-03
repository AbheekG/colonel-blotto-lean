import Blotto.PlayerSpecificCandidateScanCost

/-! The scan over the actual cubic-root list returns exactly the preserved
first passing interior candidate, with complete original-cell source time.
Root generation and the separate breakpoint caller are priced separately. -/
namespace Blotto.PlayerSpecificCandidateScanContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

def widthCoefficient : ℕ := PlayerSpecificCandidateTestContract.widthCoefficient
def workCoefficient : ℕ := 4*(PlayerSpecificCandidateTestContract.workCoefficient+500)
def polynomialCoefficient : ℕ := workCoefficient*(widthCoefficient*widthCoefficient+widthCoefficient)

theorem total_profile (C H N R : ℕ) (hN : N≤3) :
    (C*(H+1)+500)*(N+1)*R≤(4*(C+500))*(H+1)*R := by
  have hn:=Nat.mul_le_mul_left (C*(H+1)+500) (show N+1≤4 by omega)
  have hm:=Nat.mul_le_mul_right R hn
  nlinarith only [hm]

theorem source_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H)
    (hp : semantics (cubic c.state.coefficients b)≠0) :
    (PlayerSpecificCandidateScanExecution.run model c (PlayerSpecificFiniteCellSearch.roots model c b)).2≤
      workCoefficient*(H+1)*model.rat (widthCoefficient*(H+1)) := by
  have hlen : (PlayerSpecificFiniteCellSearch.roots model c b).length≤3 :=
    (PlayerSpecificCandidateContract.actual_contract model _ hp (by rfl)).1
  have hw:=PlayerSpecificCandidateRecordCost.wide H
  have hcst:=PlayerSpecificCandidateScanCost.run_cost model c (PlayerSpecificFiniteCellSearch.roots model c b) H
    (widthCoefficient*(H+1)) PlayerSpecificCandidateTestContract.workCoefficient hc (by exact le_trans (Nat.le_add_left _ _) hw)
    hlen (PlayerSpecificCandidateRecordCost.copy_cost model c b H hc hb hp)
    (PlayerSpecificCandidateTestContract.source_cost model c b H hc hb hH hp)
  exact hcst.trans (total_profile _ H _ _ hlen)

theorem actual_contract (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H)
    (hp : semantics (cubic c.state.coefficients b)≠0) :
    let result:=PlayerSpecificCandidateScanExecution.run model c (PlayerSpecificFiniteCellSearch.roots model c b)
    result.1=PlayerSpecificFiniteCellSearch.interior model c b ∧
      result.2≤workCoefficient*(H+1)*model.rat (widthCoefficient*(H+1)) :=
  ⟨PlayerSpecificCandidateScanExecution.value model c _,source_cost model c b H hc hb hH hp⟩

theorem polynomial_cost (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H)
    (hb : RationalHeight b H) (hH : 1≤H) (hp : semantics (cubic c.state.coefficients b)≠0) :
    (PlayerSpecificCandidateScanExecution.run RationalCostModel.schoolbook c
      (PlayerSpecificFiniteCellSearch.roots RationalCostModel.schoolbook c b)).2≤polynomialCoefficient*(H+1)^3 := by
  have hc:=source_cost RationalCostModel.schoolbook c b H hc hb hH hp
  change (PlayerSpecificCandidateScanExecution.run RationalCostModel.schoolbook c
    (PlayerSpecificFiniteCellSearch.roots RationalCostModel.schoolbook c b)).2≤workCoefficient*(H+1)*
      ((widthCoefficient*(H+1))*(widthCoefficient*(H+1))+widthCoefficient*(H+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificCandidateScanContract
