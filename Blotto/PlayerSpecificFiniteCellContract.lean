import Blotto.PlayerSpecificFiniteCellCost

/-! Same-return finite-bit cell acceptance/rejection with complete source
time derived from its rational data, plus an explicit cubic schoolbook
bound. No arithmetic, root-selection or price oracle is supplied. -/
namespace Blotto.PlayerSpecificFiniteCellContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificAlgebraicCandidates PlayerSpecificFiniteCellBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem actual_contract (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) (hb0 : b≠0)
    (hp : semantics (cubic c.state.coefficients b)≠0) :
    let result:=PlayerSpecificFiniteCellExecution.run model c b
    result.1=PlayerSpecificFiniteCellSearch.run model c b ∧
      (∀ r,result.1=some r → PlayerSpecificFiniteCellSearch.Good c b r) ∧
      result.2≤workCoefficient*(H+1)*model.rat (width H) := by
  have hv:=PlayerSpecificFiniteCellExecution.value model c b hb0
  refine ⟨hv,?_,PlayerSpecificFiniteCellCost.source_cost model c b H hc hb hH hp⟩
  intro r hr
  exact PlayerSpecificFiniteCellSearch.sound model c b hb0 hp r (hv.symm.trans hr)

theorem polynomial_cost (c : Cell) (b : ℚ) (H : ℕ) (hc : CellHeight c H)
    (hb : RationalHeight b H) (hH : 1≤H) (hp : semantics (cubic c.state.coefficients b)≠0) :
    (PlayerSpecificFiniteCellExecution.run RationalCostModel.schoolbook c b).2≤polynomialCoefficient*(H+1)^3 := by
  have hc:=PlayerSpecificFiniteCellCost.source_cost RationalCostModel.schoolbook c b H hc hb hH hp
  change (PlayerSpecificFiniteCellExecution.run RationalCostModel.schoolbook c b).2≤workCoefficient*(H+1)*
    ((widthCoefficient*(H+1))*(widthCoefficient*(H+1))+widthCoefficient*(H+1)) at hc
  exact hc.trans (PlayerSpecificRootContract.schoolbook_profile _ _ _ (by omega))

end Blotto.PlayerSpecificFiniteCellContract
