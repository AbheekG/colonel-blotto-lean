import Blotto.PlayerSpecificFiniteScaleCopyCost

/-! Actual reduced-scale computation has exact value, linear output size
and complete original-cell source time including its two budget operations.
Its schoolbook bound is explicitly quadratic. -/
namespace Blotto.PlayerSpecificFiniteScaleContract
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificPolynomialNormalization PlayerSpecificRationalTrace
open PlayerSpecificFiniteScaleBudget
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem source_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (m : Data) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hmH : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    (PlayerSpecificFiniteScaleExecution.run model c b m).2≤1000000000*model.rat (width H) := by
  have hi:=input_heights c b m H hc hb hmH
  have hl:=large H
  have hw:=wide H
  have hmod:=PlayerSpecificModularExecutionCost.run_cost model m [1/(2*b)]
    [c.state.coefficients.B2,0,c.state.coefficients.B1] hm hm0 hml (by simp) (by simp)
    (inputHeight H) hi.1 hi.2.1 hi.2.2
  have hmodp:=hmod.trans (Nat.mul_le_mul_left 800000000 (model.monotone (modular_width H)))
  have hframe:=PlayerSpecificFiniteScaleCopyCost.frame_cost model c b m H hc hb hm hm0 hml hmH
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hd : RationalHeight (2*b) (H+2) := by simpa only [Nat.add_comm] using h2.mul hb
  have scalar_bound (op : Arithmetic) (a d : ℚ) (ha : RationalHeight a (H+2)) (hd : RationalHeight d (H+2)) :
      price model (scalar op a d).2≤15*model.rat (width H) := by
    have hf:=fits_mono (scalar_fits_height op a d (H+2) ha hd)
      (show 4*(H+2)+3≤width H by have hh:=hw.2.1; omega)
    have hp:=price_bound model (width H) (by omega) _ hf
    rwa [scalar_length] at hp
  have hden:=scalar_bound .multiply 2 b (h2.mono (by omega)) (hb.mono (by omega))
  have hrec:=scalar_bound .divide 1 (2*b) (one_height.mono (by omega)) hd
  simp only [PlayerSpecificFiniteScaleExecution.run,scalar_value,Arithmetic.apply]
  nlinarith only [hmodp,hframe,hden,hrec]

theorem actual_contract (model : RationalCostModel) (c : Cell) (b : ℚ) (m : Data) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hmH : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    let result:=PlayerSpecificFiniteScaleExecution.run model c b m
    result.1=PlayerSpecificFiniteParameterReturn.scale c b m ∧
      PlayerSpecificAlgebraicReduction.Reduced m result.1 ∧ result.1.length≤3 ∧ HasHeight result.1 (height H) ∧
      result.2≤1000000000*model.rat (width H) := by
  have hv:=PlayerSpecificFiniteScaleExecution.value model c b m
  have hr:=PlayerSpecificModularHorner.reduced m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1] hm hm0
  refine ⟨hv,?_,?_,?_,source_cost model c b m H hc hb hm hm0 hml hmH⟩
  · rw [hv]; exact hr
  · rw [hv]
    change (PlayerSpecificModularHorner.run m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]).length≤3
    have hlt:=hr.2
    omega
  · rw [hv]; exact PlayerSpecificFiniteScaleHeights.scale_height c b m H hc hb hm hm0 hml hmH

theorem polynomial_cost (c : Cell) (b : ℚ) (m : Data) (H : ℕ) (hc : CellHeight c H) (hb : RationalHeight b H)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hmH : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    (PlayerSpecificFiniteScaleExecution.run RationalCostModel.schoolbook c b m).2≤
      (1000000000*(widthCoefficient*widthCoefficient+widthCoefficient))*(H+1)^2 := by
  have hc:=source_cost RationalCostModel.schoolbook c b m H hc hb hm hm0 hml hmH
  change (PlayerSpecificFiniteScaleExecution.run RationalCostModel.schoolbook c b m).2≤
    1000000000*((widthCoefficient*(H+1))*(widthCoefficient*(H+1))+widthCoefficient*(H+1)) at hc
  exact hc.trans (PlayerSpecificAlgebraicInverseContract.quadratic_profile _ _ _ (by omega))

end Blotto.PlayerSpecificFiniteScaleContract
