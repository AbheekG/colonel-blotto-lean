import Blotto.PlayerSpecificFiniteScaleBudget

/-! The scale caller includes every cell, budget, defining-polynomial,
seed, numerator and reduced-output record at proved original-cell heights. -/
namespace Blotto.PlayerSpecificFiniteScaleCopyCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificPolynomialNormalization PlayerSpecificRationalTrace
open PlayerSpecificFiniteScaleBudget
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem frame_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (m : Data) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hm : Normalized m) (hm0 : m≠[])
    (hml : m.length≤4) (hmH : HasHeight m (PlayerSpecificCellCandidateHeights.height H)) :
    price model (PlayerSpecificFiniteScaleExecution.frame c b m [1/(2*b)]
      [c.state.coefficients.B2,0,c.state.coefficients.B1]
      (PlayerSpecificModularExecution.run model m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]).1)≤
      500*model.rat (width H) := by
  have hw:=wide H
  have hl:=large H
  have hcell:=PlayerSpecificCellTestCopyCost.cell_cost model c H hc
  have hcellp:=hcell.trans (Nat.mul_le_mul_left 135 (model.monotone hw.2.1))
  have row_cost (p : Data) (hp : HasHeight p (height H)) (hpLen : p.length≤21) :
      price model (copyRow p)≤66*model.rat (width H) :=
    PlayerSpecificExtendedCopyCost.row_cost model p (height H) (width H) hp hpLen hw.1 hw.2.2
  have hbudget:=row_cost [b] (cons_height (hb.mono (by omega)) (nil_height _)) (by simp)
  have hmodulus:=row_cost m (mono hmH hl.1) (by omega)
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hinv : RationalHeight (1/(2*b)) (H+2) := by simpa only [one_div,Nat.add_comm] using (h2.mul hb).inv
  have hseed:=row_cost [1/(2*b)] (cons_height (hinv.mono hl.2) (nil_height _)) (by simp)
  have hnum:=row_cost [c.state.coefficients.B2,0,c.state.coefficients.B1]
    (cons_height (hc.1.2.2.2.1.mono (by omega))
      (cons_height (zero_height.mono (by omega)) (cons_height (hc.1.2.2.1.mono (by omega)) (nil_height _)))) (by simp)
  have hout : HasHeight (PlayerSpecificModularExecution.run model m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]).1 (height H) := by
    rw [PlayerSpecificModularExecution.value]
    exact PlayerSpecificFiniteScaleHeights.scale_height c b m H hc hb hm hm0 hml hmH
  have houtLen : (PlayerSpecificModularExecution.run model m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1]).1.length≤3 := by
    rw [PlayerSpecificModularExecution.value]
    have hr:=PlayerSpecificModularHorner.reduced m [1/(2*b)] [c.state.coefficients.B2,0,c.state.coefficients.B1] hm hm0
    have hlt:=hr.2
    omega
  have houtput:=row_cost _ hout (by omega)
  have hcontrol:=event_price model (width H) (by omega) (.control 3)
    ((PlayerSpecificRationalTrace.control_width 3).trans (by omega))
  change price model [.control 3]≤3*model.rat (width H) at hcontrol
  simp only [PlayerSpecificFiniteScaleExecution.frame,price_append]
  nlinarith only [hcellp,hbudget,hmodulus,hseed,hnum,houtput,hcontrol]

end Blotto.PlayerSpecificFiniteScaleCopyCost
