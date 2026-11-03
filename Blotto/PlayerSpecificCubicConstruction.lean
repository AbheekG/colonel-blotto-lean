import Blotto.PlayerSpecificCandidateScanContract

/-! Actual construction of the four cubic coefficients, including the
signed budget products and complete rational-cell/input/return copies. -/
namespace Blotto.PlayerSpecificCubicConstruction
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2000000

def run (c : Cell) (b : ℚ) : Data×Trace :=
  let negated:=scalar .multiply (-1) b
  let first:=scalar .multiply negated.1 c.state.coefficients.A2
  let third:=scalar .multiply negated.1 c.state.coefficients.A1
  let result:=[first.1,c.state.coefficients.B2,third.1,c.state.coefficients.B1]
  (result,PlayerSpecificCellTestConstruction.copyCell c++copyRow [b]++negated.2++first.2++third.2++copyRow result++[.control 4])

theorem value (c : Cell) (b : ℚ) : (run c b).1=cubic c.state.coefficients b := by
  simp only [run,scalar,Arithmetic.apply,neg_one_mul,cubic]

theorem run_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hH : 1≤H) :
    price model (run c b).2≤1000*model.rat (128*(H+1)) := by
  have scalar_bound (op : Arithmetic) (a d : ℚ) (ha : RationalHeight a (H+1)) (hd : RationalHeight d (H+1)) :
      price model (scalar op a d).2≤15*model.rat (128*(H+1)) := by
    have hf:=fits_mono (scalar_fits_height op a d (H+1) ha hd) (show 4*(H+1)+3≤128*(H+1) by omega)
    have hp:=price_bound model (128*(H+1)) (by omega) _ hf
    rwa [scalar_length] at hp
  have hn : RationalHeight (scalar .multiply (-1) b).1 H := by simpa only [scalar,Arithmetic.apply,neg_one_mul] using hb.neg
  have hneg:=scalar_bound .multiply (-1) b (one_height.neg.mono (by omega)) (hb.mono (by omega))
  have hfirst:=scalar_bound .multiply _ c.state.coefficients.A2 (hn.mono (by omega)) (hc.1.2.1.mono (by omega))
  have hthird:=scalar_bound .multiply _ c.state.coefficients.A1 (hn.mono (by omega)) (hc.1.1.mono (by omega))
  have hcell:=PlayerSpecificCellTestCopyCost.cell_cost model c H hc
  have hbudget:=PlayerSpecificExtendedCopyCost.row_cost model [b] H (128*(H+1))
    (cons_height hb (nil_height _)) (by simp) (by omega) (by omega)
  have hr : HasHeight (run c b).1 (2*H) := by rw [value]; exact PlayerSpecificCellPolynomialHeights.cubic_height c b H hc hb
  have hresult:=PlayerSpecificExtendedCopyCost.row_cost model (run c b).1 (2*H) (128*(H+1)) hr
    (by rw [value]; simp [cubic]) (by omega) (by omega)
  have hcontrol:=PlayerSpecificCellTestCopyCost.control model H 4 (by decide)
  unfold PlayerSpecificCellTestCopyCost.width at hcell hcontrol
  rw [run]
  dsimp only [run] at hresult
  dsimp only
  simp only [price_append]
  nlinarith only [hneg,hfirst,hthird,hcell,hbudget,hresult,hcontrol]

end Blotto.PlayerSpecificCubicConstruction
