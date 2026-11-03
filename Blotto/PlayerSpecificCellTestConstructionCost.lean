import Blotto.PlayerSpecificCellTestCopyCost

/-! All candidate-test construction arithmetic and enclosing copies have
a complete linear-width constant-work source bound. -/
namespace Blotto.PlayerSpecificCellTestConstructionCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalCells
open PlayerSpecificRationalCellHeights PlayerSpecificRationalTrace PlayerSpecificCellTestConstruction
open PlayerSpecificCellTestCopyCost
set_option autoImplicit false
set_option maxHeartbeats 2000000

theorem run_cost (model : RationalCostModel) (c : Cell) (H : ℕ) (hc : CellHeight c H) (hH : 1≤H) :
    price model (run c).2≤1000*model.rat (width H) := by
  have h2 : RationalHeight (2:ℚ) 2 := by norm_num [RationalHeight]
  have hone : RationalHeight (-1:ℚ) (H+2) := one_height.neg.mono (by omega)
  have hpref : RationalHeight (scalar .multiply 2 c.state.prefixMax).1 (H+2) := by
    simpa only [scalar,Arithmetic.apply,Nat.add_comm] using h2.mul hc.1.2.2.2.2
  have scalar_bound (op : Arithmetic) (a b : ℚ) (ha : RationalHeight a (H+2)) (hb : RationalHeight b (H+2)) :
      price model (scalar op a b).2≤15*model.rat (width H) := by
    have hf:=fits_mono (scalar_fits_height op a b (H+2) ha hb) (show 4*(H+2)+3≤width H by unfold width; omega)
    have hp:=price_bound model (width H) (by unfold width; omega) _ hf
    rwa [scalar_length] at hp
  have hl:=scalar_bound .multiply (-1) c.lower hone (hc.2.1.mono (by omega))
  have hp:=scalar_bound .multiply 2 c.state.prefixMax (h2.mono (by omega)) (hc.1.2.2.2.2.mono (by omega))
  have hf:=scalar_bound .subtract c.state.coefficients.B2 (scalar .multiply 2 c.state.prefixMax).1
    (hc.1.2.2.2.1.mono (by omega)) hpref
  have hs:=scalar_bound .multiply (-2) c.suffixMax (h2.neg.mono (by omega)) (hc.2.2.2.mono (by omega))
  have hcell:=cell_cost model c H hc
  have hresult:=result_cost model c H hc hH
  have hcontrol:=control model H 5 (by decide)
  rw [run]
  dsimp only [run] at hresult
  dsimp only
  simp only [price_append]
  nlinarith only [hl,hp,hf,hs,hcell,hresult,hcontrol]

end Blotto.PlayerSpecificCellTestConstructionCost
