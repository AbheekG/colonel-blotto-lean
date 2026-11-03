import Blotto.PlayerSpecificAlgebraicInitialExecution

/-! A common operand-width envelope for the actual primitive callers
used to construct one initial algebraic field row. -/
namespace Blotto.PlayerSpecificAlgebraicInitialPrimitiveCost
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificRationalTrace PlayerSpecificAlgebraicReduction PlayerSpecificSturmVariations
set_option autoImplicit false
set_option maxHeartbeats 2500000

def widthCoefficient : ℕ := 33*PlayerSpecificPolynomialSignBudget.widthCoefficient+
  PlayerSpecificFieldCombinationCost.widthCoefficient+PlayerSpecificFieldDivisionContract.widthCoefficient+
  PlayerSpecificModularContract.widthCoefficient+2*1000000^6+4096
def width (H : ℕ) : ℕ := widthCoefficient*(H+1)

theorem large (H : ℕ) : 4096*(H+1)≤width H :=
  Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)

theorem row_copy (model : RationalCostModel) (row : Data) (H : ℕ) (h : HasHeight row H) (hl : row.length≤21) :
    price model (copyRow row)≤66*model.rat (width H) := by
  have hw:=large H
  exact PlayerSpecificExtendedCopyCost.row_cost model row H (width H) h hl (by omega) (by omega)

theorem constant_cost (model : RationalCostModel) (m : Data) (q : ℚ) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hmH : HasHeight m H) (hq : RationalHeight q H) (hH : 1≤H) :
    price model (PlayerSpecificFieldCombinationContract.constant m q).2≤200000000*model.rat (width H) := by
  have hc:=PlayerSpecificFieldCombinationCost.run_cost model false m [q] [] hm hm0 hml H hmH
    (cons_height hq (nil_height _)) (nil_height _) hH (by simp) (by simp)
  have hw : PlayerSpecificFieldCombinationCost.width H≤width H := Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)
  exact hc.trans (Nat.mul_le_mul_left _ (model.monotone hw))

theorem reduction_cost (model : RationalCostModel) (m a : Data) (H : ℕ)
    (hml : m.length≤4) (hal : a.length≤4) (hmH : HasHeight m H) (ha : HasHeight a H) (hH : 1≤H) :
    price model (PlayerSpecificDivisionExecution.run a m).2≤100000000*model.rat (width H) := by
  have hc:=PlayerSpecificDivisionTraceCost.run_cost model a m H ha hmH hH hal hml
  have hw : 2*1000000^6*(H+1)≤width H := Nat.mul_le_mul_right _ (by unfold widthCoefficient; omega)
  exact hc.trans (Nat.mul_le_mul_left _ (model.monotone hw))

theorem division_cost (model : RationalCostModel) (m a b : Data) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) (hH : 1≤H) :
    (PlayerSpecificFieldDivisionExecution.run model m a b).2≤8000000000*model.rat (width H) := by
  have hc:=PlayerSpecificFieldDivisionCost.run_cost model m a b hm hm0 hml ha hb H hmH haH hbH hH
  have hw:=(PlayerSpecificFieldDivisionContract.width_linear H).trans
    (Nat.mul_le_mul_right (H+1) (show PlayerSpecificFieldDivisionContract.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega))
  exact hc.trans (Nat.mul_le_mul_left _ (model.monotone hw))

theorem product_cost (model : RationalCostModel) (m b a : Data) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (ha : Reduced m a) (hb : Reduced m b)
    (hmH : HasHeight m H) (haH : HasHeight a H) (hbH : HasHeight b H) :
    (PlayerSpecificModularExecution.run model m b a).2≤800000000*model.rat (width H) := by
  have hal : a.length≤3 := by have hl:=ha.2; omega
  have hbl : b.length≤3 := by have hl:=hb.2; omega
  have hc:=PlayerSpecificModularExecutionCost.run_cost model m b a hm hm0 hml hbl (by omega) H hmH hbH haH
  have hw:=((PlayerSpecificModularContract.linear_bounds a (by omega) H).2).trans
    (Nat.mul_le_mul_right (H+1) (show PlayerSpecificModularContract.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega))
  exact hc.trans (Nat.mul_le_mul (by omega : 200000000*(a.length+1)≤800000000) (model.monotone hw))

theorem raw_sign_cost (model : RationalCostModel) (m p : Data) (node : PlayerSpecificIsolationState.Interval) (H : ℕ)
    (hm : Normalized m) (hm0 : m≠[]) (hml : m.length≤4) (hpl : p.length≤4)
    (hmH : HasHeight m H) (hp : HasHeight p H) (he : HasHeight [node.lo,node.hi] H) (hv : node.lo<node.hi) :
    (PlayerSpecificPolynomialSignExecution.run model m p node).2≤
      (33*PlayerSpecificPolynomialSignCost.workCoefficient)*(H+1)*model.rat (width H) := by
  have hi:=PlayerSpecificCandidateTestBudget.encoded_input m p node H hmH hp he hml hpl
  have hs:=PlayerSpecificPolynomialSignCost.run_cost model m p node hm hm0 hml hpl hv
  have hwork:=PlayerSpecificCandidateTestBudget.sign_work_profile PlayerSpecificPolynomialSignCost.workCoefficient _ H hi
  have hwidth:=PlayerSpecificCandidateTestBudget.sign_work_profile PlayerSpecificPolynomialSignBudget.widthCoefficient _ H hi
  have hw : PlayerSpecificPolynomialSignBudget.width (PlayerSpecificPolynomialSignBudget.inputHeight m p node)≤width H :=
    hwidth.trans (Nat.mul_le_mul_right (H+1) (show 33*PlayerSpecificPolynomialSignBudget.widthCoefficient≤widthCoefficient by unfold widthCoefficient; omega))
  exact hs.trans (Nat.mul_le_mul hwork (model.monotone hw))

theorem negative_cost (model : RationalCostModel) (w : ℚ) (H : ℕ) (hw : RationalHeight w H) (hH : 1≤H) :
    price model (scalar .multiply (-1) w).2≤15*model.rat (width H) := by
  have hf:=fits_mono (scalar_fits_height .multiply (-1) w H (one_height.neg.mono hH) hw)
    (show 4*H+3≤width H by have hh:=large H; omega)
  simpa only [scalar_length] using price_bound model (width H) (by have hh:=large H; omega) _ hf

end Blotto.PlayerSpecificAlgebraicInitialPrimitiveCost
