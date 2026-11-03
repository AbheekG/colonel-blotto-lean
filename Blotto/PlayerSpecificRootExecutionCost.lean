import Blotto.PlayerSpecificRootExecution
import Blotto.PlayerSpecificForestTraceCost

/-! Complete original-input root-isolator price: measured coefficient
widths, polynomial and integer preparation, initial queries, conversions,
the actual cached traversal, metadata and full returned-forest copies. -/
namespace Blotto.PlayerSpecificRootExecutionCost
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificRationalMagnitude PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 1000000

def widthCoefficient : ℕ := 4096*(PlayerSpecificIntegerBudget.coefficient+1)+PlayerSpecificTraversalPrice.widthCoefficient
def workCoefficient : ℕ := 20000000000*(PlayerSpecificIntegerBudget.coefficient+1)+
  40000*PlayerSpecificIsolationDepthHeight.linearConstant+20000
def width (p : Data) : ℕ := widthCoefficient*(inputHeight p+1)

theorem integer_width (p : Data) : PlayerSpecificIntegerBudget.width (inputHeight p)≤width p := by
  unfold PlayerSpecificIntegerBudget.width PlayerSpecificIntegerBudget.height width widthCoefficient
  nlinarith

theorem traversal_width (p : Data) : PlayerSpecificTraversalPrice.width p≤width p := by
  unfold PlayerSpecificTraversalPrice.width width widthCoefficient
  nlinarith

theorem run_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificRootExecution.run model p).2≤workCoefficient*(inputHeight p+1)*model.rat (width p) := by
  let H:=inputHeight p
  let W:=width p
  let computed:=PlayerSpecificIntegerPreparation.run model p
  let cached : Prepared p:=⟨computed.1.polynomials.rows,(PlayerSpecificIntegerPreparation.polynomial_values model p).2.2⟩
  let initial:=PlayerSpecificInitialExecution.run cached computed.1.magnitude
  let isolated:=PlayerSpecificForestExecution.run cached computed.1.depth initial.1
  have hinit : initial.1=PlayerSpecificRootMagnitude.initial p cached := by
    rw [PlayerSpecificInitialExecution.value,PlayerSpecificIntegerPreparation.magnitude_value]
    rfl
  have hp0:=PlayerSpecificIntegerPreparationCost.run_cost model p hlen
  have hpp:=hp0.trans (Nat.mul_le_mul_left (20000000000*(PlayerSpecificIntegerBudget.height H+1)) (model.monotone (integer_width p)))
  have hfactor : PlayerSpecificIntegerBudget.height H+1≤(PlayerSpecificIntegerBudget.coefficient+1)*(H+1) := by
    unfold PlayerSpecificIntegerBudget.height
    nlinarith
  have hprep:=hpp.trans (Nat.mul_le_mul_right (model.rat W) (Nat.mul_le_mul_left 20000000000 hfactor))
  have hi : price model initial.2≤9000*model.rat (PlayerSpecificTraversalPrice.width p) := by
    change price model (PlayerSpecificInitialExecution.run cached computed.1.magnitude).2≤_
    rw [PlayerSpecificIntegerPreparation.magnitude_value]
    exact PlayerSpecificInitialExecution.run_cost model p cached hlen
  have hip:=hi.trans (Nat.mul_le_mul_left 9000 (model.monotone (traversal_width p)))
  have ht : price model isolated.2≤(30600*PlayerSpecificIsolationDepthHeight.linearConstant+5100)*(H+1)*
      model.rat (PlayerSpecificTraversalPrice.width p) := by
    change price model (PlayerSpecificForestExecution.run cached computed.1.depth initial.1).2≤_
    rw [PlayerSpecificIntegerPreparation.depth_value,hinit,PlayerSpecificRootExecution.prepared_eq cached]
    exact PlayerSpecificForestTraceCost.traversal_cost model p hp hlen
  have htp:=ht.trans (Nat.mul_le_mul_left ((30600*PlayerSpecificIsolationDepthHeight.linearConstant+5100)*(H+1))
    (model.monotone (traversal_width p)))
  have hc : price model (PlayerSpecificForestExecution.copyForest isolated.1)≤50*model.rat (PlayerSpecificTraversalPrice.width p) := by
    change price model (PlayerSpecificForestExecution.copyForest (PlayerSpecificForestExecution.run cached computed.1.depth initial.1).1)≤_
    rw [PlayerSpecificIntegerPreparation.depth_value,hinit,PlayerSpecificRootExecution.prepared_eq cached]
    exact PlayerSpecificTraversalPrice.output_copy_cost model p (prepare p) hp hlen (PlayerSpecificRootIsolation.depth p)
      (PlayerSpecificRootMagnitude.initial p (prepare p)) 0 (by omega)
      (PlayerSpecificRootMagnitude.initial_valid p (prepare p)) (PlayerSpecificDyadicEndpoints.initial_grid p (prepare p))
      (PlayerSpecificDyadicEndpoints.initial_bounded p (prepare p))
  have hcp:=hc.trans (Nat.mul_le_mul_left 50 (model.monotone (traversal_width p)))
  have hmag : binaryWordWidth computed.1.magnitude=2*H+3 := by
    rw [PlayerSpecificIntegerPreparation.magnitude_value,PlayerSpecificIsolationDepthHeight.root_width]
  have hcast : 64*(1+binaryWordWidth computed.1.magnitude)≤256*(H+1) := by omega
  have hP : 1≤model.rat W := ((by decide : 1≤600).trans ((PlayerSpecificTraversalPrice.width_large p).trans (traversal_width p))).trans (model.word_le W)
  have hcastp:=hcast.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left (256*(H+1)) hP)
  have hd : computed.1.depth≤PlayerSpecificIsolationDepthHeight.linearConstant*(H+1) := by
    rw [PlayerSpecificIntegerPreparation.depth_value]
    exact PlayerSpecificIsolationDepthHeight.depth_linear p hlen
  have hlength : isolated.1.length≤3 := by
    have hv : isolated.1=PlayerSpecificRootIsolation.run p := PlayerSpecificRootExecution.value model p
    rw [hv]
    exact PlayerSpecificRootIsolation.length_le_three p hp hlen
  have hdepthword:=control_width computed.1.depth
  have hlenword:=control_width isolated.1.length
  have hmeta : 32*(2+binaryWordWidth computed.1.depth+binaryWordWidth isolated.1.length)≤
      (32*PlayerSpecificIsolationDepthHeight.linearConstant+224)*(H+1) := by nlinarith only [hd,hdepthword,hlenword,hlength]
  have hmetap:=hmeta.trans (by simpa only [Nat.mul_one] using Nat.mul_le_mul_left ((32*PlayerSpecificIsolationDepthHeight.linearConstant+224)*(H+1)) hP)
  change computed.2+price model initial.2+price model isolated.2+64*(1+binaryWordWidth computed.1.magnitude)+
    price model (PlayerSpecificForestExecution.copyForest isolated.1)+32*(2+binaryWordWidth computed.1.depth+binaryWordWidth isolated.1.length)≤_
  change _≤workCoefficient*(H+1)*model.rat W
  unfold workCoefficient
  nlinarith only [hprep,hip,htp,hcp,hcastp,hmetap]

end Blotto.PlayerSpecificRootExecutionCost
