import Blotto.PlayerSpecificSignDepthHeights

/-! Original-input linear sign precision and refined endpoint sizes. Unit
coefficient heights come from the actual cached Euclidean output. -/
namespace Blotto.PlayerSpecificSignLinearSizes
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialNormalization PlayerSpecificPolynomialHeights
open PlayerSpecificIsolationState PlayerSpecificAlgebraicReduction PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 3000000

def inputHeight (m a : Data) (node : Interval) : ℕ := PlayerSpecificRationalMagnitude.inputHeight m+
  PlayerSpecificRationalMagnitude.inputHeight a+PlayerSpecificSignEnclosure.endpointHeight node+1
def depthCoefficient : ℕ := 68*PlayerSpecificExtendedGCDHeights.linearConstant+200

theorem input_heights (m a : Data) (node : Interval) :
    HasHeight m (inputHeight m a node) ∧ HasHeight a (inputHeight m a node) ∧
      PlayerSpecificRationalMagnitude.inputHeight a ≤ inputHeight m a node ∧
      PlayerSpecificSignEnclosure.endpointHeight node ≤ inputHeight m a node ∧ 1 ≤ inputHeight m a node := by
  have hm : PlayerSpecificRationalMagnitude.inputHeight m ≤ inputHeight m a node := by unfold inputHeight; omega
  have ha : PlayerSpecificRationalMagnitude.inputHeight a ≤ inputHeight m a node := by unfold inputHeight; omega
  exact ⟨mono (input_height m) hm,mono (input_height a) ha,ha,by unfold inputHeight; omega,by unfold inputHeight; omega⟩

theorem certificate_bounds (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    (PlayerSpecificAlgebraicBezout.right m a).length≤17 ∧
      PlayerSpecificRationalMagnitude.inputHeight (PlayerSpecificAlgebraicBezout.right m a)≤
        (68*PlayerSpecificExtendedGCDHeights.linearConstant+18)*(inputHeight m a node+1) := by
  have hi:=input_heights m a node
  have hb:=PlayerSpecificAlgebraicUnitExecution.bounds RationalCostModel.schoolbook m a (inputHeight m a node)
    hi.1 hi.2.1 hi.2.2.2.2 hml (by omega)
  rw [PlayerSpecificAlgebraicUnitExecution.value] at hb
  have he:=inputHeight_le hb.1
  have hm:=Nat.mul_le_mul_right (1+2*PlayerSpecificAlgebraicUnitExecution.outputHeight (inputHeight m a node)) hb.2
  refine ⟨hb.2,?_⟩
  unfold PlayerSpecificAlgebraicUnitExecution.outputHeight PlayerSpecificAlgebraicUnitExecution.certificateHeight at he hm
  nlinarith only [he,hm]

theorem depth_profile (E H A B T d : ℕ) (ha : A≤H) (hb : B≤(68*E+18)*(H+1)) (ht : T≤H)
    (hd : d≤A+B+21*T+100) : d≤(68*E+200)*(H+1) := by
  nlinarith only [ha,hb,ht,hd]

theorem depth_linear (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3) :
    PlayerSpecificSignPrecision.depth m a node≤depthCoefficient*(inputHeight m a node+1) := by
  have hi:=input_heights m a node
  have hb:=certificate_bounds m a node hml hal
  have hd:=PlayerSpecificSignDepthHeights.depth_encoded m a node hal hb.1
  exact depth_profile PlayerSpecificExtendedGCDHeights.linearConstant (inputHeight m a node) _ _ _ _
    hi.2.2.1 hb.2 hi.2.2.2.1 hd

theorem endpoint_linear (m a : Data) (node : Interval) (hml : m.length≤4) (hal : a.length≤3)
    (hv : node.lo<node.hi) :
    RationalHeight (PlayerSpecificAlgebraicSign.leaf m a node).lo ((depthCoefficient+5)*(inputHeight m a node+1)) ∧
      RationalHeight (PlayerSpecificAlgebraicSign.leaf m a node).hi ((depthCoefficient+5)*(inputHeight m a node+1)) := by
  have he:=PlayerSpecificRefinementEndpointHeights.returned_heights (prepare m) node hv (PlayerSpecificSignPrecision.depth m a node)
  have hd:=depth_linear m a node hml hal
  have hi:=(input_heights m a node).2.2.2.1
  have hbound : 3*PlayerSpecificSignEnclosure.endpointHeight node+PlayerSpecificSignPrecision.depth m a node+2≤
      (depthCoefficient+5)*(inputHeight m a node+1) := by nlinarith only [hd,hi]
  exact ⟨he.1.mono hbound,he.2.mono hbound⟩

end Blotto.PlayerSpecificSignLinearSizes
