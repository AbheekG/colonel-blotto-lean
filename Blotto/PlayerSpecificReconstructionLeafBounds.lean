import Blotto.PlayerSpecificReconstructionLeafExecution

/-! Actual refined-leaf and constructed-query data have original-input
linear sizes. No leaf height, cell index, CF precision or price is supplied. -/
namespace Blotto.PlayerSpecificReconstructionLeafBounds
open PlayerSpecificDensePolynomial PlayerSpecificIsolationState PlayerSpecificPolynomialHeights PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 5000000

def height (p : Data) : ℕ := 64*inputHeight p+2*PlayerSpecificReconstructionPrecision.depth p+64
def indexHeight (p : Data) : ℕ := 2*inputHeight p+PlayerSpecificReconstructionPrecision.depth p+4
def decodeHeight (p : Data) : ℕ := 8*inputHeight p+4

theorem height_large (p : Data) : 2≤height p := by unfold height; omega
theorem index_height (p : Data) : indexHeight p≤height p := by unfold indexHeight height; omega
theorem decode_height (p : Data) : decodeHeight p≤height p := by unfold decodeHeight height; omega
theorem decoded_height (p : Data) : 4*decodeHeight p+3≤height p := by unfold decodeHeight height; omega
theorem input_height (p : Data) : inputHeight p≤height p := by unfold height; omega

theorem height_bound (p : Data) (hlen : p.length≤4) : height p≤PlayerSpecificIntegerBudget.height (inputHeight p) := by
  have hd:=PlayerSpecificReconstructionPrecision.depth_linear p hlen
  have hc : 2*PlayerSpecificIsolationDepthHeight.linearConstant+200≤PlayerSpecificIntegerBudget.coefficient := by
    unfold PlayerSpecificIntegerBudget.coefficient
    omega
  have hm:=Nat.mul_le_mul_right (inputHeight p+1) hc
  unfold height PlayerSpecificIntegerBudget.height
  nlinarith

theorem source_width (p : Data) (hlen : p.length≤4) :
    PlayerSpecificReconstructionFilter.width (height p)≤PlayerSpecificIntegerBudget.width (inputHeight p) := by
  have h:=height_bound p hlen
  unfold PlayerSpecificReconstructionFilter.width PlayerSpecificIntegerBudget.width
  omega

theorem endpoint_heights (p : Data) (node : Interval) (hnode : node∈PlayerSpecificRationalRoots.intervals p) :
    RationalHeight node.lo (indexHeight p) ∧ RationalHeight node.hi (indexHeight p) := by
  let prepared:=prepare p
  let initial:=PlayerSpecificRootMagnitude.initial p prepared
  let depth:=PlayerSpecificReconstructionPrecision.depth p
  have hv:=(PlayerSpecificIsolationForest.valid_positive prepared depth initial
    (PlayerSpecificRootMagnitude.initial_valid p prepared) node hnode).1
  have hg:=PlayerSpecificDyadicEndpoints.forest_grid prepared depth initial 0
    (PlayerSpecificDyadicEndpoints.initial_grid p prepared) node hnode
  simp only [Nat.zero_add] at hg
  have hb:=PlayerSpecificDyadicEndpoints.forest_bounded prepared depth initial _
    (PlayerSpecificRootMagnitude.initial_valid p prepared) (PlayerSpecificDyadicEndpoints.initial_bounded p prepared) node hnode
  exact PlayerSpecificDyadicEndpoints.endpoint_height p prepared node depth hv hg hb

theorem magnitude_value (model : RationalCostModel) (p : Data) :
    (PlayerSpecificReconstructionCache.run model p).1.isolation.magnitude=PlayerSpecificRootMagnitude.rootBound p := by
  rw [PlayerSpecificReconstructionCache.isolation_value,PlayerSpecificIntegerPreparation.magnitude_value]

theorem query_data (model : RationalCostModel) (p : Data) (node : Interval)
    (hnode : node∈PlayerSpecificRationalRoots.intervals p) :
    let cache:=(PlayerSpecificReconstructionCache.run model p).1
    let located:=PlayerSpecificReconstructionIndex.run model cache.isolation.magnitude cache.buckets node
    0<cache.denominator ∧ 0<cache.buckets ∧ located.1<cache.buckets ∧ 8*cache.buckets=2^cache.lambda := by
  obtain ⟨t,ht⟩:=PlayerSpecificRationalRoots.interval_cell p node hnode
  simp only [PlayerSpecificReconstructionIndex.value,magnitude_value,
    PlayerSpecificReconstructionCache.denominator_value,PlayerSpecificReconstructionCache.buckets_value,
    PlayerSpecificReconstructionCache.lambda_value]
  rw [PlayerSpecificRootCells.index_value _ _ _ _ (PlayerSpecificRootMagnitude.rootBound_pos p) ht]
  refine ⟨PlayerSpecificReconstructionPrecision.denominator_pos p,Nat.two_pow_pos _,ht.1,?_⟩
  rw [pow_add]
  norm_num
  ring

end Blotto.PlayerSpecificReconstructionLeafBounds
