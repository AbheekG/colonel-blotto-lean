import Blotto.PlayerSpecificCandidateExecution

/-! Original-input linear sizes and copy prices for the same cached
irreducible-candidate preparation. -/
namespace Blotto.PlayerSpecificCandidateBudget
open PlayerSpecificDensePolynomial PlayerSpecificPolynomialHeights PlayerSpecificRationalTrace
open PlayerSpecificIsolationState PlayerSpecificRationalMagnitude
set_option autoImplicit false
set_option maxHeartbeats 3000000

def heightCoefficient : ℕ := PlayerSpecificFactorContract.growthCoefficient+PlayerSpecificIsolationDepthHeight.linearConstant+16
def widthCoefficient : ℕ := 8*heightCoefficient+32+PlayerSpecificFactorContract.widthCoefficient+
  PlayerSpecificRootExecutionCost.widthCoefficient+100
def height (p : Data) : ℕ := heightCoefficient*(inputHeight p+1)
def width (p : Data) : ℕ := widthCoefficient*(inputHeight p+1)

theorem height_positive (p : Data) : 1≤height p := by unfold height heightCoefficient; nlinarith
theorem height_input (p : Data) : inputHeight p≤height p := by unfold height heightCoefficient; nlinarith
theorem wide (p : Data) : 8*height p+32≤width p := by unfold height width widthCoefficient heightCoefficient; nlinarith
theorem calibrate (p : Data) (c : ℕ) (hc : c≤widthCoefficient) : c*(inputHeight p+1)≤width p :=
  Nat.mul_le_mul_right _ hc

theorem factor_bounds (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    HasHeight (PlayerSpecificFactorContract.run model p).1.1 (height p) ∧
      HasHeight (PlayerSpecificFactorContract.run model p).1.2 (height p) ∧
      (PlayerSpecificFactorContract.run model p).1.1.length≤3 ∧
      (PlayerSpecificFactorContract.run model p).1.2.length≤4 := by
  have hb:=PlayerSpecificFactorExecutionCost.output_bounds model p.length p hp hlen (le_refl _)
    (inputHeight p) (input_height p)
  have hg:=PlayerSpecificFactorContract.growth p hlen
  have hm:=Nat.mul_le_mul_right (inputHeight p+1)
    (show PlayerSpecificFactorContract.growthCoefficient≤heightCoefficient by unfold heightCoefficient; omega)
  have hh : PlayerSpecificFactorHeights.height p.length (inputHeight p)≤height p := by
    unfold height
    omega
  exact ⟨mono hb.1 hh,mono hb.2.1 hh,hb.2.2.1,hb.2.2.2⟩

theorem node_bounds (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    ∀ node∈(PlayerSpecificRootExecution.run model p).1,
      RationalHeight node.lo (height p) ∧ RationalHeight node.hi (height p) ∧ node.loValue≤5 ∧ node.hiValue≤5 := by
  intro node hn
  have hc:=PlayerSpecificRootContract.actual_contract model p hp hlen
  have ht:=hc.2.2.2.2.2.1 node hn
  have hm:=Nat.mul_le_mul_right (inputHeight p+1)
    (show PlayerSpecificIsolationDepthHeight.linearConstant+6≤heightCoefficient by unfold heightCoefficient; omega)
  have hv : Valid (prepare p) node := (PlayerSpecificRootIsolation.valid_positive p node
    (by rw [←PlayerSpecificRootExecution.value model p]; exact hn)).1
  have hcounts:=PlayerSpecificSplitExecution.stored_counts p (prepare p) hlen node hv
  exact ⟨ht.1.mono hm,ht.2.mono hm,hcounts.1,hcounts.2.1⟩

theorem forest_copy (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    price model (PlayerSpecificForestExecution.copyForest (PlayerSpecificRootExecution.run model p).1)≤50*model.rat (width p) := by
  have hw:=wide p
  apply PlayerSpecificTraversalPrice.copyForest_cost model (width p) (by omega) _
    (PlayerSpecificRootContract.actual_contract model p hp hlen).1
  intro node hn
  have hb:=node_bounds model p hp hlen node hn
  exact PlayerSpecificSplitTraceCost.copyInterval_cost model node (height p) (width p)
    hb.1 hb.2.1 hb.2.2.1 hb.2.2.2 (by omega) (by omega)

theorem rows_cost (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    (PlayerSpecificCandidateRows.run model (PlayerSpecificFactorContract.run model p).1.1
      (PlayerSpecificFactorContract.run model p).1.2 (PlayerSpecificRootExecution.run model p).1).2≤12000*model.rat (width p) := by
  have hf:=factor_bounds model p hp hlen
  have hn:=(PlayerSpecificRootContract.actual_contract model p hp hlen).1
  have hc:=PlayerSpecificCandidateRows.run_cost model _ _ _ (height p) (width p) hf.1 hf.2.1 hf.2.2.1 hf.2.2.2
    hn (height_positive p) (wide p) (node_bounds model p hp hlen)
  have hm:=Nat.mul_le_mul_right (3000*model.rat (width p)) (show (PlayerSpecificRootExecution.run model p).1.length+1≤4 by omega)
  nlinarith only [hc,hm]

theorem rows_copy (model : RationalCostModel) (p : Data) (hp : semantics p≠0) (hlen : p.length≤4) :
    price model (PlayerSpecificCandidateRows.copyRows
      (PlayerSpecificCandidateRows.run model (PlayerSpecificFactorContract.run model p).1.1
        (PlayerSpecificFactorContract.run model p).1.2 (PlayerSpecificRootExecution.run model p).1).1)≤250*model.rat (width p) := by
  have hf:=factor_bounds model p hp hlen
  exact PlayerSpecificCandidateRows.returned_copy model _ _ _ (height p) (width p) hf.1 hf.2.1 hf.2.2.2
    (PlayerSpecificRootContract.actual_contract model p hp hlen).1 (height_positive p) (wide p) (node_bounds model p hp hlen)

end Blotto.PlayerSpecificCandidateBudget
