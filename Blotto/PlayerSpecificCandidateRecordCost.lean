import Blotto.PlayerSpecificCandidateTestContract

/-! Full retained candidate records include the original Sturm endpoint
counters. Their bounds are derived from actual root isolation, rather than
assumed from a coefficient-only representation. -/
namespace Blotto.PlayerSpecificCandidateRecordCost
open PlayerSpecificDensePolynomial PlayerSpecificRationalCells PlayerSpecificRationalCellHeights
open PlayerSpecificAlgebraicCandidates PlayerSpecificRationalTrace
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem counters (model : RationalCostModel) (p : Data) (_hp : semantics p≠0) (hlen : p.length≤4)
    (candidate : Candidate) (hmem : candidate∈(PlayerSpecificCandidateExecution.run model p).1) :
    candidate.interval.loValue≤5 ∧ candidate.interval.hiValue≤5 := by
  rw [PlayerSpecificCandidateExecution.value,PlayerSpecificAlgebraicCandidates.run] at hmem
  obtain ⟨node,hnode,rfl⟩:=List.mem_map.mp hmem
  rw [select_interval]
  have hv:=(PlayerSpecificRootIsolation.valid_positive p node hnode).1
  have hc:=PlayerSpecificSplitExecution.stored_counts p (PlayerSpecificIsolationState.prepare p) hlen node hv
  exact ⟨hc.1,hc.2.1⟩

theorem width_profile (C D H : ℕ) (hD : 128≤D) :
    8*(C*(H+1))+128*(H+1)≤(D*(C+10))*(H+1) := by
  have hm:=Nat.mul_le_mul_right ((C+10)*(H+1)) hD
  nlinarith only [hm]

theorem wide (H : ℕ) :
    8*PlayerSpecificCellCandidateHeights.height H+128*(H+1)≤
      PlayerSpecificCandidateTestContract.widthCoefficient*(H+1) := by
  exact width_profile PlayerSpecificCellCandidateHeights.coefficient PlayerSpecificCandidateTestBudget.widthCoefficient H
    (by unfold PlayerSpecificCandidateTestBudget.widthCoefficient; omega)

theorem copy_cost (model : RationalCostModel) (c : Cell) (b : ℚ) (H : ℕ)
    (hc : CellHeight c H) (hb : RationalHeight b H) (hp : semantics (cubic c.state.coefficients b)≠0)
    (candidate : Candidate) (hmem : candidate∈PlayerSpecificFiniteCellSearch.roots model c b) :
    price model (PlayerSpecificCandidateSelection.copyCandidate candidate)≤
      81*model.rat (PlayerSpecificCandidateTestContract.widthCoefficient*(H+1)) := by
  have hs:=PlayerSpecificCellCandidateHeights.generated model c b H hc hb hp candidate hmem
  have hf:=PlayerSpecificCandidateFieldInput.field_input model _ hp (by rfl) candidate hmem
  have hn:=counters model _ hp (by rfl) candidate hmem
  have hw:=wide H
  exact PlayerSpecificCandidateSelection.copy_cost model candidate (PlayerSpecificCellCandidateHeights.height H) _
    hs.1 hf.2.2.1 hs.2.1 hs.2.2 hn.1 hn.2 (by omega) (by omega)

end Blotto.PlayerSpecificCandidateRecordCost
