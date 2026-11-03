import Blotto.PlayerSpecificCopyFrameCost

/-! Actual portable binary descriptions of the original rational input and
complete accepted parameter record. Every serialized word is certified
copy-only, and decoding recovers the exact original/returned record trace. -/
namespace Blotto.PlayerSpecificFiniteParameterDescription
open PlayerSpecificRationalTrace PlayerSpecificCopyFrame
set_option autoImplicit false
set_option maxHeartbeats 2500000

theorem interval_pure (node : PlayerSpecificIsolationState.Interval) : Pure (PlayerSpecificSplitExecution.copyInterval node) := by
  intro e he
  simp only [PlayerSpecificSplitExecution.copyInterval,List.mem_cons,List.not_mem_nil,or_false] at he
  rcases he with rfl|rfl|rfl|rfl|rfl <;> trivial

theorem candidate_pure (candidate : PlayerSpecificAlgebraicCandidates.Candidate) :
    Pure (PlayerSpecificCandidateSelection.copyCandidate candidate) := by
  rw [PlayerSpecificCandidateSelection.copyCandidate,pure_append]
  exact ⟨pure_copyRow _,interval_pure _⟩

theorem cell_pure (c : PlayerSpecificRationalCells.Cell) : Pure (PlayerSpecificCellTestConstruction.copyCell c) := by
  simp only [PlayerSpecificCellTestConstruction.copyCell,pure_append]
  exact ⟨⟨pure_copyRow _,pure_copyRow _⟩,pure_controls [1]⟩

theorem result_pure (result : Option PlayerSpecificFiniteParameterReturn.Result) : Pure (PlayerSpecificFiniteParameterExecution.copyResult result) := by
  cases result with
  | none => exact pure_controls [0]
  | some r =>
    simp only [PlayerSpecificFiniteParameterExecution.copyResult,pure_append]
    exact ⟨⟨⟨cell_pure _,candidate_pure _⟩,pure_copyRow _⟩,pure_controls [1]⟩

theorem frame_pure {N : ℕ} (i : RationalPlayerSpecificInput N) (result : Option PlayerSpecificFiniteParameterReturn.Result) :
    Pure (PlayerSpecificFiniteParameterExecution.frame i result) := by
  simp only [PlayerSpecificFiniteParameterExecution.frame,pure_append]
  exact ⟨⟨pure_copyRow _,result_pure _⟩,pure_controls [N,if result.isSome then 1 else 0]⟩

theorem frame_price_le {N : ℕ} (model : RationalCostModel) (i : RationalPlayerSpecificInput N) :
    price model (PlayerSpecificFiniteParameterExecution.frame i (PlayerSpecificFiniteParameterExecution.run model i).1)≤
      (PlayerSpecificFiniteParameterExecution.run model i).2 := by
  rw [PlayerSpecificFiniteParameterCost.run_eq]
  split <;> dsimp only <;> omega

structure Output where
  parameters : Option PlayerSpecificFiniteParameterReturn.Result
  bits : List Bool
  work : ℕ

def run {N : ℕ} (i : RationalPlayerSpecificInput N) : Output :=
  let recognized:=PlayerSpecificFiniteParameterExecution.run RationalCostModel.schoolbook i
  let trace:=PlayerSpecificFiniteParameterExecution.frame i recognized.1
  ⟨recognized.1,encode trace,recognized.2+PlayerSpecificCopyFrameCost.work trace⟩

theorem value {N : ℕ} (i : RationalPlayerSpecificInput N) :
    (run i).parameters=PlayerSpecificFiniteParameterReturn.run RationalCostModel.schoolbook i :=
  PlayerSpecificFiniteParameterExecution.value RationalCostModel.schoolbook i

theorem decoded {N : ℕ} (i : RationalPlayerSpecificInput N) (suffix : List Bool) :
    read ((run i).bits++suffix)=some (PlayerSpecificFiniteParameterExecution.frame i (run i).parameters,suffix) :=
  read_encode _ (frame_pure i _) suffix

end Blotto.PlayerSpecificFiniteParameterDescription
