import Blotto.GeneralPaperDeltaPlanBounds
import Blotto.GeneralPaperEpochFieldAdvancePrice

/-! Four occurrence arrays and four cell arrays use the same pre-update
snapshot and selected row bids. Each array is filled once from retained
query plans. Only data-bearing arrays are returned; price sums are analysis.
-/
namespace Blotto.GeneralPaperFieldDeltaExecution
open GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
open GeneralPaperEpochFieldAdvancePrice (total)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def run {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan) : Deltas state × ℕ :=
  let candidate := choice.candidateBid
  let response := choice.responseBid
  let po := GeneralPaperDeltaArrayExecution.unsigned bits index price W mesh false snapshot.q.cdf snapshot.lambda.cdf state.plan.pOccurrences
  let qo := GeneralPaperDeltaArrayExecution.unsigned bits index price W mesh true snapshot.p.cdf snapshot.mu.cdf state.plan.qOccurrences
  let lo := GeneralPaperDeltaArrayExecution.signed bits index price W mesh state.plan.alphabet candidate snapshot.p.cdf state.plan.lambdaOccurrences
  let mo := GeneralPaperDeltaArrayExecution.signed bits index price W mesh state.plan.alphabet response snapshot.q.cdf state.plan.muOccurrences
  let pc := GeneralPaperDeltaArrayExecution.unsigned bits index price W mesh false snapshot.q.cdf snapshot.lambda.cdf state.plan.pCells.ranks
  let qc := GeneralPaperDeltaArrayExecution.unsigned bits index price W mesh true snapshot.p.cdf snapshot.mu.cdf state.plan.qCells.ranks
  let lc := GeneralPaperDeltaArrayExecution.signed bits index price W mesh state.plan.alphabet candidate snapshot.p.cdf state.plan.lambdaCells.ranks
  let mc := GeneralPaperDeltaArrayExecution.signed bits index price W mesh state.plan.alphabet response snapshot.q.cdf state.plan.muCells.ranks
  (⟨po.1,qo.1,lo.1,mo.1,pc.1,qc.1,lc.1,mc.1⟩,total po.2 qo.2 lo.2 mo.2 pc.2 qc.2 lc.2 mc.2+256*W)

theorem data {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run bits index price W mesh state snapshot choice).1=(generate state snapshot choice).1 := by
  unfold run generate GeneralPaperUnsignedCellUpdates.delta GeneralPaperSignedCellUpdates.delta
  dsimp only
  rw [GeneralPaperDeltaArrayExecution.unsigned_data bits index price W mesh false _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.unsigned_data bits index price W mesh true _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.signed_data bits index price W mesh _ _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.signed_data bits index price W mesh _ _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.unsigned_data bits index price W mesh false _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.unsigned_data bits index price W mesh true _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.signed_data bits index price W mesh _ _ _ _ hMesh,
    GeneralPaperDeltaArrayExecution.signed_data bits index price W mesh _ _ _ _ hMesh]

theorem same_data {k : ℕ} (price : ℕ → ℕ) (W mesh : ℕ) (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) :
    (run true (fun w => w) price W mesh state snapshot choice).1=(run false (fun _ => 1) (fun _ => 1) 1 mesh state snapshot choice).1 := by
  rw [data true (fun w => w) price W mesh _ _ _ hMesh,data false (fun _ => 1) (fun _ => 1) 1 mesh _ _ _ hMesh]

theorem returned_bound {k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W mesh : ℕ) (state : State k)
    (snapshot : Snapshot k) (choice : Choice state.plan)
    (hMesh : mesh=(GeneralPaperSourceParameters.prepare k).meshDenominator) (hp : Positive snapshot) (hc : Coherent snapshot) :
    (run bits index price W mesh state snapshot choice).1.Bounded (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) := by
  rw [data bits index price W mesh _ _ _ hMesh]
  exact generated_bound state snapshot choice hp hc

end Blotto.GeneralPaperFieldDeltaExecution
