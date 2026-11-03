import Blotto.GeneralPaperAdaptiveEpochBounds

/-! Full-code semantics of the actual eight-array update. All four losses
use one immutable snapshot and its selected rows. The cell identities are
derived from the stored prepared plans and valid ordered summary metadata.
-/
namespace Blotto.GeneralPaperEpochDeltaSemantics
open GeneralPaperEpochFieldPlan GeneralPaperEpochFieldState GeneralPaperEpochSnapshot GeneralPaperEpochDeltas
set_option autoImplicit false
set_option maxHeartbeats 3500000

def pIncrement {k : ℕ} (state : State k) (snapshot : Snapshot k) (code : ℕ) : ℕ :=
  GeneralPaperQueryLossCounts.increment k false
    (GeneralPaperNativeLossReference.reference k state.plan.alphabet state.plan.qSummary state.plan.lambdaSummary snapshot.q.cdf snapshot.lambda.cdf code)

def qIncrement {k : ℕ} (state : State k) (snapshot : Snapshot k) (code : ℕ) : ℕ :=
  GeneralPaperQueryLossCounts.increment k true
    (GeneralPaperNativeLossReference.reference k state.plan.alphabet state.plan.pSummary state.plan.muSummary snapshot.p.cdf snapshot.mu.cdf code)

def lambdaIncrement {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) (code : ℕ) : ℕ :=
  GeneralPaperSignedUpdateReference.increment k state.plan.alphabet choice.candidateBid state.plan.pSummary snapshot.p.cdf code

def muIncrement {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) (code : ℕ) : ℕ :=
  GeneralPaperSignedUpdateReference.increment k state.plan.alphabet choice.responseBid state.plan.qSummary snapshot.q.cdf code

theorem p_occurrence {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (generate state snapshot choice).1.pOccurrences.read r=pIncrement state snapshot (state.plan.pSummary.read r) := by
  change (GeneralPaperNativeDeltaArrays.unsigned k false snapshot.q.cdf snapshot.lambda.cdf state.plan.pOccurrences).1.read r=_
  rw [state.plan.pOccurrences_spec,GeneralPaperNativeDeltaArrays.unsigned_read]
  rfl

theorem q_occurrence {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (generate state snapshot choice).1.qOccurrences.read r=qIncrement state snapshot (state.plan.qSummary.read r) := by
  change (GeneralPaperNativeDeltaArrays.unsigned k true snapshot.p.cdf snapshot.mu.cdf state.plan.qOccurrences).1.read r=_
  rw [state.plan.qOccurrences_spec,GeneralPaperNativeDeltaArrays.unsigned_read]
  rfl

theorem lambda_occurrence {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (generate state snapshot choice).1.lambdaOccurrences.read r=lambdaIncrement state snapshot choice (state.plan.lambdaSummary.read r) := by
  change (GeneralPaperNativeDeltaArrays.signed k state.plan.alphabet choice.candidateBid snapshot.p.cdf state.plan.lambdaOccurrences).1.read r=_
  rw [state.plan.lambdaOccurrences_spec,GeneralPaperNativeDeltaArrays.signed_read]
  rfl

theorem mu_occurrence {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (r : Fin (GeneralPaperSourceParameters.prepare k).summarySize) :
    (generate state snapshot choice).1.muOccurrences.read r=muIncrement state snapshot choice (state.plan.muSummary.read r) := by
  change (GeneralPaperNativeDeltaArrays.signed k state.plan.alphabet choice.responseBid snapshot.q.cdf state.plan.muOccurrences).1.read r=_
  rw [state.plan.muOccurrences_spec,GeneralPaperNativeDeltaArrays.signed_read]
  rfl

theorem p_cell {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hOrdered : Ordered state.plan) (hCodes : CodesValid state.plan) :
    ∀ (r : Fin state.plan.pCells.partition.count) (i : ℕ),
      GeneralPaperEpochCellInstructions.Contains state.plan.pCells.partition.intervals r i →
      (generate state snapshot choice).1.pCells.read r=pIncrement state snapshot i := by
  change ∀ r i, GeneralPaperEpochCellInstructions.Contains state.plan.pCells.partition.intervals r i →
    (GeneralPaperUnsignedCellUpdates.delta k false snapshot.q.cdf snapshot.lambda.cdf state.plan.pCells).1.read r=pIncrement state snapshot i
  rw [state.plan.pCells_spec]
  intro r i hI
  exact GeneralPaperUnsignedCellUpdates.delta_semantics k state.plan.alphabet false _ _ _ _ _
    hOrdered.2.1 hOrdered.2.2.1 hCodes.2.1 hCodes.2.2.1 r i hI

theorem q_cell {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hOrdered : Ordered state.plan) (hCodes : CodesValid state.plan) :
    ∀ (r : Fin state.plan.qCells.partition.count) (i : ℕ),
      GeneralPaperEpochCellInstructions.Contains state.plan.qCells.partition.intervals r i →
      (generate state snapshot choice).1.qCells.read r=qIncrement state snapshot i := by
  change ∀ r i, GeneralPaperEpochCellInstructions.Contains state.plan.qCells.partition.intervals r i →
    (GeneralPaperUnsignedCellUpdates.delta k true snapshot.p.cdf snapshot.mu.cdf state.plan.qCells).1.read r=qIncrement state snapshot i
  rw [state.plan.qCells_spec]
  intro r i hI
  exact GeneralPaperUnsignedCellUpdates.delta_semantics k state.plan.alphabet true _ _ _ _ _
    hOrdered.1 hOrdered.2.2.2 hCodes.1 hCodes.2.2.2.1 r i hI

theorem lambda_cell {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hOrdered : Ordered state.plan) (hCodes : CodesValid state.plan) :
    ∀ (r : Fin state.plan.lambdaCells.partition.count) (i : ℕ),
      GeneralPaperEpochCellInstructions.Contains state.plan.lambdaCells.partition.intervals r i →
      (generate state snapshot choice).1.lambdaCells.read r=lambdaIncrement state snapshot choice i := by
  change ∀ r i, GeneralPaperEpochCellInstructions.Contains state.plan.lambdaCells.partition.intervals r i →
    (GeneralPaperSignedCellUpdates.delta k state.plan.alphabet choice.candidateBid snapshot.p.cdf state.plan.lambdaCells).1.read r=lambdaIncrement state snapshot choice i
  rw [state.plan.lambdaCells_spec]
  intro r i hI
  exact GeneralPaperSignedCellUpdates.delta_semantics k state.plan.alphabet _ _ _ hOrdered.1 hCodes.1
    choice.candidate (hCodes.2.2.2.2.1 _) r i hI

theorem mu_cell {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hOrdered : Ordered state.plan) (hCodes : CodesValid state.plan) :
    ∀ (r : Fin state.plan.muCells.partition.count) (i : ℕ),
      GeneralPaperEpochCellInstructions.Contains state.plan.muCells.partition.intervals r i →
      (generate state snapshot choice).1.muCells.read r=muIncrement state snapshot choice i := by
  change ∀ r i, GeneralPaperEpochCellInstructions.Contains state.plan.muCells.partition.intervals r i →
    (GeneralPaperSignedCellUpdates.delta k state.plan.alphabet choice.responseBid snapshot.q.cdf state.plan.muCells).1.read r=muIncrement state snapshot choice i
  rw [state.plan.muCells_spec]
  intro r i hI
  exact GeneralPaperSignedCellUpdates.delta_semantics k state.plan.alphabet _ _ _ hOrdered.2.1 hCodes.2.1
    choice.response (hCodes.2.2.2.2.2 _) r i hI

end Blotto.GeneralPaperEpochDeltaSemantics
