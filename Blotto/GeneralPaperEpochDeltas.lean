import Blotto.GeneralPaperEpochSnapshot

/-! Generate all eight delta arrays from one common snapshot and one pair
of selected option indices. Both unsigned cross-payoffs and signed row/CDF
updates therefore refer to the pre-update four-block state.
-/
namespace Blotto.GeneralPaperEpochDeltas
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
open GeneralPaperEpochFieldPlan GeneralPaperEpochFieldState GeneralPaperEpochSnapshot
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Choice {k : ℕ} (plan : Plan k) where
  candidate : Fin plan.candidateCount
  response : Fin plan.responseCount

def Choice.candidateBid {k : ℕ} {plan : Plan k} (choice : Choice plan) : ℕ := plan.candidateOptions.read choice.candidate

def Choice.responseBid {k : ℕ} {plan : Plan k} (choice : Choice plan) : ℕ := plan.responseOptions.read choice.response

def generate {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) : Deltas state × ℕ :=
  let po := GeneralPaperNativeDeltaArrays.unsigned k false snapshot.q.cdf snapshot.lambda.cdf state.plan.pOccurrences
  let qo := GeneralPaperNativeDeltaArrays.unsigned k true snapshot.p.cdf snapshot.mu.cdf state.plan.qOccurrences
  let lo := GeneralPaperNativeDeltaArrays.signed k state.plan.alphabet choice.candidateBid snapshot.p.cdf state.plan.lambdaOccurrences
  let mo := GeneralPaperNativeDeltaArrays.signed k state.plan.alphabet choice.responseBid snapshot.q.cdf state.plan.muOccurrences
  let pc := GeneralPaperUnsignedCellUpdates.delta k false snapshot.q.cdf snapshot.lambda.cdf state.plan.pCells
  let qc := GeneralPaperUnsignedCellUpdates.delta k true snapshot.p.cdf snapshot.mu.cdf state.plan.qCells
  let lc := GeneralPaperSignedCellUpdates.delta k state.plan.alphabet choice.candidateBid snapshot.p.cdf state.plan.lambdaCells
  let mc := GeneralPaperSignedCellUpdates.delta k state.plan.alphabet choice.responseBid snapshot.q.cdf state.plan.muCells
  (⟨po.1,qo.1,lo.1,mo.1,pc.1,qc.1,lc.1,mc.1⟩,po.2+qo.2+lo.2+mo.2+pc.2+qc.2+lc.2+mc.2+56)

theorem generated_bound {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan)
    (hPositive : Positive snapshot) (hCoherent : Coherent snapshot) :
    (generate state snapshot choice).1.Bounded (8*(GeneralPaperSourceParameters.prepare k).meshDenominator) := by
  rcases hPositive with ⟨hp,hq,hl,hm⟩
  rcases hCoherent with ⟨cp,cq,cl,cm⟩
  dsimp only [Deltas.Bounded,generate]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · rw [state.plan.pOccurrences_spec,cq,cl]
    exact fun r => GeneralPaperNativeDeltaArrays.unsigned_bound k state.plan.alphabet false _ _ _ _ hq hl _ r
  · rw [state.plan.qOccurrences_spec,cp,cm]
    exact fun r => GeneralPaperNativeDeltaArrays.unsigned_bound k state.plan.alphabet true _ _ _ _ hp hm _ r
  · rw [state.plan.lambdaOccurrences_spec,cp]
    exact fun r => GeneralPaperNativeDeltaArrays.signed_bound k state.plan.alphabet choice.candidateBid _ _ hp _ r
  · rw [state.plan.muOccurrences_spec,cq]
    exact fun r => GeneralPaperNativeDeltaArrays.signed_bound k state.plan.alphabet choice.responseBid _ _ hq _ r
  · rw [state.plan.pCells_spec,cq,cl]
    exact fun r => GeneralPaperUnsignedCellUpdates.delta_bound k state.plan.alphabet false _ _ _ _ _ hq hl r
  · rw [state.plan.qCells_spec,cp,cm]
    exact fun r => GeneralPaperUnsignedCellUpdates.delta_bound k state.plan.alphabet true _ _ _ _ _ hp hm r
  · rw [state.plan.lambdaCells_spec,cp]
    exact fun r => GeneralPaperSignedCellUpdates.delta_bound k state.plan.alphabet choice.candidateBid _ _ _ hp r
  · rw [state.plan.muCells_spec,cq]
    exact fun r => GeneralPaperSignedCellUpdates.delta_bound k state.plan.alphabet choice.responseBid _ _ _ hq r

theorem generated_work {k : ℕ} (state : State k) (snapshot : Snapshot k) (choice : Choice state.plan) :
    (generate state snapshot choice).2=
      (2*(GeneralPaperSourceParameters.prepare k).summarySize+state.plan.pCells.partition.count+state.plan.qCells.partition.count)*(48*(30+k)+298)+
      (2*(GeneralPaperSourceParameters.prepare k).summarySize+state.plan.lambdaCells.partition.count+state.plan.muCells.partition.count)*(12*(30+k)+108)+200 := by
  unfold generate
  dsimp only
  rw [GeneralPaperNativeDeltaArrays.unsigned_work,GeneralPaperNativeDeltaArrays.unsigned_work,
    GeneralPaperNativeDeltaArrays.signed_work,GeneralPaperNativeDeltaArrays.signed_work,
    GeneralPaperUnsignedCellUpdates.delta_work,GeneralPaperUnsignedCellUpdates.delta_work,
    GeneralPaperSignedCellUpdates.delta_work,GeneralPaperSignedCellUpdates.delta_work]
  ring

end Blotto.GeneralPaperEpochDeltas
