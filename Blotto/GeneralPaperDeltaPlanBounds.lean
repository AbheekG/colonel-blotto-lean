import Blotto.GeneralPaperDeltaArrayPrice

/-! Constructed field plans derive all signed code/position/bid caps. Cell
representatives come from clipped partitions; projecting the signed code
retains the unsigned domain. All proofs and calibrations are erased.
-/
namespace Blotto.GeneralPaperDeltaPlanBounds
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def SignedSafe {n k : ℕ} (lambda : ℕ) (plan : GeneralPaperSignedUpdatePlan.Plan k n) : Prop :=
  ∀ q,plan.codes.read q≤2^(lambda+1) ∧ plan.positions.read q≤2^(lambda+1)

structure PlanSafe {k : ℕ} (lambda : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k) : Prop where
  alphabet : plan.alphabet≤2^(lambda+1)
  candidate : ∀ q,plan.candidateOptions.read q≤2^(lambda+1)
  response : ∀ q,plan.responseOptions.read q≤2^(lambda+1)
  lambdaOccurrences : SignedSafe lambda plan.lambdaOccurrences
  muOccurrences : SignedSafe lambda plan.muOccurrences
  lambdaCells : SignedSafe lambda plan.lambdaCells.ranks
  muCells : SignedSafe lambda plan.muCells.ranks

theorem prepared_safe {n k : ℕ} (lambda U : ℕ) (summary : GeneralPaperUnsignedCellConstancy.Summary k)
    (codes : FixedArrayTable n ℕ) (hU : U=2^lambda) (hCodes : ∀ q,codes.read q<2*U) :
    SignedSafe lambda (GeneralPaperSignedUpdatePlan.prepare k U summary codes) := by
  have hDouble : 2*U=2^(lambda+1) := by rw [pow_succ,←hU]; omega
  have hCap : U≤2^(lambda+1) := by rw [hU]; exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_succ _)
  intro q
  constructor
  · change codes.read q≤2^(lambda+1)
    exact (hCodes q).le.trans_eq hDouble
  · change (GeneralPaperSignedUpdatePlan.projected U codes).1.read q≤2^(lambda+1)
    rw [GeneralPaperSignedUpdatePlan.projected_read]
    exact (GeneralPaperUnsignedPartition.project_bound U (codes.read q) (hCodes q)).le.trans hCap

theorem cells_safe {n k : ℕ} (lambda U : ℕ) (summary : GeneralPaperUnsignedCellConstancy.Summary k)
    (options : FixedArrayTable n ℕ) (hU : U=2^lambda) :
    SignedSafe lambda (GeneralPaperSignedCellUpdates.prepare k U summary options).ranks := by
  unfold GeneralPaperSignedCellUpdates.prepare
  dsimp only
  apply prepared_safe lambda U summary _ hU
  intro q
  exact GeneralPaperCellRepresentatives.representative_bound (2*U) _ q

theorem of_codes {k : ℕ} (lambda : ℕ) (plan : GeneralPaperEpochFieldPlan.Plan k)
    (hU : plan.alphabet=2^lambda) (hCodes : GeneralPaperEpochFieldPlan.CodesValid plan) : PlanSafe lambda plan := by
  have hCap : plan.alphabet≤2^(lambda+1) := by
    rw [hU]
    exact Nat.pow_le_pow_right (by decide : 0<(2:ℕ)) (Nat.le_succ _)
  refine ⟨hCap,fun q => (hCodes.2.2.2.2.1 q).le.trans hCap,
    fun q => (hCodes.2.2.2.2.2 q).le.trans hCap,?_,?_,?_,?_⟩
  · rw [plan.lambdaOccurrences_spec]
    exact prepared_safe lambda plan.alphabet plan.pSummary plan.lambdaSummary hU hCodes.2.2.1
  · rw [plan.muOccurrences_spec]
    exact prepared_safe lambda plan.alphabet plan.qSummary plan.muSummary hU hCodes.2.2.2.1
  · rw [plan.lambdaCells_spec]
    exact cells_safe lambda plan.alphabet plan.pSummary plan.candidateOptions hU
  · rw [plan.muCells_spec]
    exact cells_safe lambda plan.alphabet plan.qSummary plan.responseOptions hU

theorem actual_plan {m k : ℕ} (cache : GeneralPaperCatalogueEpochCache.Cache m k)
    (hCodes : GeneralPaperCatalogueEpochMetadata.CodesValid cache) (j : Fin m) :
    PlanSafe cache.alphabet.lambda (cache.plans.read j) := by
  apply of_codes
  · rw [GeneralPaperCatalogueEpochCache.plan_read]
    exact cache.alphabet.dyadic
  · exact GeneralPaperCatalogueEpochMetadata.field_codes cache hCodes j

end Blotto.GeneralPaperDeltaPlanBounds
