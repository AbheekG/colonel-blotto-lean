import Blotto.GeneralPaperRankStorageMonotonicity

/-! Complete native unsigned/signed cell constructors. Actual partition
counts lift representative/rank windows to closed source limits. All native
partition, finish, returned-plan, caller-control and scratch phases join. -/
namespace Blotto.GeneralPaperCellPlanConstructionStorage
open GeneralPaperEncodedScalarStorage
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPartitionConstructionStorage (unsignedExtras signedPositions signedExtras)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def unsignedPart {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ) :=
  (GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) model.rat W U cdfSummary tailSummary options).1

def signedPart {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :=
  (GeneralPaperSignedCellPartitionPrice.run true (fun w => w) model.rat W U summary options).1

theorem unsigned_part_data {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ) :
    unsignedPart model W k U cdfSummary tailSummary options=
      GeneralPaperEpochPartition.prepare U cdfSummary (unsignedExtras model W U tailSummary options) := by
  unfold unsignedPart GeneralPaperUnsignedCellPartitionPrice.run
  dsimp only
  rw [GeneralPaperEpochPartitionPrice.data]
  rfl

theorem signed_part_data {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    signedPart model W k U summary options=
      GeneralPaperEpochPartition.prepare (2*U) (signedPositions model W U summary) (signedExtras model W U options) := by
  unfold signedPart GeneralPaperSignedCellPartitionPrice.run
  dsimp only
  rw [GeneralPaperEpochPartitionPrice.data]
  rfl

theorem unsigned_returned {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ) :
    GeneralPaperEncodedCellPlans.unsignedFootprint W
      (GeneralPaperCellPlanExecution.unsigned true (fun w => w) model.rat W k U cdfSummary tailSummary options).1≤
      GeneralPaperEncodedCellPlans.unsignedProfile W (natBits U) (3*(GeneralPaperSourceParameters.prepare k).summarySize+m+1) k := by
  rw [GeneralPaperCellPlanExecution.unsigned_data]
  exact GeneralPaperEncodedCellPlans.unsigned_prepared W (natBits U) _ k U cdfSummary tailSummary options
    (GeneralPaperUnsignedPartition.count_bound U cdfSummary tailSummary options) (Nat.le_refl _)

theorem signed_returned {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    GeneralPaperEncodedCellPlans.signedFootprint W
      (GeneralPaperCellPlanExecution.signed true (fun w => w) model.rat W k U summary options).1≤
      GeneralPaperEncodedCellPlans.signedProfile W (natBits (2*U)) (4*(GeneralPaperSourceParameters.prepare k).summarySize+2*m+2) k := by
  rw [GeneralPaperCellPlanExecution.signed_data]
  exact GeneralPaperEncodedCellPlans.signed_prepared W (natBits (2*U)) _ k U summary options
    (GeneralPaperSignedPartition.count_bound U summary options) (Nat.le_refl _)

def unsignedWindow {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ)
    (inputCount usedP usedE copied cellCount repCount cdfCount tailCount : ℕ)
    (hi : inputCount≤(GeneralPaperSourceParameters.prepare k).summarySize+m)
    (hc : cellCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (hr : repCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (hCDF : cdfCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (ht : tailCount≤(unsignedPart model W k U cdfSummary tailSummary options).count+1)
    (q : Fin ((unsignedPart model W k U cdfSummary tailSummary options).count+1)) : ℕ :=
  let part := unsignedPart model W k U cdfSummary tailSummary options
  let reps := GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W part.intervals
  GeneralPaperCellPartitionConstructionStorage.unsignedWindow model W U inputCount usedP usedE copied cellCount cdfSummary tailSummary options hi
      (by rw [←unsigned_part_data model W k U cdfSummary tailSummary options]; exact hc)+
    GeneralPaperRankCutArrayStorage.representativeWindow model W U part.intervals repCount hr+
    GeneralPaperQueryLossConstructionStorage.window model W k U cdfSummary tailSummary reps.1.1 cdfCount tailCount hCDF ht q+
    GeneralPaperEncodedCellPlans.unsignedFootprint W
      (GeneralPaperCellPlanExecution.unsigned true (fun w => w) model.rat W k U cdfSummary tailSummary options).1+
    fields W [k,U,m]+(GeneralPaperCellPlanExecution.unsigned true (fun w => w) model.rat W k U cdfSummary tailSummary options).2+256*W

def unsignedProfile (model : RationalCostModel) (W k U m : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let B := 3*s+m+1
  GeneralPaperCellPartitionConstructionStorage.unsignedProfile model W U s m+
    GeneralPaperRankCutArrayStorage.representativeProfile model W U B+GeneralPaperQueryLossConstructionStorage.profile model W B k U+
    GeneralPaperEncodedCellPlans.unsignedProfile W (natBits U) B k+fields W [k,U,m]+
    GeneralPaperCellPlanPrice.unsignedProfile model.rat W m k U+256*W

theorem unsigned_bounded {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (options : FixedArrayTable m ℕ)
    (hCDFCode : ∀ i,cdfSummary.read i<U) (hTailCode : ∀ i,tailSummary.read i<2*U) (hOptions : ∀ i,options.read i<U)
    (inputCount usedP usedE copied cellCount repCount cdfCount tailCount : ℕ)
    (hi : inputCount≤(GeneralPaperSourceParameters.prepare k).summarySize+m)
    (hc : cellCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (hr : repCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (hCDF : cdfCount≤(unsignedPart model W k U cdfSummary tailSummary options).count)
    (ht : tailCount≤(unsignedPart model W k U cdfSummary tailSummary options).count+1)
    (q : Fin ((unsignedPart model W k U cdfSummary tailSummary options).count+1)) :
    unsignedWindow model W k U cdfSummary tailSummary options inputCount usedP usedE copied cellCount repCount cdfCount tailCount hi hc hr hCDF ht q≤
      unsignedProfile model W k U m := by
  have hn := GeneralPaperUnsignedCellPartitionPrice.count_bound true (fun w => w) model.rat W U cdfSummary tailSummary options
  have hp := GeneralPaperCellPartitionConstructionStorage.unsigned_bounded model W U inputCount usedP usedE copied cellCount
    cdfSummary tailSummary options hCDFCode hTailCode hOptions hi
    (by rw [←unsigned_part_data model W k U cdfSummary tailSummary options]; exact hc)
  have hrep := (GeneralPaperActualRankPlanConstructionStorage.unsigned_representatives model W k U cdfSummary tailSummary options repCount hr).trans
    (GeneralPaperRankStorageMonotonicity.representatives model W U _ _ hn)
  have hRank := (GeneralPaperActualRankPlanConstructionStorage.unsigned_cell_ranks model W k U cdfSummary tailSummary options
    (fun i => (hCDFCode i).le) (fun i => (hTailCode i).le) cdfCount tailCount hCDF ht q).trans
      (GeneralPaperRankStorageMonotonicity.loss_complete model W k U _ _ hn)
  have hout := unsigned_returned model W k U cdfSummary tailSummary options
  have hprice := GeneralPaperCellPlanPrice.unsigned_bit_work model.rat model.monotone W k U cdfSummary tailSummary options hCDFCode hTailCode hOptions
  dsimp only [unsignedWindow,unsignedProfile,unsignedPart] at hp hrep hRank hout hprice ⊢
  omega

def signedWindow {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (positionCount extraCount usedP usedE copied cellCount repCount rankCount : ℕ)
    (hp : positionCount≤2*(GeneralPaperSourceParameters.prepare k).summarySize) (he : extraCount≤2*m+1)
    (hc : cellCount≤(signedPart model W k U summary options).count)
    (hr : repCount≤(signedPart model W k U summary options).count)
    (hq : rankCount≤(signedPart model W k U summary options).count) : ℕ :=
  let part := signedPart model W k U summary options
  let reps := GeneralPaperCellRepresentativePrice.run true (fun w => w) model.rat W part.intervals
  GeneralPaperCellPartitionConstructionStorage.signedWindow model W U positionCount extraCount usedP usedE copied cellCount summary options hp he
      (by rw [←signed_part_data model W k U summary options]; exact hc)+
    GeneralPaperRankCutArrayStorage.representativeWindow model W (2*U) part.intervals repCount hr+
    GeneralPaperSignedUpdateConstructionStorage.window model W k U summary reps.1.1 rankCount hq+
    GeneralPaperEncodedCellPlans.signedFootprint W (GeneralPaperCellPlanExecution.signed true (fun w => w) model.rat W k U summary options).1+
    fields W [k,U,m]+(GeneralPaperCellPlanExecution.signed true (fun w => w) model.rat W k U summary options).2+256*W

def signedProfile (model : RationalCostModel) (W k U m : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let B := 4*s+2*m+2
  GeneralPaperCellPartitionConstructionStorage.signedProfile model W U s m+
    GeneralPaperRankCutArrayStorage.representativeProfile model W (2*U) B+GeneralPaperSignedUpdateConstructionStorage.profile model W B k U+
    GeneralPaperEncodedCellPlans.signedProfile W (natBits (2*U)) B k+fields W [k,U,m]+
    GeneralPaperCellPlanPrice.signedProfile model.rat W m k U+256*W

theorem signed_bounded {m : ℕ} (model : RationalCostModel) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ i,summary.read i<U) (hOptions : ∀ i,options.read i<U)
    (positionCount extraCount usedP usedE copied cellCount repCount rankCount : ℕ)
    (hp : positionCount≤2*(GeneralPaperSourceParameters.prepare k).summarySize) (he : extraCount≤2*m+1)
    (hc : cellCount≤(signedPart model W k U summary options).count)
    (hr : repCount≤(signedPart model W k U summary options).count)
    (hq : rankCount≤(signedPart model W k U summary options).count) :
    signedWindow model W k U summary options positionCount extraCount usedP usedE copied cellCount repCount rankCount hp he hc hr hq≤
      signedProfile model W k U m := by
  have hn := GeneralPaperSignedCellPartitionPrice.count_bound true (fun w => w) model.rat W U summary options
  have hpart := GeneralPaperCellPartitionConstructionStorage.signed_bounded model W U positionCount extraCount usedP usedE copied cellCount
    summary options hSummary hOptions hp he (by rw [←signed_part_data model W k U summary options]; exact hc)
  have hrep := (GeneralPaperActualRankPlanConstructionStorage.signed_representatives model W k U summary options repCount hr).trans
    (GeneralPaperRankStorageMonotonicity.representatives model W (2*U) _ _ hn)
  have hRank := (GeneralPaperActualRankPlanConstructionStorage.signed_cell_ranks model W k U summary options
    (fun i => (hSummary i).le) rankCount hq).trans (GeneralPaperRankStorageMonotonicity.signed_complete model W k U _ _ hn)
  have hout := signed_returned model W k U summary options
  have hprice := GeneralPaperCellPlanPrice.signed_bit_work model.rat model.monotone W k U summary options hSummary hOptions
  dsimp only [signedWindow,signedProfile,signedPart] at hpart hrep hRank hout hprice ⊢
  omega

end Blotto.GeneralPaperCellPlanConstructionStorage
