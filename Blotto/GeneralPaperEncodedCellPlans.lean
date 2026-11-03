import Blotto.GeneralPaperEncodedPartitionStorage

/-! Complete retained cell plans: partition endpoints, representatives,
rank plans and native annotations. Constructor counts and clamped endpoint
bounds supply the premises; no plan is rebuilt or scanned during execution. -/
namespace Blotto.GeneralPaperEncodedCellPlans
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 4096

def unsignedFootprint {k : ℕ} (W : ℕ) (plan : GeneralPaperUnsignedCellUpdates.Plan k) : ℕ :=
  GeneralPaperEncodedPartitionStorage.footprint W plan.partition+GeneralPaperEncodedNatArray.footprint W plan.queries+
    GeneralPaperEncodedRankPlans.lossFootprint W plan.ranks+(1+binaryWordWidth plan.representativeWork)+64*W

def unsignedProfile (W L B k : ℕ) : ℕ :=
  GeneralPaperEncodedPartitionStorage.profile W L B+B*(L+W)+GeneralPaperEncodedRankPlans.lossProfile W B k+50*B+20+96*W

theorem unsigned_prepared {n : ℕ} (W L B k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable n ℕ)
    (hCount : (GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options).partition.count≤B)
    (hU : 1+binaryWordWidth U≤L) :
    unsignedFootprint W (GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options)≤unsignedProfile W L B k := by
  let plan := GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options
  have hp : GeneralPaperEncodedPartitionStorage.footprint W plan.partition≤GeneralPaperEncodedPartitionStorage.profile W L B :=
    GeneralPaperEncodedPartitionStorage.constructed W L B U _ hCount hU
  have hWords (i : Fin plan.partition.count) : 1+binaryWordWidth (plan.queries.read i)≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperUnsignedCellUpdates.query_bound k U cdfSummary signedSummary options i).le) 1).trans hU
  have hq := GeneralPaperEncodedNatArray.bounded_length W L B plan.queries hCount hWords
  have hr : GeneralPaperEncodedRankPlans.lossFootprint W plan.ranks≤GeneralPaperEncodedRankPlans.lossProfile W B k :=
    (GeneralPaperEncodedRankPlans.loss W k U cdfSummary signedSummary plan.queries).trans
      (GeneralPaperEncodedRankPlans.loss_mono W k _ B hCount)
  have hRep : plan.representativeWork≤50*B+18 := by
    rw [GeneralPaperUnsignedCellUpdates.representative_work]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 50 hCount) 18
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ hRep
  change GeneralPaperEncodedPartitionStorage.footprint W plan.partition+GeneralPaperEncodedNatArray.footprint W plan.queries+
    GeneralPaperEncodedRankPlans.lossFootprint W plan.ranks+(1+binaryWordWidth plan.representativeWork)+64*W≤_
  unfold unsignedProfile
  nlinarith only [hp,hq,hr,hw]

def signedFootprint {k : ℕ} (W : ℕ) (plan : GeneralPaperSignedCellUpdates.Plan k) : ℕ :=
  GeneralPaperEncodedPartitionStorage.footprint W plan.partition+GeneralPaperEncodedNatArray.footprint W plan.queries+
    GeneralPaperEncodedSignedPlans.footprint W plan.ranks+(1+binaryWordWidth plan.representativeWork)+64*W

def signedProfile (W L B k : ℕ) : ℕ :=
  GeneralPaperEncodedPartitionStorage.profile W L B+B*(L+W)+GeneralPaperEncodedSignedPlans.profile W L B k+50*B+20+96*W

theorem signed_prepared {n : ℕ} (W L B k U : ℕ) (summary : Summary k) (options : FixedArrayTable n ℕ)
    (hCount : (GeneralPaperSignedCellUpdates.prepare k U summary options).partition.count≤B)
    (hU : 1+binaryWordWidth (2*U)≤L) :
    signedFootprint W (GeneralPaperSignedCellUpdates.prepare k U summary options)≤signedProfile W L B k := by
  let plan := GeneralPaperSignedCellUpdates.prepare k U summary options
  have hp : GeneralPaperEncodedPartitionStorage.footprint W plan.partition≤GeneralPaperEncodedPartitionStorage.profile W L B :=
    GeneralPaperEncodedPartitionStorage.constructed W L B (2*U) _ hCount hU
  have hWords (i : Fin plan.partition.count) : 1+binaryWordWidth (plan.queries.read i)≤L :=
    (Nat.add_le_add_left (binaryWordWidth_mono (GeneralPaperSignedCellUpdates.query_bound k U summary options i).le) 1).trans hU
  have hq := GeneralPaperEncodedNatArray.bounded_length W L B plan.queries hCount hWords
  have hr : GeneralPaperEncodedSignedPlans.footprint W plan.ranks≤GeneralPaperEncodedSignedPlans.profile W L B k :=
    (GeneralPaperEncodedSignedPlans.prepared W L k U summary plan.queries hWords).trans
      (GeneralPaperEncodedSignedPlans.profile_mono W L k _ B hCount)
  have hRep : plan.representativeWork≤50*B+18 := by
    rw [GeneralPaperSignedCellUpdates.representative_work]
    exact Nat.add_le_add_right (Nat.mul_le_mul_left 50 hCount) 18
  have hw := GeneralPaperEncodedFixedVector.annotation _ _ hRep
  change GeneralPaperEncodedPartitionStorage.footprint W plan.partition+GeneralPaperEncodedNatArray.footprint W plan.queries+
    GeneralPaperEncodedSignedPlans.footprint W plan.ranks+(1+binaryWordWidth plan.representativeWork)+64*W≤_
  unfold signedProfile
  nlinarith only [hp,hq,hr,hw]

theorem source_unsigned {k : ℕ} (W : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (cdfSummary signedSummary : Summary k)
    (options : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ) :
    unsignedFootprint W (GeneralPaperUnsignedCellUpdates.prepare k (8*a.C) cdfSummary signedSummary options)≤
      unsignedProfile W (GeneralPaperDecoderControls.operandWidth a.lambda) (GeneralPaperBatchCounterPrice.limit k) k := by
  apply unsigned_prepared
  · exact (GeneralPaperUnsignedPartition.count_bound (8*a.C) cdfSummary signedSummary options).trans
      (by unfold GeneralPaperBatchCounterPrice.limit; omega)
  · apply GeneralPaperEncodedSignedPlans.code_word
    rw [a.dyadic]
    exact Nat.pow_le_pow_right (by decide : 1≤(2:ℕ)) (by omega)

theorem source_signed {k : ℕ} (W : ℕ) (a : GeneralPaperCodeAlphabet.Alphabet) (summary : Summary k)
    (options : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+2) ℕ) :
    signedFootprint W (GeneralPaperSignedCellUpdates.prepare k (8*a.C) summary options)≤
      signedProfile W (GeneralPaperDecoderControls.operandWidth a.lambda) (GeneralPaperBatchCounterPrice.limit k) k := by
  apply signed_prepared
  · exact (GeneralPaperSignedPartition.count_bound (8*a.C) summary options).trans
      (by unfold GeneralPaperBatchCounterPrice.limit; omega)
  · apply GeneralPaperEncodedSignedPlans.code_word
    rw [a.dyadic,pow_succ]
    omega

end Blotto.GeneralPaperEncodedCellPlans
