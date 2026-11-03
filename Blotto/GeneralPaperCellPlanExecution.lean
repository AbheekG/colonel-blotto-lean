import Blotto.GeneralPaperPlanProfileMonotonicity

/-! Complete dependent native cell plans. A fixed-partition finish builds
its representative/rank arrays once. Equality of whole plan objects then
transports partition counts without a copy or an executable cast pass.
-/
namespace Blotto.GeneralPaperCellPlanExecution
open GeneralPaperUnsignedCellConstancy (Summary)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def unsignedReference (k U : ℕ) (cdfSummary signedSummary : Summary k) (part : GeneralPaperPreparedPartition.Prepared) :
    GeneralPaperUnsignedCellUpdates.Plan k :=
  let representatives := GeneralPaperCellRepresentatives.build part.intervals
  ⟨part,representatives.1,GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary representatives.1,representatives.2⟩

def unsignedFinish (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k)
    (part : GeneralPaperPreparedPartition.Prepared) : GeneralPaperUnsignedCellUpdates.Plan k × ℕ :=
  let representatives := GeneralPaperCellRepresentativePrice.run bits index price W part.intervals
  let ranks := GeneralPaperQueryLossExecution.run bits index price W k U cdfSummary signedSummary representatives.1.1
  (⟨part,representatives.1.1,ranks.1,representatives.1.2⟩,representatives.2+ranks.2+128*W)

def unsigned {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k)
    (options : FixedArrayTable m ℕ) : GeneralPaperUnsignedCellUpdates.Plan k × ℕ :=
  let part := GeneralPaperUnsignedCellPartitionPrice.run bits index price W U cdfSummary signedSummary options
  let finished := unsignedFinish bits index price W k U cdfSummary signedSummary part.1
  (finished.1,part.2+finished.2+64*W)

theorem unsigned_finish_data (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k)
    (part : GeneralPaperPreparedPartition.Prepared) :
    (unsignedFinish bits index price W k U cdfSummary signedSummary part).1=unsignedReference k U cdfSummary signedSummary part := by
  unfold unsignedFinish unsignedReference
  dsimp only
  rw [GeneralPaperQueryLossExecution.data,GeneralPaperCellRepresentativePrice.data]

theorem unsigned_data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k)
    (options : FixedArrayTable m ℕ) :
    (unsigned bits index price W k U cdfSummary signedSummary options).1=GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options := by
  change (unsignedFinish bits index price W k U cdfSummary signedSummary
    (GeneralPaperUnsignedCellPartitionPrice.run bits index price W U cdfSummary signedSummary options).1).1=_
  rw [unsigned_finish_data]
  exact congrArg (unsignedReference k U cdfSummary signedSummary)
    (GeneralPaperUnsignedCellPartitionPrice.data bits index price W U cdfSummary signedSummary options)

theorem unsigned_queries {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k)
    (options : FixedArrayTable m ℕ) (r : Fin (unsigned bits index price W k U cdfSummary signedSummary options).1.partition.count) :
    (unsigned bits index price W k U cdfSummary signedSummary options).1.queries.read r<U :=
  GeneralPaperUnsignedCellPartitionPrice.representative_codes bits index price W U cdfSummary signedSummary options r

def signedReference (k U : ℕ) (summary : Summary k) (part : GeneralPaperPreparedPartition.Prepared) :
    GeneralPaperSignedCellUpdates.Plan k :=
  let representatives := GeneralPaperCellRepresentatives.build part.intervals
  ⟨part,representatives.1,GeneralPaperSignedUpdatePlan.prepare k U summary representatives.1,representatives.2⟩

def signedFinish (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (part : GeneralPaperPreparedPartition.Prepared) : GeneralPaperSignedCellUpdates.Plan k × ℕ :=
  let representatives := GeneralPaperCellRepresentativePrice.run bits index price W part.intervals
  let ranks := GeneralPaperSignedUpdateExecution.run bits index price W k U summary representatives.1.1
  (⟨part,representatives.1.1,ranks.1,representatives.1.2⟩,representatives.2+ranks.2+128*W)

def signed {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (options : FixedArrayTable m ℕ) : GeneralPaperSignedCellUpdates.Plan k × ℕ :=
  let part := GeneralPaperSignedCellPartitionPrice.run bits index price W U summary options
  let finished := signedFinish bits index price W k U summary part.1
  (finished.1,part.2+finished.2+64*W)

theorem signed_finish_data (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (part : GeneralPaperPreparedPartition.Prepared) :
    (signedFinish bits index price W k U summary part).1=signedReference k U summary part := by
  unfold signedFinish signedReference
  dsimp only
  rw [GeneralPaperSignedUpdateExecution.data,GeneralPaperCellRepresentativePrice.data]

theorem signed_data {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (options : FixedArrayTable m ℕ) :
    (signed bits index price W k U summary options).1=GeneralPaperSignedCellUpdates.prepare k U summary options := by
  change (signedFinish bits index price W k U summary
    (GeneralPaperSignedCellPartitionPrice.run bits index price W U summary options).1).1=_
  rw [signed_finish_data]
  exact congrArg (signedReference k U summary) (GeneralPaperSignedCellPartitionPrice.data bits index price W U summary options)

theorem signed_queries {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k)
    (options : FixedArrayTable m ℕ) (r : Fin (signed bits index price W k U summary options).1.partition.count) :
    (signed bits index price W k U summary options).1.queries.read r<2*U :=
  GeneralPaperSignedCellPartitionPrice.representative_codes bits index price W U summary options r

theorem unsigned_same_data {m : ℕ} (price : ℕ → ℕ) (W k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ) :
    (unsigned true (fun w => w) price W k U cdfSummary signedSummary options).1=
      (unsigned false (fun _ => 1) (fun _ => 1) 1 k U cdfSummary signedSummary options).1 := by
  rw [unsigned_data,unsigned_data]

theorem signed_same_data {m : ℕ} (price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    (signed true (fun w => w) price W k U summary options).1=(signed false (fun _ => 1) (fun _ => 1) 1 k U summary options).1 := by
  rw [signed_data,signed_data]

end Blotto.GeneralPaperCellPlanExecution
