import Blotto.GeneralPaperNativeDeltaArrays

/-! Prepare unsigned cells and their query ranks once, then fill one exact
delta per cell each round from the current prefix arrays. The actual epoch
instruction list has the full-code cumulative loss effect without a supplied
cell-callback identity. Sorting and complete bit/space prices remain separate.
-/
namespace Blotto.GeneralPaperUnsignedCellUpdates
open GeneralPaperEpochCellInstructions
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Plan (k : ℕ) where
  partition : GeneralPaperPreparedPartition.Prepared
  queries : FixedArrayTable partition.count ℕ
  ranks : GeneralPaperQueryLossCounts.Plan k partition.count
  representativeWork : ℕ

def prepare {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ) : Plan k :=
  let partition := GeneralPaperUnsignedPartition.prepare U cdfSummary signedSummary options
  let representatives := GeneralPaperCellRepresentatives.build partition.intervals
  ⟨partition,representatives.1,GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary representatives.1,representatives.2⟩

def delta (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : Prefix k) (plan : Plan k) :
    FixedArrayTable plan.partition.count ℕ × ℕ :=
  GeneralPaperNativeDeltaArrays.unsigned k response cdfPrefix signedPrefix plan.ranks

def batch (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : ℕ → Prefix k) (plan : Plan k) (period : ℕ) :
    List GeneralPaperIntervalBatch.Instruction :=
  build plan.partition.intervals (GeneralPaperEpochLevelArray.execute
    (fun t => (delta k response (cdfPrefix t) (signedPrefix t) plan).1) period).1

theorem query_bound {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (r : Fin (prepare k U cdfSummary signedSummary options).partition.count) :
    (prepare k U cdfSummary signedSummary options).queries.read r<U :=
  GeneralPaperCellRepresentatives.representative_bound U _ r

theorem representative_work {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ) :
    (prepare k U cdfSummary signedSummary options).representativeWork=
      50*(prepare k U cdfSummary signedSummary options).partition.count+18 :=
  GeneralPaperCellRepresentatives.work _

theorem rank_work {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ) :
    (prepare k U cdfSummary signedSummary options).ranks.work≤
      (4*(prepare k U cdfSummary signedSummary options).partition.count+2)*((35+k)*(12*(35+k)+34)+120)+192 :=
  GeneralPaperQueryLossCounts.prepare_work k U cdfSummary signedSummary _

theorem delta_work (k : ℕ) (response : Bool) (cdfPrefix signedPrefix : Prefix k) (plan : Plan k) :
    (delta k response cdfPrefix signedPrefix plan).2=plan.partition.count*(48*(30+k)+298)+18 :=
  GeneralPaperNativeDeltaArrays.unsigned_work k response cdfPrefix signedPrefix plan.ranks

theorem delta_semantics {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : Prefix k) (hCDFMono : Monotone cdfSummary.read) (hSignedMono : Monotone signedSummary.read)
    (hCDFCodes : ∀ a, cdfSummary.read a<U) (hSignedCodes : ∀ a, signedSummary.read a<2*U)
    (r : Fin (prepare k U cdfSummary signedSummary options).partition.count) (i : ℕ)
    (hI : Contains (prepare k U cdfSummary signedSummary options).partition.intervals r i) :
    (delta k response cdfPrefix signedPrefix (prepare k U cdfSummary signedSummary options)).1.read r=
      GeneralPaperQueryLossCounts.increment k response
        (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix i) := by
  dsimp only [prepare] at r hI ⊢
  change (GeneralPaperNativeDeltaArrays.unsigned k response cdfPrefix signedPrefix
    (GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary
      (GeneralPaperCellRepresentatives.build (GeneralPaperUnsignedPartition.prepare U cdfSummary signedSummary options).intervals).1)).1.read r=_
  rw [GeneralPaperNativeDeltaArrays.unsigned_read k U response cdfSummary signedSummary cdfPrefix signedPrefix _ r]
  exact GeneralPaperUnsignedCellConstancy.increment_constant k U response cdfSummary signedSummary options cdfPrefix signedPrefix
    hCDFMono hSignedMono hCDFCodes hSignedCodes r _ i
    (GeneralPaperCellRepresentatives.contains_representative U _ r) hI

theorem delta_bound {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary cdfValues signedValues : Summary k)
    (options : FixedArrayTable m ℕ) (hCDF : 0<∑ r, cdfValues.read r) (hSigned : 0<∑ r, signedValues.read r)
    (r : Fin (prepare k U cdfSummary signedSummary options).partition.count) :
    (delta k response (GeneralPaperEpochPrefixArray.build cdfValues) (GeneralPaperEpochPrefixArray.build signedValues)
      (prepare k U cdfSummary signedSummary options)).1.read r≤8*(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  GeneralPaperNativeDeltaArrays.unsigned_bound k U response cdfSummary signedSummary cdfValues signedValues hCDF hSigned _ r

theorem cumulative_effect {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : ℕ → Prefix k) (hCDFMono : Monotone cdfSummary.read) (hSignedMono : Monotone signedSummary.read)
    (hCDFCodes : ∀ a, cdfSummary.read a<U) (hSignedCodes : ∀ a, signedSummary.read a<2*U)
    (period : ℕ) (i : Fin U) :
    GeneralPaperIntervalBatch.effect (batch k response cdfPrefix signedPrefix (prepare k U cdfSummary signedSummary options) period) i.val=
      GeneralPaperGeometricLevels.levels (fun t (a : Fin U) => GeneralPaperQueryLossCounts.increment k response
        (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary (cdfPrefix t) (signedPrefix t) a.val)) period i := by
  have he := GeneralPaperEpochCellInstructions.cumulative_effect
    (prepare k U cdfSummary signedSummary options).partition.intervals
    (fun t => (delta k response (cdfPrefix t) (signedPrefix t) (prepare k U cdfSummary signedSummary options)).1)
    (fun t (a : Fin U) => GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary (cdfPrefix t) (signedPrefix t) a.val)) 0 period
    (GeneralPaperUnsignedPartition.covers U cdfSummary signedSummary options)
    (GeneralPaperUnsignedPartition.disjoint U cdfSummary signedSummary options)
    (fun t _ r a hA => by
      simpa only [Nat.zero_add] using (delta_semantics k U response cdfSummary signedSummary options (cdfPrefix t) (signedPrefix t)
        hCDFMono hSignedMono hCDFCodes hSignedCodes r a.val hA)) i
  simpa only [batch,Nat.zero_add] using he

theorem batch_length {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : ℕ → Prefix k) (period : ℕ) :
    (batch k response cdfPrefix signedPrefix (prepare k U cdfSummary signedSummary options) period).length≤
      3*(GeneralPaperSourceParameters.prepare k).summarySize+m+1 := by
  rw [batch,build_length]
  exact GeneralPaperUnsignedPartition.count_bound U cdfSummary signedSummary options

end Blotto.GeneralPaperUnsignedCellUpdates
