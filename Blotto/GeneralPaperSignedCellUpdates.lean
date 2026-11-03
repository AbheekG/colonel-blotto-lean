import Blotto.GeneralPaperUnsignedCellUpdates

/-! Prepare signed cells/ranks once and reuse them with each round's weak
CDF and selected cached bid. Exact native delta arrays discharge the signed
epoch-end batch effect, retaining one joint signed learner.
-/
namespace Blotto.GeneralPaperSignedCellUpdates
open GeneralPaperEpochCellInstructions
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

structure Plan (k : ℕ) where
  partition : GeneralPaperPreparedPartition.Prepared
  queries : FixedArrayTable partition.count ℕ
  ranks : GeneralPaperSignedUpdatePlan.Plan k partition.count
  representativeWork : ℕ

def prepare {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) : Plan k :=
  let partition := GeneralPaperSignedPartition.prepare U summary options
  let representatives := GeneralPaperCellRepresentatives.build partition.intervals
  ⟨partition,representatives.1,GeneralPaperSignedUpdatePlan.prepare k U summary representatives.1,representatives.2⟩

def delta (k U bid : ℕ) (preparedPrefix : Prefix k) (plan : Plan k) : FixedArrayTable plan.partition.count ℕ × ℕ :=
  GeneralPaperNativeDeltaArrays.signed k U bid preparedPrefix plan.ranks

def batch (k U : ℕ) (bid : ℕ → ℕ) (preparedPrefix : ℕ → Prefix k) (plan : Plan k) (period : ℕ) :
    List GeneralPaperIntervalBatch.Instruction :=
  build plan.partition.intervals (GeneralPaperEpochLevelArray.execute (fun t => (delta k U (bid t) (preparedPrefix t) plan).1) period).1

theorem query_bound {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (r : Fin (prepare k U summary options).partition.count) : (prepare k U summary options).queries.read r<2*U :=
  GeneralPaperCellRepresentatives.representative_bound (2*U) _ r

theorem representative_work {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    (prepare k U summary options).representativeWork=50*(prepare k U summary options).partition.count+18 :=
  GeneralPaperCellRepresentatives.work _

theorem rank_work {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) :
    (prepare k U summary options).ranks.work≤
      (prepare k U summary options).partition.count*((35+k)*(12*(35+k)+34)+178)+70 :=
  GeneralPaperSignedUpdatePlan.prepare_work k U summary _

theorem delta_work (k U bid : ℕ) (preparedPrefix : Prefix k) (plan : Plan k) :
    (delta k U bid preparedPrefix plan).2=plan.partition.count*(12*(30+k)+108)+18 :=
  GeneralPaperNativeDeltaArrays.signed_work k U bid preparedPrefix plan.ranks

theorem delta_semantics {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ a, summary.read a<U) (q : Fin m) (hBid : options.read q<U)
    (r : Fin (prepare k U summary options).partition.count) (i : ℕ)
    (hI : Contains (prepare k U summary options).partition.intervals r i) :
    (delta k U (options.read q) preparedPrefix (prepare k U summary options)).1.read r=
      GeneralPaperSignedUpdateReference.increment k U (options.read q) summary preparedPrefix i := by
  dsimp only [prepare] at r hI ⊢
  change (GeneralPaperNativeDeltaArrays.signed k U (options.read q) preparedPrefix
    (GeneralPaperSignedUpdatePlan.prepare k U summary
      (GeneralPaperCellRepresentatives.build (GeneralPaperSignedPartition.prepare U summary options).intervals).1)).1.read r=_
  rw [GeneralPaperNativeDeltaArrays.signed_read k U (options.read q) summary preparedPrefix _ r]
  exact GeneralPaperSignedCellConstancy.increment_constant k U summary options preparedPrefix hMono hCodes q hBid r _ i
    (GeneralPaperCellRepresentatives.contains_representative (2*U) _ r) hI

theorem delta_bound {m : ℕ} (k U bid : ℕ) (summary values : Summary k) (options : FixedArrayTable m ℕ)
    (hTotal : 0<∑ r, values.read r) (r : Fin (prepare k U summary options).partition.count) :
    (delta k U bid (GeneralPaperEpochPrefixArray.build values) (prepare k U summary options)).1.read r≤
      8*(GeneralPaperSourceParameters.prepare k).meshDenominator :=
  GeneralPaperNativeDeltaArrays.signed_bound k U bid summary values hTotal _ r

theorem cumulative_effect {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (preparedPrefix : ℕ → Prefix k) (selection : ℕ → Fin m) (hMono : Monotone summary.read)
    (hCodes : ∀ a, summary.read a<U) (hBid : ∀ q, options.read q<U) (period : ℕ) (i : Fin (2*U)) :
    GeneralPaperIntervalBatch.effect
      (batch k U (fun t => options.read (selection t)) preparedPrefix (prepare k U summary options) period) i.val=
      GeneralPaperGeometricLevels.levels (fun t (a : Fin (2*U)) =>
        GeneralPaperSignedUpdateReference.increment k U (options.read (selection t)) summary (preparedPrefix t) a.val) period i := by
  have he := GeneralPaperEpochCellInstructions.cumulative_effect
    (prepare k U summary options).partition.intervals
    (fun t => (delta k U (options.read (selection t)) (preparedPrefix t) (prepare k U summary options)).1)
    (fun t (a : Fin (2*U)) => GeneralPaperSignedUpdateReference.increment k U (options.read (selection t)) summary (preparedPrefix t) a.val)
    0 period (GeneralPaperSignedPartition.covers U summary options) (GeneralPaperSignedPartition.disjoint U summary options)
    (fun t _ r a hA => by
      simpa only [Nat.zero_add] using (delta_semantics k U summary options (preparedPrefix t) hMono hCodes (selection t) (hBid _) r a.val hA)) i
  simpa only [batch,Nat.zero_add] using he

theorem batch_length {m : ℕ} (k U : ℕ) (bid : ℕ → ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (preparedPrefix : ℕ → Prefix k) (period : ℕ) :
    (batch k U bid preparedPrefix (prepare k U summary options) period).length≤
      4*(GeneralPaperSourceParameters.prepare k).summarySize+2*m+2 := by
  rw [batch,build_length]
  exact GeneralPaperSignedPartition.count_bound U summary options

end Blotto.GeneralPaperSignedCellUpdates
