import Blotto.GeneralPaperDeltaAccumulation

/-! Each actual occurrence array follows the same exact update as its full
alphabet code. Locations are constructed from the native code array and its
alphabet bounds; repeated summary occurrences remain distinct array entries.
-/
namespace Blotto.GeneralPaperOccurrenceUpdates
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

def location {m : ℕ} (U : ℕ) (codes : FixedArrayTable m ℕ) (hCodes : ∀ r, codes.read r<U) (r : Fin m) : Fin U :=
  ⟨codes.read r,hCodes r⟩

theorem unsigned_levels {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k)
    (cdfPrefix signedPrefix : ℕ → Prefix k) (codes : FixedArrayTable m ℕ) (hCodes : ∀ r, codes.read r<U)
    (count : ℕ) (r : Fin m) :
    (GeneralPaperDeltaAccumulation.run
      (fun t => GeneralPaperNativeDeltaArrays.unsigned k response (cdfPrefix t) (signedPrefix t)
        (GeneralPaperQueryLossCounts.prepare k U cdfSummary signedSummary codes)) count).1.read r=
    GeneralPaperGeometricLevels.levels (fun t (a : Fin U) => GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary (cdfPrefix t) (signedPrefix t) a.val)) count (location U codes hCodes r) := by
  rw [GeneralPaperDeltaAccumulation.read_run]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t _
  exact GeneralPaperNativeDeltaArrays.unsigned_read k U response cdfSummary signedSummary (cdfPrefix t) (signedPrefix t) codes r

theorem signed_levels {m : ℕ} (k U : ℕ) (bid : ℕ → ℕ) (summary : Summary k) (preparedPrefix : ℕ → Prefix k)
    (codes : FixedArrayTable m ℕ) (hCodes : ∀ r, codes.read r<2*U) (count : ℕ) (r : Fin m) :
    (GeneralPaperDeltaAccumulation.run
      (fun t => GeneralPaperNativeDeltaArrays.signed k U (bid t) (preparedPrefix t)
        (GeneralPaperSignedUpdatePlan.prepare k U summary codes)) count).1.read r=
    GeneralPaperGeometricLevels.levels (fun t (a : Fin (2*U)) =>
      GeneralPaperSignedUpdateReference.increment k U (bid t) summary (preparedPrefix t) a.val) count (location (2*U) codes hCodes r) := by
  rw [GeneralPaperDeltaAccumulation.read_run]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t _
  exact GeneralPaperNativeDeltaArrays.signed_read k U (bid t) summary (preparedPrefix t) codes r

theorem unsigned_cell_levels {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : ℕ → Prefix k) (hCDFMono : Monotone cdfSummary.read) (hSignedMono : Monotone signedSummary.read)
    (hCDFCodes : ∀ a, cdfSummary.read a<U) (hSignedCodes : ∀ a, signedSummary.read a<2*U)
    (count : ℕ) (r : Fin (GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options).partition.count)
    (i : Fin U) (hI : GeneralPaperEpochCellInstructions.Contains
      (GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options).partition.intervals r i.val) :
    (GeneralPaperDeltaAccumulation.run (fun t => GeneralPaperUnsignedCellUpdates.delta k response (cdfPrefix t) (signedPrefix t)
      (GeneralPaperUnsignedCellUpdates.prepare k U cdfSummary signedSummary options)) count).1.read r=
    GeneralPaperGeometricLevels.levels (fun t (a : Fin U) => GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary (cdfPrefix t) (signedPrefix t) a.val)) count i := by
  rw [GeneralPaperDeltaAccumulation.read_run]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t _
  exact GeneralPaperUnsignedCellUpdates.delta_semantics k U response cdfSummary signedSummary options (cdfPrefix t) (signedPrefix t)
    hCDFMono hSignedMono hCDFCodes hSignedCodes r i.val hI

theorem signed_cell_levels {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (preparedPrefix : ℕ → Prefix k) (selection : ℕ → Fin m) (hMono : Monotone summary.read)
    (hCodes : ∀ a, summary.read a<U) (hBid : ∀ q, options.read q<U) (count : ℕ)
    (r : Fin (GeneralPaperSignedCellUpdates.prepare k U summary options).partition.count) (i : Fin (2*U))
    (hI : GeneralPaperEpochCellInstructions.Contains (GeneralPaperSignedCellUpdates.prepare k U summary options).partition.intervals r i.val) :
    (GeneralPaperDeltaAccumulation.run (fun t => GeneralPaperSignedCellUpdates.delta k U (options.read (selection t)) (preparedPrefix t)
      (GeneralPaperSignedCellUpdates.prepare k U summary options)) count).1.read r=
    GeneralPaperGeometricLevels.levels (fun t (a : Fin (2*U)) =>
      GeneralPaperSignedUpdateReference.increment k U (options.read (selection t)) summary (preparedPrefix t) a.val) count i := by
  rw [GeneralPaperDeltaAccumulation.read_run]
  apply GeneralPaperEpochLevelArray.levels_agree
  intro t _
  exact GeneralPaperSignedCellUpdates.delta_semantics k U summary options (preparedPrefix t) hMono hCodes (selection t) (hBid _) r i.val hI

end Blotto.GeneralPaperOccurrenceUpdates
