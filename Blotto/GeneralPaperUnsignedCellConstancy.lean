import Blotto.GeneralPaperUnsignedPartition

/-! Actual mesh counts and integer primal/response increments are constant
on the constructed unsigned cells, for every current prefix array. This
uses identical occurrence membership, not an assumed loss callback.
-/
namespace Blotto.GeneralPaperUnsignedCellConstancy
open GeneralPaperEpochCellInstructions GeneralPaperUnsignedPartition
set_option autoImplicit false
set_option maxHeartbeats 3500000

abbrev Summary (k : ℕ) := FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ
abbrev Prefix (k : ℕ) := FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ

theorem cdf_counts {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (preparedPrefix : Prefix k) (hMono : Monotone cdfSummary.read) (hCodes : ∀ a, cdfSummary.read a<U)
    (r : Fin (prepare U cdfSummary signedSummary options).count) (i j : ℕ)
    (hI : Contains (prepare U cdfSummary signedSummary options).intervals r i)
    (hJ : Contains (prepare U cdfSummary signedSummary options).intervals r j) :
    GeneralPaperRankedCDFQuery.referenceCount k cdfSummary preparedPrefix i=
      GeneralPaperRankedCDFQuery.referenceCount k cdfSummary preparedPrefix j ∧
    GeneralPaperRankedCDFQuery.referenceCount k cdfSummary preparedPrefix (i+1)=
      GeneralPaperRankedCDFQuery.referenceCount k cdfSummary preparedPrefix (j+1) := by
  constructor
  · unfold GeneralPaperRankedCDFQuery.referenceCount
    rw [GeneralPaperCellCDFConstancy.same_members_position k cdfSummary hMono i j
      (fun a => GeneralPaperEpochPartition.strict_test_constant U cdfSummary _ a (hCodes a) r i j hI hJ)]
  · unfold GeneralPaperRankedCDFQuery.referenceCount
    have he : ∀ a, cdfSummary.read a< i+1 ↔ cdfSummary.read a<j+1 := by
      intro a
      have hc := GeneralPaperEpochPartition.weak_test_constant U cdfSummary (extras U signedSummary options).1 a (hCodes a) r i j hI hJ
      omega
    rw [GeneralPaperCellCDFConstancy.same_members_position k cdfSummary hMono (i+1) (j+1) he]

theorem tail_counts {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (preparedPrefix : Prefix k) (hMono : Monotone signedSummary.read) (hCodes : ∀ a, signedSummary.read a<2*U)
    (r : Fin (prepare U cdfSummary signedSummary options).count) (i j : ℕ)
    (hI : Contains (prepare U cdfSummary signedSummary options).intervals r i)
    (hJ : Contains (prepare U cdfSummary signedSummary options).intervals r j) :
    GeneralPaperRankedInterval.referenceCount k signedSummary preparedPrefix i U=
      GeneralPaperRankedInterval.referenceCount k signedSummary preparedPrefix j U ∧
    GeneralPaperRankedInterval.referenceCount k signedSummary preparedPrefix (U+i) (2*U)=
      GeneralPaperRankedInterval.referenceCount k signedSummary preparedPrefix (U+j) (2*U) := by
  have hi := GeneralPaperCellRepresentatives.contains_bound U _ r i hI
  have hj := GeneralPaperCellRepresentatives.contains_bound U _ r j hJ
  have he := projected_test_constant U cdfSummary signedSummary options
  constructor
  · apply GeneralPaperRankedInterval.same_lower_position k signedSummary preparedPrefix hMono i j U
    intro a
    have hc := he a (hCodes a) r i j hI hJ
    unfold GeneralPaperSignedUpdatePlan.project at hc
    by_cases hA : signedSummary.read a<U
    · simp only [hA,ite_true] at hc
      exact hc
    · omega
  · apply GeneralPaperRankedInterval.same_lower_position k signedSummary preparedPrefix hMono (U+i) (U+j) (2*U)
    intro a
    have hc := he a (hCodes a) r i j hI hJ
    unfold GeneralPaperSignedUpdatePlan.project at hc
    by_cases hA : signedSummary.read a<U
    · omega
    · simp only [hA,ite_false] at hc
      omega

theorem reference_constant {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : Prefix k) (hCDFMono : Monotone cdfSummary.read) (hSignedMono : Monotone signedSummary.read)
    (hCDFCodes : ∀ a, cdfSummary.read a<U) (hSignedCodes : ∀ a, signedSummary.read a<2*U)
    (r : Fin (prepare U cdfSummary signedSummary options).count) (i j : ℕ)
    (hI : Contains (prepare U cdfSummary signedSummary options).intervals r i)
    (hJ : Contains (prepare U cdfSummary signedSummary options).intervals r j) :
    GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix i=
      GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix j := by
  have hc := cdf_counts k U cdfSummary signedSummary options cdfPrefix hCDFMono hCDFCodes r i j hI hJ
  have ht := tail_counts k U cdfSummary signedSummary options signedPrefix hSignedMono hSignedCodes r i j hI hJ
  unfold GeneralPaperNativeLossReference.reference
  rw [hc.1,hc.2,ht.1,ht.2]

theorem increment_constant {m : ℕ} (k U : ℕ) (response : Bool) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (cdfPrefix signedPrefix : Prefix k) (hCDFMono : Monotone cdfSummary.read) (hSignedMono : Monotone signedSummary.read)
    (hCDFCodes : ∀ a, cdfSummary.read a<U) (hSignedCodes : ∀ a, signedSummary.read a<2*U)
    (r : Fin (prepare U cdfSummary signedSummary options).count) (i j : ℕ)
    (hI : Contains (prepare U cdfSummary signedSummary options).intervals r i)
    (hJ : Contains (prepare U cdfSummary signedSummary options).intervals r j) :
    GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix i)=
    GeneralPaperQueryLossCounts.increment k response
      (GeneralPaperNativeLossReference.reference k U cdfSummary signedSummary cdfPrefix signedPrefix j) := by
  rw [reference_constant k U cdfSummary signedSummary options cdfPrefix signedPrefix hCDFMono hSignedMono hCDFCodes hSignedCodes r i j hI hJ]

end Blotto.GeneralPaperUnsignedCellConstancy
