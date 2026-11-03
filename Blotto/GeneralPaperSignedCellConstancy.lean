import Blotto.GeneralPaperSignedPartition

/-! The constructed signed cells preserve the sign, row indicator and
rounded weak CDF simultaneously, for a bid selected from the cached options.
-/
namespace Blotto.GeneralPaperSignedCellConstancy
open GeneralPaperEpochCellInstructions GeneralPaperSignedPartition
open GeneralPaperUnsignedCellConstancy (Summary Prefix)
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem cdf_count {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ a, summary.read a<U)
    (r : Fin (prepare U summary options).count) (i j : ℕ)
    (hI : Contains (prepare U summary options).intervals r i) (hJ : Contains (prepare U summary options).intervals r j) :
    GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (GeneralPaperSignedUpdatePlan.project U i+1)=
      GeneralPaperRankedCDFQuery.referenceCount k summary preparedPrefix (GeneralPaperSignedUpdatePlan.project U j+1) := by
  unfold GeneralPaperRankedCDFQuery.referenceCount
  have he : ∀ a, summary.read a<GeneralPaperSignedUpdatePlan.project U i+1 ↔
      summary.read a<GeneralPaperSignedUpdatePlan.project U j+1 := by
    intro a
    have hc := weak_project_constant U summary options a (hCodes a) r i j hI hJ
    omega
  rw [GeneralPaperCellCDFConstancy.same_members_position k summary hMono _ _ he]

theorem increment_constant {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ) (preparedPrefix : Prefix k)
    (hMono : Monotone summary.read) (hCodes : ∀ a, summary.read a<U) (q : Fin m) (hBid : options.read q<U)
    (r : Fin (prepare U summary options).count) (i j : ℕ)
    (hI : Contains (prepare U summary options).intervals r i) (hJ : Contains (prepare U summary options).intervals r j) :
    GeneralPaperSignedUpdateReference.increment k U (options.read q) summary preparedPrefix i=
      GeneralPaperSignedUpdateReference.increment k U (options.read q) summary preparedPrefix j := by
  have hc := cdf_count k U summary options preparedPrefix hMono hCodes r i j hI hJ
  have hs := sign_constant U summary options r i j hI hJ
  have hb := bid_project_constant U summary options q hBid r i j hI hJ
  unfold GeneralPaperSignedUpdateReference.increment
  simp only [hc,hs,hb]

end Blotto.GeneralPaperSignedCellConstancy
