import Blotto.GeneralPaperEpochPartition

/-! The prepared cells make strict and weak rounded CDF queries constant,
regardless of the current positive occurrence weights. Cached row-indicator
thresholds are constant by the same breakpoint argument.
-/
namespace Blotto.GeneralPaperCellCDFConstancy
open GeneralPaperRankSearch GeneralPaperSelectedRank GeneralPaperRankedCDFQuery GeneralPaperEpochCellInstructions
set_option autoImplicit false
set_option maxHeartbeats 3500000

theorem same_members_position (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (hMono : Monotone summary.read) (left right : ℕ) (hSame : ∀ r, summary.read r<left ↔ summary.read r<right) :
    (lookup k summary left).position=(lookup k summary right).position := by
  have hl := lookup_valid k summary hMono left
  have hr := lookup_valid k summary hMono right
  have hv : ValidRank summary left (lookup k summary right).position.val :=
    ⟨hr.1,fun r => (hSame r).trans (hr.2 r)⟩
  apply Fin.ext
  exact GeneralPaperRankProperties.unique summary left _ _ hl hv

theorem same_members_value (k : ℕ) (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (hMono : Monotone summary.read) (left right : ℕ) (hSame : ∀ r, summary.read r<left ↔ summary.read r<right) :
    referenceValue k summary preparedPrefix left=referenceValue k summary preparedPrefix right := by
  unfold referenceValue referenceCount
  rw [same_members_position k summary hMono left right hSame]

theorem strict_cdf_constant {m : ℕ} (k U : ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (extras : FixedArrayTable m ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (hMono : Monotone summary.read) (hCodes : ∀ r, summary.read r<U)
    (cell : Fin (GeneralPaperEpochPartition.prepare U summary extras).count) (i j : ℕ)
    (hI : Contains (GeneralPaperEpochPartition.prepare U summary extras).intervals cell i)
    (hJ : Contains (GeneralPaperEpochPartition.prepare U summary extras).intervals cell j) :
    referenceValue k summary preparedPrefix i=referenceValue k summary preparedPrefix j := by
  apply same_members_value k summary preparedPrefix hMono i j
  intro r
  exact GeneralPaperEpochPartition.strict_test_constant U summary extras r (hCodes r) cell i j hI hJ

theorem weak_cdf_constant {m : ℕ} (k U : ℕ)
    (summary : FixedArrayTable (GeneralPaperSourceParameters.prepare k).summarySize ℕ) (extras : FixedArrayTable m ℕ)
    (preparedPrefix : FixedArrayTable ((GeneralPaperSourceParameters.prepare k).summarySize+1) ℕ)
    (hMono : Monotone summary.read) (hCodes : ∀ r, summary.read r<U)
    (cell : Fin (GeneralPaperEpochPartition.prepare U summary extras).count) (i j : ℕ)
    (hI : Contains (GeneralPaperEpochPartition.prepare U summary extras).intervals cell i)
    (hJ : Contains (GeneralPaperEpochPartition.prepare U summary extras).intervals cell j) :
    referenceValue k summary preparedPrefix (i+1)=referenceValue k summary preparedPrefix (j+1) := by
  apply same_members_value k summary preparedPrefix hMono (i+1) (j+1)
  intro r
  have he := GeneralPaperEpochPartition.weak_test_constant U summary extras r (hCodes r) cell i j hI hJ
  omega

end Blotto.GeneralPaperCellCDFConstancy
