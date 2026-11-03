import Blotto.GeneralPaperCellPlanExecution

/-! Complete cell-plan prices with no supplied count/query/phase oracle.
Actual partition counts lift representative and rank profiles; returned
representatives supply every strict query bound in both native plan types.
-/
namespace Blotto.GeneralPaperCellPlanPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCellPlanExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def unsignedProfile (price : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let count := 3*s+m+1
  GeneralPaperUnsignedCellPartitionPrice.profile price W s m U+
    (GeneralPaperCellRepresentativePrice.profile price W count+GeneralPaperQueryLossPrice.profile price W count k U+128*W)+64*W

def signedProfile (price : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let count := 4*s+2*m+2
  GeneralPaperSignedCellPartitionPrice.profile price W s m U+
    (GeneralPaperCellRepresentativePrice.profile price W count+GeneralPaperSignedUpdatePrice.profile price W count k U+128*W)+64*W

def unsignedArithmeticProfile (m k : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let count := 3*s+m+1
  GeneralPaperUnsignedCellPartitionPrice.arithmeticProfile s m+
    (GeneralPaperCellRepresentativePrice.arithmeticProfile count+GeneralPaperQueryLossPrice.arithmeticProfile count k+128)+64

def signedArithmeticProfile (m k : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  let count := 4*s+2*m+2
  GeneralPaperSignedCellPartitionPrice.arithmeticProfile s m+
    (GeneralPaperCellRepresentativePrice.arithmeticProfile count+GeneralPaperSignedUpdatePrice.arithmeticProfile count k+128)+64

theorem unsigned_bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ)
    (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ r,cdfSummary.read r<U) (hSigned : ∀ r,signedSummary.read r<2*U) (hOptions : ∀ r,options.read r<U) :
    (unsigned true (fun w => w) price W k U cdfSummary signedSummary options).2≤unsignedProfile price W m k U := by
  let part := GeneralPaperUnsignedCellPartitionPrice.run true (fun w => w) price W U cdfSummary signedSummary options
  let reps := GeneralPaperCellRepresentativePrice.run true (fun w => w) price W part.1.intervals
  let ranks := GeneralPaperQueryLossExecution.run true (fun w => w) price W k U cdfSummary signedSummary reps.1.1
  have hc := GeneralPaperUnsignedCellPartitionPrice.count_bound true (fun w => w) price W U cdfSummary signedSummary options
  have hp := GeneralPaperUnsignedCellPartitionPrice.bit_work price hMono W U cdfSummary signedSummary options hCDF hSigned hOptions
  have hr := (GeneralPaperCellRepresentativePrice.bit_work price hMono W part.1.intervals).trans
    (GeneralPaperCellRepresentativePrice.profile_mono price hMono W _ _ hc)
  have hq := GeneralPaperQueryLossPrice.bit_work price hMono W k U cdfSummary signedSummary reps.1.1
    (GeneralPaperUnsignedCellPartitionPrice.representative_codes true (fun w => w) price W U cdfSummary signedSummary options)
    (fun r => (hCDF r).le) (fun r => (hSigned r).le)
  have hRank := hq.trans (GeneralPaperPlanProfileMonotonicity.loss_profile price hMono W _ _ k U hc)
  have hFinish := Nat.add_le_add_right (Nat.add_le_add hr hRank) (128*W)
  exact Nat.add_le_add_right (Nat.add_le_add hp hFinish) _

theorem signed_bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ)
    (summary : Summary k) (options : FixedArrayTable m ℕ) (hSummary : ∀ r,summary.read r<U) (hOptions : ∀ r,options.read r<U) :
    (signed true (fun w => w) price W k U summary options).2≤signedProfile price W m k U := by
  let part := GeneralPaperSignedCellPartitionPrice.run true (fun w => w) price W U summary options
  let reps := GeneralPaperCellRepresentativePrice.run true (fun w => w) price W part.1.intervals
  have hc := GeneralPaperSignedCellPartitionPrice.count_bound true (fun w => w) price W U summary options
  have hp := GeneralPaperSignedCellPartitionPrice.bit_work price hMono W U summary options hSummary hOptions
  have hr := (GeneralPaperCellRepresentativePrice.bit_work price hMono W part.1.intervals).trans
    (GeneralPaperCellRepresentativePrice.profile_mono price hMono W _ _ hc)
  have hq := GeneralPaperSignedUpdatePrice.bit_work price hMono W k U summary reps.1.1
    (GeneralPaperSignedCellPartitionPrice.representative_codes true (fun w => w) price W U summary options) (fun r => (hSummary r).le)
  have hRank := hq.trans (GeneralPaperPlanProfileMonotonicity.signed_profile price hMono W _ _ k U hc)
  have hFinish := Nat.add_le_add_right (Nat.add_le_add hr hRank) (128*W)
  exact Nat.add_le_add_right (Nat.add_le_add hp hFinish) _

theorem unsigned_arithmetic_work {m : ℕ} (k U : ℕ) (cdfSummary signedSummary : Summary k) (options : FixedArrayTable m ℕ)
    (hCDF : ∀ r,cdfSummary.read r<U) (hSigned : ∀ r,signedSummary.read r<2*U) (hOptions : ∀ r,options.read r<U) :
    (unsigned false (fun _ => 1) (fun _ => 1) 1 k U cdfSummary signedSummary options).2≤unsignedArithmeticProfile m k := by
  let part := GeneralPaperUnsignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 U cdfSummary signedSummary options
  let reps := GeneralPaperCellRepresentativePrice.run false (fun _ => 1) (fun _ => 1) 1 part.1.intervals
  have hc := GeneralPaperUnsignedCellPartitionPrice.count_bound false (fun _ => 1) (fun _ => 1) 1 U cdfSummary signedSummary options
  have hp := GeneralPaperUnsignedCellPartitionPrice.arithmetic_work U cdfSummary signedSummary options hCDF hSigned hOptions
  have hr := (GeneralPaperCellRepresentativePrice.arithmetic_work part.1.intervals).trans
    (GeneralPaperCellRepresentativePrice.arithmetic_profile_mono _ _ hc)
  have hq := GeneralPaperQueryLossPrice.arithmetic_work k U cdfSummary signedSummary reps.1.1
  have hRank := hq.trans (GeneralPaperPlanProfileMonotonicity.loss_arithmetic _ _ k hc)
  exact Nat.add_le_add_right (Nat.add_le_add hp (Nat.add_le_add_right (Nat.add_le_add hr hRank) 128)) 64

theorem signed_arithmetic_work {m : ℕ} (k U : ℕ) (summary : Summary k) (options : FixedArrayTable m ℕ)
    (hSummary : ∀ r,summary.read r<U) (hOptions : ∀ r,options.read r<U) :
    (signed false (fun _ => 1) (fun _ => 1) 1 k U summary options).2≤signedArithmeticProfile m k := by
  let part := GeneralPaperSignedCellPartitionPrice.run false (fun _ => 1) (fun _ => 1) 1 U summary options
  let reps := GeneralPaperCellRepresentativePrice.run false (fun _ => 1) (fun _ => 1) 1 part.1.intervals
  have hc := GeneralPaperSignedCellPartitionPrice.count_bound false (fun _ => 1) (fun _ => 1) 1 U summary options
  have hp := GeneralPaperSignedCellPartitionPrice.arithmetic_work U summary options hSummary hOptions
  have hr := (GeneralPaperCellRepresentativePrice.arithmetic_work part.1.intervals).trans
    (GeneralPaperCellRepresentativePrice.arithmetic_profile_mono _ _ hc)
  have hq := GeneralPaperSignedUpdatePrice.arithmetic_work k U summary reps.1.1
  have hRank := hq.trans (GeneralPaperPlanProfileMonotonicity.signed_arithmetic _ _ k hc)
  exact Nat.add_le_add_right (Nat.add_le_add hp (Nat.add_le_add_right (Nat.add_le_add hr hRank) 128)) 64

end Blotto.GeneralPaperCellPlanPrice
