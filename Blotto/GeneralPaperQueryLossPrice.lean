import Blotto.GeneralPaperQueryLossExecution

/-! Full primal/response query-loss preparation prices. The native work
cap is derived from the returned plan and both counter additions count.
-/
namespace Blotto.GeneralPaperQueryLossPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperQueryLossExecution
open GeneralPaperSignedTailOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem native_cap (m k : ℕ) : (4*m+2)*((35+k)*(12*(35+k)+34)+120)+192≤magnitude m k := by
  have hd : (35+k)*(12*(35+k)+34)+120≤128*((35+k)+1)^2 := by nlinarith only [Nat.zero_le k]
  have h := Nat.mul_le_mul_left (4*m+2) hd
  have hs := Nat.mul_le_mul_right (((35+k)+1)^2) (show 128*(4*m+2)≤1024*(m+2) by omega)
  unfold magnitude
  nlinarith only [h,hs]

theorem annotation_bound {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable m ℕ) : (run bits index price W k U cdfSummary tailSummary queries).1.work≤magnitude m k := by
  rw [data]
  exact (GeneralPaperQueryLossCounts.prepare_work k U cdfSummary tailSummary queries).trans (native_cap m k)

def profile (price : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  GeneralPaperCDFPairPrice.profile price W m k U+GeneralPaperSignedTailPrice.profile price W m k U+
    4*price (width m k U)+128*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  GeneralPaperCDFPairPrice.arithmeticProfile m k+GeneralPaperSignedTailPrice.arithmeticProfile m k+132

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ) (cdfSummary tailSummary : Summary k)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q<U)
    (hCDF : ∀ r,cdfSummary.read r≤U) (hTail : ∀ r,tailSummary.read r≤2*U) :
    (run true (fun w => w) price W k U cdfSummary tailSummary queries).2≤profile price W m k U := by
  let cdf := GeneralPaperCDFPairExecution.run true (fun w => w) price W k cdfSummary queries
  let tails := GeneralPaperSignedTailExecution.run true (fun w => w) price W k U tailSummary queries
  have hc := GeneralPaperCDFPairPrice.bit_work price hMono W k U cdfSummary queries hQueries hCDF
  have ht := GeneralPaperSignedTailPrice.bit_work price hMono W k U tailSummary queries (fun q => (hQueries q).le) hTail
  have hWhole := annotation_bound true (fun w => w) price W k U cdfSummary tailSummary queries
  change cdf.1.work+tails.1.work+16≤magnitude m k at hWhole
  have hAdds := GeneralPaperFieldPlanCounters.pair_work price hMono (magnitude m k) (width m k U)
    cdf.1.work tails.1.work (GeneralPaperSignedTailOperands.word_bound m k U) hWhole
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hc ht) hAdds) _

theorem arithmetic_work {m : ℕ} (k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U cdfSummary tailSummary queries).2≤arithmeticProfile m k := by
  have hc := GeneralPaperCDFPairPrice.arithmetic_work k cdfSummary queries
  have ht := GeneralPaperSignedTailPrice.arithmetic_work k U tailSummary queries
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 k U cdfSummary tailSummary queries).2=
      (GeneralPaperCDFPairExecution.run false (fun _ => 1) (fun _ => 1) 1 k cdfSummary queries).2+
      (GeneralPaperSignedTailExecution.run false (fun _ => 1) (fun _ => 1) 1 k U tailSummary queries).2+132 := by
    unfold run
    dsimp only
    simp only [GeneralPaperFieldPlanCounters.pair,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  exact Nat.add_le_add_right (Nat.add_le_add hc ht) 132

theorem same_data {m : ℕ} (price : ℕ → ℕ) (W k U : ℕ) (cdfSummary tailSummary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W k U cdfSummary tailSummary queries).1=
      (run false (fun _ => 1) (fun _ => 1) 1 k U cdfSummary tailSummary queries).1 := by
  rw [data,data]

end Blotto.GeneralPaperQueryLossPrice
