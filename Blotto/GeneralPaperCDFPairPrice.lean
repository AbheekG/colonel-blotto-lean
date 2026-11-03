import Blotto.GeneralPaperCDFPairExecution

/-! Complete strict/weak CDF preparation with execution-derived counters
and code caps. Native query counts agree for every current prefix array.
-/
namespace Blotto.GeneralPaperCDFPairPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperCDFPairExecution
open GeneralPaperSignedTailOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem native_cap (m k : ℕ) : 2*m*((35+k)*(12*(35+k)+34)+120)+88≤magnitude m k := by
  have h := Nat.mul_le_mul_right ((35+k)*(12*(35+k)+34)+120) (show 2*m≤2*(m+1) by omega)
  exact (Nat.add_le_add_right h 88).trans (GeneralPaperSignedTailOperands.native_cap m k)

theorem annotation_bound {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run bits index price W k summary queries).1.work≤magnitude m k := by
  rw [data]
  exact (GeneralPaperCDFPairPlan.prepare_work k summary queries).trans (native_cap m k)

def profile (price : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  2*GeneralPaperCDFShiftPrice.profile price W m U+2*GeneralPaperRankArrayPrice.profile price W m k U+
    8*price (width m k U)+128*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  2*GeneralPaperCDFShiftPrice.arithmeticProfile m+2*GeneralPaperRankArrayPrice.arithmeticProfile m k+136

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q<U) (hSummary : ∀ r,summary.read r≤U) :
    (run true (fun w => w) price W k summary queries).2≤profile price W m k U := by
  let lc := GeneralPaperCDFShiftPrice.run true (fun w => w) price W 0 queries
  let uc := GeneralPaperCDFShiftPrice.run true (fun w => w) price W 1 queries
  let lr := GeneralPaperRankArrayExecution.prepare true (fun w => w) price W k summary lc.1.1
  let ur := GeneralPaperRankArrayExecution.prepare true (fun w => w) price W k summary uc.1.1
  have hlc := GeneralPaperCDFShiftPrice.bit_work price hMono W U 0 queries (by omega) hQueries
  have huc := GeneralPaperCDFShiftPrice.bit_work price hMono W U 1 queries (Nat.le_refl _) hQueries
  have hlr := GeneralPaperRankArrayPrice.bit_work price hMono W k U summary lc.1.1
    (GeneralPaperCDFShiftPrice.cuts true (fun w => w) price W U 0 queries (by omega) hQueries) hSummary
  have hur := GeneralPaperRankArrayPrice.bit_work price hMono W k U summary uc.1.1
    (GeneralPaperCDFShiftPrice.cuts true (fun w => w) price W U 1 queries (Nat.le_refl _) hQueries) hSummary
  have hWhole := annotation_bound true (fun w => w) price W k summary queries
  change lc.1.2+uc.1.2+lr.1.2+ur.1.2+16≤magnitude m k at hWhole
  have hAdds := GeneralPaperFieldPlanCounters.four_work price hMono (magnitude m k) (width m k U)
    lc.1.2 uc.1.2 lr.1.2 ur.1.2 (GeneralPaperSignedTailOperands.word_bound m k U) hWhole
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hlc huc) hlr) hur) hAdds) (128*W)
  exact h.trans_eq (by unfold profile; ring)

theorem arithmetic_work {m : ℕ} (k : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 k summary queries).2≤arithmeticProfile m k := by
  let lc := GeneralPaperCDFShiftPrice.run false (fun _ => 1) (fun _ => 1) 1 0 queries
  let uc := GeneralPaperCDFShiftPrice.run false (fun _ => 1) (fun _ => 1) 1 1 queries
  have hlc := GeneralPaperCDFShiftPrice.arithmetic_work 0 queries
  have huc := GeneralPaperCDFShiftPrice.arithmetic_work 1 queries
  have hlr := GeneralPaperRankArrayPrice.arithmetic_work k summary lc.1.1
  have hur := GeneralPaperRankArrayPrice.arithmetic_work k summary uc.1.1
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hlc huc) hlr) hur) 136
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 k summary queries).2=
      lc.2+uc.2+(GeneralPaperRankArrayExecution.prepare false (fun _ => 1) (fun _ => 1) 1 k summary lc.1.1).2+
      (GeneralPaperRankArrayExecution.prepare false (fun _ => 1) (fun _ => 1) 1 k summary uc.1.1).2+136 := by
    unfold run
    dsimp only
    simp only [lc,uc,GeneralPaperSignedTailOperands.additions,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  exact h.trans_eq (by unfold arithmeticProfile; ring)

theorem same_data {m : ℕ} (price : ℕ → ℕ) (W k : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W k summary queries).1=(run false (fun _ => 1) (fun _ => 1) 1 k summary queries).1 := by
  rw [data,data]

end Blotto.GeneralPaperCDFPairPrice
