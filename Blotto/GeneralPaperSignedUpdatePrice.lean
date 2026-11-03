import Blotto.GeneralPaperSignedUpdateExecution

/-! Full signed-update rank-plan prices, with actual projected code bounds
and a whole native annotation cap derived from the executed plan.
-/
namespace Blotto.GeneralPaperSignedUpdatePrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSignedUpdateExecution
open GeneralPaperSignedTailOperands (magnitude width)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

theorem native_cap (m k : ℕ) : m*((35+k)*(12*(35+k)+34)+178)+70≤magnitude m k := by
  have hd : (35+k)*(12*(35+k)+34)+178≤128*((35+k)+1)^2 := by nlinarith only [Nat.zero_le k]
  have h := Nat.mul_le_mul_left m hd
  have hs := Nat.mul_le_mul_right (((35+k)+1)^2) (show 128*m≤1024*(m+2) by omega)
  unfold magnitude
  nlinarith only [h,hs]

theorem annotation_bound {m : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable m ℕ) :
    (run bits index price W k U summary codes).1.work≤magnitude m k := by
  rw [data]
  exact (GeneralPaperSignedUpdatePlan.prepare_work k U summary codes).trans (native_cap m k)

def profile (price : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  GeneralPaperSignedPositionsPrice.profile price W m U+GeneralPaperCDFShiftPrice.profile price W m U+
    GeneralPaperRankArrayPrice.profile price W m k U+6*price (width m k U)+128*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  GeneralPaperSignedPositionsPrice.arithmeticProfile m+GeneralPaperCDFShiftPrice.arithmeticProfile m+
    GeneralPaperRankArrayPrice.arithmeticProfile m k+134

theorem bit_work {m : ℕ} (price : ℕ → ℕ) (hMono : Monotone price) (W k U : ℕ) (summary : Summary k)
    (codes : FixedArrayTable m ℕ) (hCodes : ∀ q,codes.read q<2*U) (hSummary : ∀ r,summary.read r≤U) :
    (run true (fun w => w) price W k U summary codes).2≤profile price W m k U := by
  let ps := GeneralPaperSignedPositionsPrice.run true (fun w => w) price W U codes
  let cs := GeneralPaperCDFShiftPrice.run true (fun w => w) price W 1 ps.1.1
  let rs := GeneralPaperRankArrayExecution.prepare true (fun w => w) price W k summary cs.1.1
  have hPos := GeneralPaperSignedPositionsPrice.positions true (fun w => w) price W U codes hCodes
  have hp := GeneralPaperSignedPositionsPrice.bit_work price hMono W U codes hCodes
  have hc := GeneralPaperCDFShiftPrice.bit_work price hMono W U 1 ps.1.1 (Nat.le_refl _) hPos
  have hr := GeneralPaperRankArrayPrice.bit_work price hMono W k U summary cs.1.1
    (GeneralPaperCDFShiftPrice.cuts true (fun w => w) price W U 1 ps.1.1 (Nat.le_refl _) hPos) hSummary
  have hWhole := annotation_bound true (fun w => w) price W k U summary codes
  change ps.1.2+cs.1.2+rs.1.2+16≤magnitude m k at hWhole
  have hAdds := GeneralPaperFieldPlanCounters.triple_work price hMono (magnitude m k) (width m k U)
    ps.1.2 cs.1.2 rs.1.2 (GeneralPaperSignedTailOperands.word_bound m k U) hWhole
  exact Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hp hc) hr) hAdds) _

theorem arithmetic_work {m : ℕ} (k U : ℕ) (summary : Summary k) (codes : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U summary codes).2≤arithmeticProfile m k := by
  let ps := GeneralPaperSignedPositionsPrice.run false (fun _ => 1) (fun _ => 1) 1 U codes
  let cs := GeneralPaperCDFShiftPrice.run false (fun _ => 1) (fun _ => 1) 1 1 ps.1.1
  have hp := GeneralPaperSignedPositionsPrice.arithmetic_work U codes
  have hc := GeneralPaperCDFShiftPrice.arithmetic_work 1 ps.1.1
  have hr := GeneralPaperRankArrayPrice.arithmetic_work k summary cs.1.1
  have h := Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add hp hc) hr) 134
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 k U summary codes).2=
      ps.2+cs.2+(GeneralPaperRankArrayExecution.prepare false (fun _ => 1) (fun _ => 1) 1 k summary cs.1.1).2+134 := by
    unfold run
    dsimp only
    simp only [ps,cs,GeneralPaperFieldPlanCounters.triple,GeneralPaperNaturalPrimitivePrice.binary]
  rw [hCost]
  exact h

theorem same_data {m : ℕ} (price : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (codes : FixedArrayTable m ℕ) :
    (run true (fun w => w) price W k U summary codes).1=(run false (fun _ => 1) (fun _ => 1) 1 k U summary codes).1 := by
  rw [data,data]

end Blotto.GeneralPaperSignedUpdatePrice
