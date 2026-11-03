import Blotto.GeneralPaperSignedTailOperands

/-! Full signed-tail preparation includes both cut arrays, both cached-rank
fills, all four native annotation additions and plan writes. The same signed
summary supplies both signs; no separate denominator/normalization is added.
-/
namespace Blotto.GeneralPaperSignedTailPrice
open GeneralPaperUnsignedCellConstancy (Summary)
open GeneralPaperSignedTailExecution
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W m k U : ℕ) : ℕ :=
  2*GeneralPaperSignedCutPrice.profile primitive W m U+
  2*GeneralPaperRankArrayPrice.profile primitive W (m+1) k (2*U)+
  8*primitive (GeneralPaperSignedTailOperands.width m k U)+128*W

def arithmeticProfile (m k : ℕ) : ℕ :=
  2*GeneralPaperSignedCutPrice.arithmeticProfile m+2*GeneralPaperRankArrayPrice.arithmeticProfile (m+1) k+136

theorem bit_work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k U : ℕ) (summary : Summary k)
    (queries : FixedArrayTable m ℕ) (hQueries : ∀ q,queries.read q≤U) (hSummary : ∀ r,summary.read r≤2*U) :
    (run true (fun w => w) primitive W k U summary queries).2≤profile primitive W m k U := by
  let pc := GeneralPaperSignedCutExecution.run true (fun w => w) primitive W U false queries
  let nc := GeneralPaperSignedCutExecution.run true (fun w => w) primitive W U true queries
  let pr := GeneralPaperRankArrayExecution.prepare true (fun w => w) primitive W k summary pc.1.1
  let nr := GeneralPaperRankArrayExecution.prepare true (fun w => w) primitive W k summary nc.1.1
  have hpc := GeneralPaperSignedCutPrice.bit_work primitive hMono W U false queries hQueries
  have hnc := GeneralPaperSignedCutPrice.bit_work primitive hMono W U true queries hQueries
  have hpr := GeneralPaperRankArrayPrice.bit_work primitive hMono W k (2*U) summary pc.1.1
    (GeneralPaperSignedCutPrice.codes true (fun w => w) primitive W U false queries hQueries) hSummary
  have hnr := GeneralPaperRankArrayPrice.bit_work primitive hMono W k (2*U) summary nc.1.1
    (GeneralPaperSignedCutPrice.codes true (fun w => w) primitive W U true queries hQueries) hSummary
  have hAdds := GeneralPaperSignedTailOperands.additions_work true (fun w => w) primitive hMono W k U summary queries
  change pc.2≤_ at hpc
  change nc.2≤_ at hnc
  change pr.2≤_ at hpr
  change nr.2≤_ at hnr
  change GeneralPaperSignedTailOperands.additions primitive pc.1.2 nc.1.2 pr.1.2 nr.1.2≤_ at hAdds
  have hCost : (run true (fun w => w) primitive W k U summary queries).2=
      pc.2+nc.2+pr.2+nr.2+GeneralPaperSignedTailOperands.additions primitive pc.1.2 nc.1.2 pr.1.2 nr.1.2+128*W := by
    unfold run
    dsimp only
    simp only [pc,nc,pr,nr,GeneralPaperSignedTailOperands.additions,Nat.add_assoc]
  have hParts := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpc hnc) hpr) hnr
  have hAll := Nat.add_le_add_right (Nat.add_le_add hParts hAdds) (128*W)
  rw [hCost]
  exact hAll.trans_eq (by unfold profile; ring)

theorem arithmetic_work {m : ℕ} (k U : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run false (fun _ => 1) (fun _ => 1) 1 k U summary queries).2≤arithmeticProfile m k := by
  let pc := GeneralPaperSignedCutExecution.run false (fun _ => 1) (fun _ => 1) 1 U false queries
  let nc := GeneralPaperSignedCutExecution.run false (fun _ => 1) (fun _ => 1) 1 U true queries
  let pr := GeneralPaperRankArrayExecution.prepare false (fun _ => 1) (fun _ => 1) 1 k summary pc.1.1
  let nr := GeneralPaperRankArrayExecution.prepare false (fun _ => 1) (fun _ => 1) 1 k summary nc.1.1
  have hpc := GeneralPaperSignedCutPrice.arithmetic_work U false queries
  have hnc := GeneralPaperSignedCutPrice.arithmetic_work U true queries
  have hpr := GeneralPaperRankArrayPrice.arithmetic_work k summary pc.1.1
  have hnr := GeneralPaperRankArrayPrice.arithmetic_work k summary nc.1.1
  change pc.2≤_ at hpc
  change nc.2≤_ at hnc
  change pr.2≤_ at hpr
  change nr.2≤_ at hnr
  have hCost : (run false (fun _ => 1) (fun _ => 1) 1 k U summary queries).2=
      pc.2+nc.2+pr.2+nr.2+136 := by
    unfold run
    dsimp only
    simp only [pc,nc,pr,nr,GeneralPaperNaturalPrimitivePrice.binary]
  have hParts := Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hpc hnc) hpr) hnr
  have hAll := Nat.add_le_add_right hParts 136
  rw [hCost]
  exact hAll.trans_eq (by unfold arithmeticProfile; ring)

theorem same_data {m : ℕ} (primitive : ℕ → ℕ) (W k U : ℕ) (summary : Summary k) (queries : FixedArrayTable m ℕ) :
    (run true (fun w => w) primitive W k U summary queries).1=
      (run false (fun _ => 1) (fun _ => 1) 1 k U summary queries).1 := by
  rw [data,data]

end Blotto.GeneralPaperSignedTailPrice
