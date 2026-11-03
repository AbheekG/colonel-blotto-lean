import Blotto.GeneralPaperPhysicalBidExecution
import Blotto.GeneralPaperRowBudgetRefinedPrice

/-! A physical response consumes the returned code row and one retained
shared shift. Each coordinate is decoded once, open bids are incremented,
and the complete rational row passes through the native hard-budget check. -/
namespace Blotto.GeneralPaperPhysicalResponseExecution
open GeneralPaperCodeAlphabet GeneralPaperResponsePhysicalHeights
open GeneralPaperPhysicalBidExecution GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def row {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) : FixedArrayTable m ℚ × ℕ :=
  PaperIndexedArrayConstruction.run (index bits) (address bits W m) (fun j =>
    let bid := GeneralPaperPhysicalBidExecution.run bits model W a delta (codes.read j)
    (bid.1,bid.2+64*address bits W m))

def run {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) (B : ℚ) : (FixedArrayTable m ℚ × Bool) × ℕ :=
  let produced := row bits model W a delta codes
  let checked := GeneralPaperRowBudgetExecution.run (primitive bits model) (index bits) (address bits W m) produced.1 B
  ((produced.1,checked.1),produced.2+checked.2+128*W)

theorem row_data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) : (row bits model W a delta codes).1=
      FixedArrayTable.ofFn (fun j => (decodedChoice a (codes.read j)).physical delta) := by
  unfold row
  rw [PaperIndexedArrayConstruction.run_data]
  congr 1
  funext j
  exact GeneralPaperPhysicalBidExecution.data bits model W a delta (codes.read j)

theorem data {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) (B : ℚ) : (run bits model W a delta codes B).1.1=
      FixedArrayTable.ofFn (fun j => (decodedChoice a (codes.read j)).physical delta) :=
  row_data bits model W a delta codes

theorem checks {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) (B : ℚ) : (run bits model W a delta codes B).1.2=true ↔
      (∀ j,0≤(decodedChoice a (codes.read j)).physical delta) ∧
      (∑ j,(decodedChoice a (codes.read j)).physical delta)≤B := by
  unfold run
  dsimp only
  rw [GeneralPaperRowBudgetExecution.correct,row_data]
  simp only [FixedArrayTable.read_ofFn]

theorem item_word {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (codes : FixedArrayTable m ℕ) (j : Fin m) :
    rationalWordWidth ((row true model W a delta codes).1.read j)≤additionWidth m qbar t a := by
  rw [row_data,FixedArrayTable.read_ofFn]
  exact bid_word m (binaryWordWidth a.C) (shiftHeight m qbar a.C) t _ (threshold_height a _) delta hd

theorem scan_prefix_word {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (codes : FixedArrayTable m ℕ)
    (count : ℕ) (hc : count≤m) :
    rationalWordWidth (GeneralPaperRowBudgetExecution.scan model.rat (index true) (address true W m)
      (row true model W a delta codes).1 count hc).1.1≤additionWidth m qbar t a := by
  rw [GeneralPaperRowBudgetExecution.scan_total,row_data]
  simp only [FixedArrayTable.read_ofFn]
  exact prefix_word (fun i : Fin count => decodedChoice a (codes.read ⟨i.val,by omega⟩)) hc
    (binaryWordWidth a.C) (shiftHeight m qbar a.C) t (fun _ => threshold_height a _) delta hd

def rowBitProfile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperSourceRowsExecution.rowBitProfile model W m a+2*m*model.rat (additionWidth m qbar t a)

theorem row_bit_work {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (codes : FixedArrayTable m ℕ)
    (hCode : ∀ j,codes.read j≤8*a.C) : (row true model W a delta codes).2≤rowBitProfile model W m qbar t a := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m)
    (GeneralPaperPhysicalBidExecution.bitProfile model W m qbar t a+64*arrayWord W m)
    (fun j => let bid := GeneralPaperPhysicalBidExecution.run true model W a delta (codes.read j)
      (bid.1,bid.2+64*arrayWord W m))
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
    (fun j => Nat.add_le_add_right (GeneralPaperPhysicalBidExecution.bit_work model W m qbar t a delta hd _ (hCode j)) _)
  apply h.trans_eq
  unfold rowBitProfile GeneralPaperSourceRowsExecution.rowBitProfile GeneralPaperPhysicalBidExecution.bitProfile
  ring

def bitProfile (model : RationalCostModel) (W m qbar t : ℕ) (a : Alphabet) : ℕ :=
  rowBitProfile model W m qbar t a+(3*m+2)*model.rat (additionWidth m qbar t a)+
    128*(m+1)*arrayWord W m+128*W

theorem bit_work {m : ℕ} (model : RationalCostModel) (W qbar t : ℕ) (a : Alphabet) (delta : ℚ)
    (hd : RationalHeight delta (shiftHeight m qbar a.C)) (codes : FixedArrayTable m ℕ)
    (hCode : ∀ j,codes.read j≤8*a.C) (B : ℚ) (hB : RationalHeight B t) :
    (run true model W a delta codes B).2≤bitProfile model W m qbar t a := by
  have hr := row_bit_work model W qbar t a delta hd codes hCode
  have hz : rationalWordWidth (0:ℚ)≤additionWidth m qbar t a := by
    rw [show rationalWordWidth (0:ℚ)=3 by decide]; unfold additionWidth word; omega
  have hb' := rationalWordWidth_of_height hB
  have hb : rationalWordWidth B≤additionWidth m qbar t a := by unfold additionWidth word; omega
  have hc := GeneralPaperRowBudgetRefinedPrice.work model (index true) (address true W m) (additionWidth m qbar t a)
    (row true model W a delta codes).1 B (item_word model W qbar t a delta hd codes)
    (scan_prefix_word model W qbar t a delta hd codes) hz hb
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
  unfold run bitProfile
  dsimp only
  simp only [primitive,index,address,ite_true] at hc ⊢
  omega

def arithmeticProfile (m : ℕ) (a : Alphabet) : ℕ :=
  m*(16777216*(a.lambda+3)+134)+44*(m+1)+(77*m+66)+128

theorem arithmetic_work {m : ℕ} (model : RationalCostModel) (a : Alphabet) (delta : ℚ)
    (codes : FixedArrayTable m ℕ) (B : ℚ) :
    (run false model 1 a delta codes B).2≤arithmeticProfile m a := by
  have hr := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (16777216*(a.lambda+3)+134)
    (fun j => let bid := GeneralPaperPhysicalBidExecution.run false model 1 a delta (codes.read j)
      (bid.1,bid.2+64)) le_rfl (fun _ _ => le_rfl) (fun j =>
        Nat.add_le_add_right (GeneralPaperPhysicalBidExecution.arithmetic_work model a delta (codes.read j)) 64)
  have hc := GeneralPaperRowBudgetExecution.arithmetic_work (row false model 1 a delta codes).1 B
  unfold run arithmeticProfile
  dsimp only
  simp only [primitive,index,address,Bool.false_eq_true,ite_false,Nat.mul_one]
  change (row false model 1 a delta codes).2+
    (GeneralPaperRowBudgetExecution.run (fun _ => 1) (fun _ => 1) 1 (row false model 1 a delta codes).1 B).2+128≤_
  have hr' : (row false model 1 a delta codes).2≤m*(16777216*(a.lambda+3)+134)+44*(m+1) := by
    simpa only [row,index,address,Bool.false_eq_true,ite_false,Nat.mul_one] using hr
  omega

theorem checks_of_physical_budget {m : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (delta : ℚ) (codes : FixedArrayTable m ℕ) (B : ℚ)
    (h : (∀ j,0≤(decodedChoice a (codes.read j)).physical delta) ∧
      (∑ j,(decodedChoice a (codes.read j)).physical delta)≤B) : (run bits model W a delta codes B).1.2=true :=
  (checks bits model W a delta codes B).2 h

end Blotto.GeneralPaperPhysicalResponseExecution
