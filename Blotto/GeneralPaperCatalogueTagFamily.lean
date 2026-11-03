import Blotto.GeneralPaperCatalogueTagValue

/-! Native tag arrays from retained fraction/open arrays. Each fraction is
evaluated once, with both table reads, two casts, division/result write and
both indexed array loops charged. No tag reconstruction pass follows.
-/
namespace Blotto.GeneralPaperCatalogueTagFamily
open GeneralPaperCodeAlphabet
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 6000000
set_option maxRecDepth 4096

def entry {K : ℕ} (price : ℕ → ℕ) (W : ℕ) (thresholds : FixedArrayTable K Farey.Fraction)
    (opened : FixedArrayTable K Bool) (i : Fin K) : GeneralPaperResponseTag.Tag × ℕ :=
  let found := GeneralPaperCatalogueTagValue.run price W (thresholds.read i) (opened.read i)
  (found.1,found.2+32*W)

def row {K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (thresholds : FixedArrayTable K Farey.Fraction)
    (opened : FixedArrayTable K Bool) : FixedArrayTable K GeneralPaperResponseTag.Tag × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W K else W) (entry price W thresholds opened)

def element {m K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (data : GeneralPaperCatalogueArrays.Arrays m K) (j : Fin m) : FixedArrayTable K GeneralPaperResponseTag.Tag × ℕ :=
  let found := row bits index price W (data.thresholds.read j) (data.opened.read j)
  (found.1,found.2+32*W)

def run {m K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (data : GeneralPaperCatalogueArrays.Arrays m K) : FixedArrayTable m (FixedArrayTable K GeneralPaperResponseTag.Tag) × ℕ :=
  PaperIndexedArrayConstruction.run index (if bits then arrayWord W m else W) (element bits index price W data)

def rowProfile (model : RationalCostModel) (W K lambda : ℕ) : ℕ :=
  K*(4*model.rat (GeneralPaperDecoderControls.operandWidth lambda)+96*W)+44*(K+1)*arrayWord W K

def profile (model : RationalCostModel) (W m K lambda : ℕ) : ℕ :=
  m*(rowProfile model W K lambda+32*W)+44*(m+1)*arrayWord W m

def rowArithmeticProfile (K : ℕ) : ℕ := K*100+44*(K+1)

def arithmeticProfile (m K : ℕ) : ℕ := m*(rowArithmeticProfile K+32)+44*(m+1)

theorem row_data {K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (thresholds : FixedArrayTable K Farey.Fraction)
    (opened : FixedArrayTable K Bool) :
    (row bits index price W thresholds opened).1=FixedArrayTable.ofFn (fun i =>
      (⟨(thresholds.read i).value,opened.read i⟩:GeneralPaperResponseTag.Tag)) :=
  PaperIndexedArrayConstruction.run_data _ _ _

theorem data {m K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ) (values : GeneralPaperCatalogueArrays.Arrays m K) :
    (run bits index price W values).1=GeneralPaperCatalogueArrays.tags values := by
  rw [run,PaperIndexedArrayConstruction.run_data]
  unfold GeneralPaperCatalogueArrays.tags GeneralPaperNativeRowBudget.tags
  congr 1
  funext j
  exact row_data bits index price W (values.thresholds.read j) (values.opened.read j)

theorem row_bit_work {K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool)
    (hBounds : ∀ i,(thresholds.read i).num≤a.C ∧ (thresholds.read i).den≤a.C) :
    (row true (fun w => w) model.rat W thresholds opened).2≤rowProfile model W K a.lambda := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W K)
    (4*model.rat (GeneralPaperDecoderControls.operandWidth a.lambda)+96*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W K) (GeneralPaperSummaryArrayControls.array_index W K)
  intro i
  have h := GeneralPaperCatalogueTagValue.bit_work model W a (thresholds.read i) (hBounds i).1 (hBounds i).2 (opened.read i)
  exact (Nat.add_le_add_right h (32*W)).trans_eq (by omega)

theorem bit_work {m K : ℕ} (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (values : GeneralPaperCatalogueArrays.Arrays m K)
    (hBounds : ∀ j i,((values.thresholds.read j).read i).num≤a.C ∧ ((values.thresholds.read j).read i).den≤a.C) :
    (run true (fun w => w) model.rat W values).2≤profile model W m K a.lambda := by
  apply GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W m) (rowProfile model W K a.lambda+32*W) _
    (GeneralPaperSummaryArrayControls.array_word_positive W m) (GeneralPaperSummaryArrayControls.array_index W m)
  intro j
  exact Nat.add_le_add_right (row_bit_work model W a (values.thresholds.read j) (values.opened.read j) (hBounds j)) _

theorem row_arithmetic_work {K : ℕ} (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool) :
    (row false (fun _ => 1) (fun _ => 1) 1 thresholds opened).2≤rowArithmeticProfile K := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 100
    (entry (fun _ => 1) 1 thresholds opened) (Nat.le_refl _) (fun _ _ => Nat.le_refl _) (fun _ => Nat.le_refl _)
  simpa only [row,Bool.false_eq_true,ite_false,rowArithmeticProfile,Nat.mul_one] using h

theorem arithmetic_work {m K : ℕ} (values : GeneralPaperCatalogueArrays.Arrays m K) :
    (run false (fun _ => 1) (fun _ => 1) 1 values).2≤arithmeticProfile m K := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1 (rowArithmeticProfile K+32)
    (element false (fun _ => 1) (fun _ => 1) 1 values) (Nat.le_refl _) (fun _ _ => Nat.le_refl _)
    (fun j => Nat.add_le_add_right (row_arithmetic_work (values.thresholds.read j) (values.opened.read j)) 32)
  simpa only [run,Bool.false_eq_true,ite_false,arithmeticProfile,Nat.mul_one] using h

theorem every_row_prefix {K : ℕ} (index price : ℕ → ℕ) (W A : ℕ)
    (thresholds : FixedArrayTable K Farey.Fraction) (opened : FixedArrayTable K Bool) (count : ℕ) (hCount : count≤K) :
    (PaperIndexedArrayConstruction.fill index A (entry price W thresholds opened) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

theorem every_field_prefix {m K : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W A : ℕ)
    (values : GeneralPaperCatalogueArrays.Arrays m K) (count : ℕ) (hCount : count≤m) :
    (PaperIndexedArrayConstruction.fill index A (element bits index price W values) count hCount).1.size=count := by
  rw [PaperIndexedArrayConstruction.fill_data,Array.size_ofFn]

end Blotto.GeneralPaperCatalogueTagFamily
