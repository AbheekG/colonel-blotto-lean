import Blotto.GeneralPaperEqualAddressedPreparation

/-! Sum every measured grouped equal-budget bit-preparation phase, including
original input rounding, all cache work and final budget/address/control.
This explicit ledger still takes the preparation reference word; its sharp
paper rate and full lifetime/common-reference calibration remain open. -/
namespace Blotto.GeneralPaperEqualBitPreparationLedger
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 1400000

def total (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ) : ℕ :=
  w.rounding + w.lengths + w.packing + w.routes + w.segments + w.compaction +
    (w.integerProduct + w.integerCounts) + w.midpointPower + width + boolean + (budget + address + controls)

def profile {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) (b : ℕ) : ℕ :=
  let L := 3670016 * (binaryWordWidth n + k + 10) + 1
  (GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 128 n k +
      13 * model.rat (GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 128 n k) values) +
      512 * (n + 1) * GeneralPaperSummaryArrayExecution.arrayWord W n + 128 * W) +
    ((12 * n + 2) * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height (binaryWordWidth n + k + 11)) +
      64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n) +
    ((12 * n + 12) * model.rat (3 + 2 * (binaryWordWidth n + k + 9)) + (12 * n + 24) * A +
      GeneralPaperEqualPackingExecution.unit A n * (2 * n + 4)) +
    (64 * (n + 1) * model.rat (4 * (binaryWordWidth n + k + 9) + 3) +
      4096 * (n + 1) * (A + binaryWordWidth (n + 1) + 1)) +
    (4294967296 * (model.rat (4194304 * (binaryWordWidth n + k + 10)) + A + 1)) +
    (1048576 * (model.rat (1048576 * (binaryWordWidth n + k + 10) + 1) + A + 1)) +
    (1048576 * (model.rat (3670016 * (binaryWordWidth n + k + 10) + 2) + A + 1)) +
    (64 * (binaryWordWidth (k + 5) + 1) * (A + model.rat (GeneralPaperNatPowerOperands.width 2 (k + 5))) + 128 * A + 128) +
    (128 * (L + 1) * (A + model.rat (L + 6) + 1)) +
    (8192 * (L + 1) * (model.rat (L + 8) + A + 1)) +
    (4096 * (b + A + model.rat (8 * (binaryWordWidth n + binaryWordWidth k + binaryWordWidth b + 66)) + 1))

theorem bit_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := (GeneralPaperEqualAddressedPreparation.run true model W A k values v hv small budget).2
    total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2 ≤
      profile model W A k values (rationalWordWidth budget) := by
  dsimp only
  have h0 := GeneralPaperEqualPreparationPrefix.rounding_work model W A k values v hv small budget
  have h1 := GeneralPaperEqualPreparationPrefix.length_work true model W A k values v hv small budget
  have h2 := GeneralPaperEqualPreparationPrefix.packing_work true model W A k values v hv small budget
  have h3 := GeneralPaperEqualRoutedPreparation.route_work true model W A k values v hv small budget
  have h4 := GeneralPaperEqualCompactedPreparation.segment_work true model W A k values v hv small budget
  have h5 := GeneralPaperEqualCompactedPreparation.compaction_work true model W A k values v hv small budget
  have h6 := GeneralPaperEqualCompactedPreparation.integer_work true model W A k values v hv small budget
  have h7 := GeneralPaperEqualCompactedPreparation.power_work true model W A k values v hv small budget
  have h8 := GeneralPaperEqualClosedPreparation.width_work true model W A k values v hv small budget
  have h9 := GeneralPaperEqualClosedPreparation.boolean_headline true model W A k values v hv small budget
  have h10 := GeneralPaperEqualAddressedPreparation.closure_work true model W A k values v hv small budget
  unfold total profile
  dsimp only
  exact (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.add_le_add h0 h1) h2) h3) h4) h5) h6) h7) h8) h9) h10)

end Blotto.GeneralPaperEqualBitPreparationLedger
