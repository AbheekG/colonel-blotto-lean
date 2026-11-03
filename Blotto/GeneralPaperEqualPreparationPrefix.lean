import Blotto.GeneralPaperEqualPackedCache

/-! Actual rounded-input, materialized-length and measured-packing path to
the exact existing sampler. The three ledger entries name only these prefix
phases: route/segment/cache/closure prices and complete lifetime are still
separate obligations. No total preparation cost is claimed here. -/
namespace Blotto.GeneralPaperEqualPreparationPrefix
open MeasureTheory
open GeneralPaperEqualNativeSampler (rounded roundDen)
open GeneralPaperEqualFiniteKernel (terminal lottery)
set_option autoImplicit false
set_option maxHeartbeats 1200000

theorem uniform_items {n : ℕ} (v : RationalFieldSelector n) (small : ∀ j, 2 * v.weight j ≤ 1) :
    (terminal v small).uniformItems = List.finRange n := by
  simp [RationalTerminalLotto.uniformItems, terminal]

def run {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    GeneralPaperEqualStoredBitSampler.Sampler (terminal (rounded bits model W k values v hv) small).partition
      (lottery (rounded bits model W k values v hv) small) × (ℕ × ℕ × ℕ) :=
  let raw := GeneralPaperValueRoundingPaperContract.run bits model W 128 k values
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 k (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 k values)
  let i := terminal r small
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = i.length j := by
    intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  let packed := GeneralPaperEqualMaterializedPacking.run i model A lengths.1 hL (List.finRange n)
    (uniform_items r small).symm
  let hPacked := GeneralPaperEqualMaterializedPacking.data i model A lengths.1 hL (List.finRange n)
    (uniform_items r small).symm
  let sampler := GeneralPaperEqualPackedCache.close r small packed.1 hPacked k budget
  (sampler, (raw.2, lengths.2, packed.2))

theorem data {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).1 =
      GeneralPaperEqualStoredBitSampler.native bits model W k values v hv small budget := by
  unfold run
  dsimp only
  exact GeneralPaperEqualPackedCache.close_eq _ _ _ _ k budget

theorem length_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.2.1 ≤
      (12 * n + 2) * model.rat (1 + 2 * GeneralPaperEqualLengthArray.height (binaryWordWidth n + k + 11)) +
      64 * (n + 1) * (A + 1) + PaperIndexedArrayConstruction.overhead id A n n := by
  let raw := (GeneralPaperValueRoundingPaperContract.run bits model W 128 k values).1
  have hd : binaryWordWidth raw.2 ≤ binaryWordWidth n + k + 11 :=
    (GeneralPaperEqualNativeSampler.roundDen_word bits model W k values v hv).trans (by omega)
  have ha : ∀ j, raw.1.read j ≤ raw.2 := by
    intro j
    have h := Finset.single_le_sum (s := Finset.univ) (f := fun j => raw.1.read j)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    exact h.trans_eq (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 k values)
  exact GeneralPaperEqualLengthArray.work model A raw.1 raw.2 (binaryWordWidth n + k + 11) (by omega) hd ha

theorem packing_work {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run bits model W A k values v hv small budget).2.2.2 ≤
      (12 * n + 12) * model.rat (3 + 2 * (binaryWordWidth n + k + 9)) + (12 * n + 24) * A +
      GeneralPaperEqualPackingExecution.unit A n * (2 * n + 4) := by
  unfold run
  dsimp only
  apply GeneralPaperEqualMaterializedPacking.work (D := roundDen bits model W k values)
  · exact GeneralPaperEqualNativeSampler.roundDen_positive bits model W k values v hv
  · norm_num [terminal]
  · have hOne : rationalWordWidth (1 : ℚ) = 3 := by decide
    change rationalWordWidth (1 : ℚ) ≤ _
    rw [hOne]
    omega
  · have h := GeneralPaperEqualNativeSampler.roundDen_word bits model W k values v hv
    omega
  · intro j
    exact (GeneralPaperEqualNativeSampler.rounded_lattice bits model W k values v hv j).int_mul 2

theorem rounding_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run true model W A k values v hv small budget).2.1 ≤
      GeneralPaperValueRoundingPaperContract.scaleBitProfile model W 128 n k +
      13 * model.rat (GeneralPaperValueRoundingInputPrice.size (GeneralPaperValueRoundingPaperContract.scale 128 n k) values) +
      512 * (n + 1) * GeneralPaperSummaryArrayExecution.arrayWord W n + 128 * W :=
  GeneralPaperValueRoundingPaperContract.bit_work model W 128 k values v hv

theorem epsilon {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1)
    (small : ∀ j, 2 * (rounded bits model W (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv).weight j ≤ 1)
    (budget : ℚ) (hB : 0 < budget) :
    let sampler := (run bits model W A (GeneralPaperDyadicAccuracy.prepare eps).exponent values v hv small budget).1
    Supported (budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ∧
      regret v.values (budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model)
        (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ≤ (eps : ℝ) := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualStoredBitSampler.native_epsilon bits model W values v hv eps hp hOne small budget hB

theorem description {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let b := rationalWordWidth budget
    let R := GeneralPaperEqualDescriptionRates.reference n k b
    GeneralPaperEqualRetainedStorage.footprint R (run bits model W A k values v hv small budget).1 ≤
      GeneralPaperEqualDescriptionRates.paperBound n k b ∧
      GeneralPaperEqualRetainedStorage.footprint R (run bits model W A k values v hv small budget).1 < 2 ^ R := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualDescriptionRates.native_paper_description bits model W k values v hv small budget

end Blotto.GeneralPaperEqualPreparationPrefix
