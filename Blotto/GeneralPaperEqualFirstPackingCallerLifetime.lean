import Blotto.GeneralPaperEqualFirstSourceOwnership

/-! The actual native materialized packing source, its proved original/
rounded/length caller owners and complete returned group-array payload.
A linear shared label pool and local work charges supply the scan reserve;
the exact measured packing price is covered by the fourteen-field ledger. -/
namespace Blotto.GeneralPaperEqualFirstPackingCallerLifetime
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal)
open GeneralPaperEqualFirstInitialPrefixLifetime (raw)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def lengths {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) :=
  GeneralPaperEqualLengthArray.run model A (raw model W exponent values).1.1 (raw model W exponent values).1.2

theorem length_correct {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (j : Fin n) :
    (lengths model W A exponent values).1.read j = (terminal (rounded true model W exponent values v hv) small).length j := by
  unfold lengths
  rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
  rfl

def packing {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) :=
  GeneralPaperEqualMaterializedPacking.run (terminal (rounded true model W exponent values v hv) small) model A
    (lengths model W A exponent values).1 (length_correct model W A exponent values v hv small) (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items _ small).symm

theorem work_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W exponent values v hv).weight j ≤ 1) (_budget : ℚ) :
    (packing model W A exponent values v hv small).2 ≤
      GeneralPaperEqualFirstPrefixRates.packingBound model A n exponent :=
  GeneralPaperEqualFirstPrefixRates.packing model W A exponent values v hv small
    (lengths model W A exponent values).1 (length_correct model W A exponent values v hv small)

def borrowed {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstInitialPrefixLifetime.window model W A exponent values budget .returned

def returnedPayload {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) : ℕ :=
  GeneralPaperEqualPackedOwner.footprint A (packing model W A exponent values v hv small).1

theorem returned_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) :
    returnedPayload model W A exponent values v hv small ≤ GeneralPaperEqualPackedOwner.profile A n 3 (binaryWordWidth n + exponent + 10) :=
  GeneralPaperEqualFirstSourceOwnership.packed true model W A exponent values v hv small
    (packing model W A exponent values v hv small).1 (lengths model W A exponent values).1 (length_correct model W A exponent values v hv small)

def window {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperPackingLifetime.window (lengths model W A exponent values).1 model A
    (terminal (rounded true model W exponent values v hv) small).B (List.finRange n)
    (borrowed model W A exponent values budget) (returnedPayload model W A exponent values v hv small)

def profile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperPackingLifetime.profile A n
    (GeneralPaperEqualFirstPrefixRates.packingBound model A n exponent)
    (GeneralPaperEqualFirstInitialPrefixLifetime.profile model W A exponent values budget)
    (GeneralPaperEqualPackedOwner.profile A n 3 (binaryWordWidth n + exponent + 10))

theorem actual {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    window model W A exponent values v hv small budget ≤ profile model W A exponent values budget := by
  have hWork := work_bound model W A exponent values v hv small budget
  change (GeneralPaperEqualPackingExecution.run model A (lengths model W A exponent values).1
    (terminal (rounded true model W exponent values v hv) small).B (List.finRange n)).2 ≤ _ at hWork
  have hKernel := GeneralPaperPackingLifetime.bounded (lengths model W A exponent values).1 model A _
    (terminal (rounded true model W exponent values v hv) small).B (List.finRange n)
    (borrowed model W A exponent values budget) (returnedPayload model W A exponent values v hv small)
    (List.length_finRange (n := n)).le hWork
  exact hKernel.trans (GeneralPaperPackingLifetime.owner_work_mono A n _ _ _ _ _ _ le_rfl
    (GeneralPaperEqualFirstInitialPrefixLifetime.all_phases model W A exponent values v hv budget .returned)
    (returned_bound model W A exponent values v hv small))

end Blotto.GeneralPaperEqualFirstPackingCallerLifetime
