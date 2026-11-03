import Blotto.GeneralPaperEqualSegmentCallerOwners

/-! The segment-phase window is instantiated at the actual measured native
preparation prefix. Its borrowed owner is now proved, including original
input/budget, short rounded arrays, packed groups, routes and fixed code.
This observer is erased; it does not add a preparation replay or traversal. -/
namespace Blotto.GeneralPaperEqualSegmentCallerLifetime
open GeneralPaperEqualNativeSampler (rounded roundDen)
open GeneralPaperEqualFiniteKernel (terminal)
set_option autoImplicit false
set_option maxHeartbeats 1800000

def borrowed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  let raw := GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 exponent (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)
  let i := terminal r small
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = i.length j := by
    intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  let packed := GeneralPaperEqualMaterializedPacking.run i model A lengths.1 hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items r small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths.1 hL
  GeneralPaperEqualSegmentCallerOwners.footprint A W exponent values raw.1 lengths.1 packed.1 routes.1 budget
    raw.2 lengths.2 packed.2 routes.2

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (terminal (rounded bits model W exponent values v hv) small).groups.length) : ℕ :=
  let raw := GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 exponent (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)
  let i := terminal r small
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = i.length j := by
    intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  let packed := GeneralPaperEqualMaterializedPacking.run i model A lengths.1 hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items r small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths.1 hL
  GeneralPaperNativeSegmentFactoryLifetime.window (packed.1.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction r small))
    packed.1.groups.data.size i.groups_count model A
    (borrowed bits model W A exponent values v hv small budget) phase

def segmentReturn {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (_budget : ℚ) :=
  let raw := GeneralPaperValueRoundingPaperContract.run bits model W 128 exponent values
  let hp := GeneralPaperValueRoundingPaperContract.positivity bits model W 128 exponent (by decide) values v hv
  let r := GeneralPaperNativeRationalValues.selector raw.1.2 hp.1 raw.1.1 hp.2
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 128 exponent values)
  let i := terminal r small
  let lengths := GeneralPaperEqualLengthArray.run model A raw.1.1 raw.1.2
  let hL : ∀ j, lengths.1.read j = i.length j := by
    intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl
  let packed := GeneralPaperEqualMaterializedPacking.run i model A lengths.1 hL (List.finRange n)
    (GeneralPaperEqualPreparationPrefix.uniform_items r small).symm
  let routes := GeneralPaperEqualRouteConstruction.prepare packed.1 model A lengths.1 hL
  GeneralPaperEqualNativeSegmentPreparation.prepared r small packed.1 model A

theorem source_price {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    (segmentReturn bits model W A exponent values v hv small budget).2 =
      (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2.1.1.segments := rfl

theorem prefix_price (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ) :
    w.rounding + w.lengths + w.packing + w.routes ≤
      GeneralPaperEqualBitPreparationLedger.total w width boolean budget address controls := by
  unfold GeneralPaperEqualBitPreparationLedger.total
  omega

def ownerProfile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualSegmentCallerOwners.profile A W n exponent (GeneralPaperValueRoundingInputPrice.inputSize values)
    (rationalWordWidth budget) (roundDen true model W exponent values)
    (GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget))

theorem owner_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    borrowed true model W A exponent values v hv small budget ≤ ownerProfile model W A exponent values budget := by
  let result := (GeneralPaperEqualAddressedPreparation.run true model W A exponent values v hv small budget).2
  have hCost := GeneralPaperEqualBitPreparationLedger.bit_work model W A exponent values v hv small budget
  have hPrefix := (prefix_price result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2).trans hCost
  unfold borrowed ownerProfile
  dsimp only
  apply GeneralPaperEqualSegmentCallerOwners.native true model W A exponent values v hv small _ _ _ _ budget
  · exact hPrefix
  · intro j
    rw [GeneralPaperEqualLengthArray.data, FixedArrayTable.read_ofFn]
    rfl

theorem factory_borrowed_mono (model : RationalCostModel) (A s B C : ℕ) (h : B ≤ C) :
    GeneralPaperNativeSegmentFactoryLifetime.profile model A s B ≤ GeneralPaperNativeSegmentFactoryLifetime.profile model A s C := by
  unfold GeneralPaperNativeSegmentFactoryLifetime.profile GeneralPaperFixedSegmentFactoryLifetime.profile
    GeneralPaperFixedEnvironmentLifetime.profile GeneralPaperSegmentCompilerLifetime.profile
    GeneralPaperExpressionRowLifetime.profile GeneralPaperExpressionMatrixLifetime.activeProfile
    GeneralPaperExpressionArrayReturns.rowProfile GeneralPaperExpressionArrayReturns.matrixProfile
    GeneralPaperSegmentCompilerStorage.assemblyProfile
  omega

def profile {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperNativeSegmentFactoryLifetime.profile model A (GeneralPaperEqualNativeSampler.fieldHeight n exponent)
    (ownerProfile model W A exponent values budget)

theorem actual {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperNativeSegmentFactoryLifetime.Phase (terminal (rounded true model W exponent values v hv) small).groups.length) :
    window true model W A exponent values v hv small budget phase ≤ profile model W A exponent values budget := by
  have hBorrowed := owner_bound model W A exponent values v hv small budget
  have h : ∀ packed : RationalTerminalPacking (terminal (rounded true model W exponent values v hv) small),
      GeneralPaperNativeSegmentFactoryLifetime.window (packed.uniformSpec (GeneralPaperEqualFiniteKernel.no_fraction _ small))
        packed.groups.data.size (terminal _ small).groups_count model A
        (borrowed true model W A exponent values v hv small budget) phase ≤ profile model W A exponent values budget := by
    intro packed
    exact (GeneralPaperNativeSegmentFactoryLifetime.native true model W A exponent values v hv small packed _ phase).trans
      (factory_borrowed_mono model A _ _ _ hBorrowed)
  unfold window
  dsimp only
  apply h

end Blotto.GeneralPaperEqualSegmentCallerLifetime
