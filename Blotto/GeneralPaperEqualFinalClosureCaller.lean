import Blotto.GeneralPaperEqualFinalClosureLifetime

/-! Actual final native closure retains all earlier owners, the complete
fourteen-field work record and a proved complete returned-sampler payload.
Input and reference words stay fixed parameters; no space census executes. -/
namespace Blotto.GeneralPaperEqualFinalClosureCaller
open GeneralPaperEqualNativeSampler (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
open GeneralPaperEncodedScalarStorage (natBits fields)
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 4096

def workOwner (A : ℕ) (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ) : ℕ :=
  fields A [w.rounding, w.lengths, w.packing, w.routes, w.segments, w.compaction,
    w.integerProduct, w.integerCounts, w.midpointPower, width, boolean, budget, address, controls] + 128 * A

def workProfile (A F : ℕ) : ℕ := 14 * (natBits F + A) + 160 * A

theorem work_owner_bound (A F : ℕ) (w : GeneralPaperEqualCompactedPreparation.Work) (width boolean budget address controls : ℕ)
    (h : GeneralPaperEqualBitPreparationLedger.total w width boolean budget address controls ≤ F) :
    workOwner A w width boolean budget address controls ≤ workProfile A F := by
  have hFields := GeneralPaperExpressionArrayReturns.fields_mono_cap A F
    [w.rounding, w.lengths, w.packing, w.routes, w.segments, w.compaction,
      w.integerProduct, w.integerCounts, w.midpointPower, width, boolean, budget, address, controls] (by
        intro x hx
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
        unfold GeneralPaperEqualBitPreparationLedger.total at h
        rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega)
  change fields A _ ≤ 14 * (natBits F + A) + 32 * A at hFields
  unfold workOwner workProfile
  omega

def borrowed {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  let result := (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2
  GeneralPaperEqualBooleanCallerLifetime.window bits model W A exponent values v hv small budget .returned +
    workOwner A result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2

def borrowedProfile {n : ℕ} (model : RationalCostModel) (W A exponent c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualBooleanCallerLifetime.profile model W A exponent c width values budget +
    workProfile A (GeneralPaperEqualBitPreparationLedger.profile model W A exponent values (rationalWordWidth budget))

theorem borrowed_bound {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    borrowed true model W A exponent values v hv small budget ≤
      borrowedProfile model W A exponent (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  have hBoolean := GeneralPaperEqualBooleanCallerLifetime.all_phases model W A exponent values v hv small budget .returned
  let result := (GeneralPaperEqualAddressedPreparation.run true model W A exponent values v hv small budget).2
  have hWork := work_owner_bound A _ result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2
    (GeneralPaperEqualBitPreparationLedger.bit_work model W A exponent values v hv small budget)
  exact Nat.add_le_add hBoolean hWork

def returnedPayload {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualRetainedStorage.footprint A
    (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).1

theorem returned_payload_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    returnedPayload bits model W A exponent values v hv small budget ≤
      GeneralPaperEqualNativeRetainedStorage.profile A n exponent (rationalWordWidth budget) := by
  unfold returnedPayload
  rw [GeneralPaperEqualAddressedPreparation.data]
  exact GeneralPaperEqualNativeRetainedStorage.native_bound bits model W A exponent values v hv small budget

def window {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualFinalClosureLifetime.Phase) : ℕ :=
  GeneralPaperEqualFinalClosureLifetime.window model A n (terminal (rounded bits model W exponent values v hv) small).groups.length exponent budget
    (borrowed bits model W A exponent values v hv small budget)
    (returnedPayload bits model W A exponent values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A exponent m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFinalClosureLifetime.profile model A n m exponent (rationalWordWidth budget)
    (borrowedProfile model W A exponent c width values budget)
    (GeneralPaperEqualNativeRetainedStorage.profile A n exponent (rationalWordWidth budget))

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W exponent values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualFinalClosureLifetime.Phase) :
    window true model W A exponent values v hv small budget phase ≤
      profile model W A exponent (terminal (rounded true model W exponent values v hv) small).groups.length
        (count (lottery (rounded true model W exponent values v hv) small))
        (GeneralPaperEqualNativeCache.prepare true model W exponent values v hv small budget).rangeBits values budget := by
  have hKernel := GeneralPaperEqualFinalClosureLifetime.all_phases model A n
    (terminal (rounded true model W exponent values v hv) small).groups.length exponent budget
    (borrowed true model W A exponent values v hv small budget)
    (returnedPayload true model W A exponent values v hv small budget) phase
  exact hKernel.trans (GeneralPaperEqualFinalClosureLifetime.owner_mono model A n _ exponent _ _ _ _ _
    (borrowed_bound model W A exponent values v hv small budget)
    (returned_payload_bound true model W A exponent values v hv small budget))

theorem source_prices {n : ℕ} (bits : Bool) (model : RationalCostModel) (W A exponent : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded bits model W exponent values v hv).weight j ≤ 1) (budget : ℚ) :
    let actual := (GeneralPaperEqualAddressedPreparation.run bits model W A exponent values v hv small budget).2.2
    let bw := GeneralPaperEqualFinalClosureLifetime.budgetWord model A budget
    let a := GeneralPaperEqualFinalClosureLifetime.address model A n
      (terminal (rounded bits model W exponent values v hv) small).groups.length exponent budget
    (bw.2, a.2, 128 * (A + bw.1 + 1)) = actual := by
  simp only [GeneralPaperEqualFinalClosureLifetime.budgetWord, GeneralPaperEqualFinalClosureLifetime.address,
    GeneralPaperEqualAddressedPreparation.run, GeneralPaperEqualAddressedClosure.run, FixedArrayTable.size, rounded]

end Blotto.GeneralPaperEqualFinalClosureCaller
