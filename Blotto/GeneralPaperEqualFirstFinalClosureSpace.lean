import Blotto.GeneralPaperEqualFirstGroupedPreparation

/-! Final budget scan, address/control construction and the exact corrected
grouped sampler return. Prior callers and every measured component-price
record remain reserved alongside the complete returned payload. -/
namespace Blotto.GeneralPaperEqualFirstFinalClosureSpace
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperPositiveSegmentCompaction (count)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def borrowed {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  let result := (GeneralPaperEqualFirstGroupedPreparation.run model W A k values v hv small budget).2
  GeneralPaperEqualFirstPowerBooleanSpace.window model W A k values v hv small budget .returned+
    GeneralPaperEqualFinalClosureCaller.workOwner A result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2

def borrowedProfile {n : ℕ} (model : RationalCostModel) (W A k m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFirstPowerBooleanSpace.profile model W A k m c width values budget+
    GeneralPaperEqualFinalClosureCaller.workProfile A
      (GeneralPaperEqualFirstGroupedPreparation.profile model W A k values (rationalWordWidth budget))

theorem borrowed_bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    borrowed model W A k values v hv small budget ≤
      borrowedProfile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small))
        (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits values budget := by
  have h0 := GeneralPaperEqualFirstPowerBooleanSpace.all_phases model W A k values v hv small budget .returned
  let result := (GeneralPaperEqualFirstGroupedPreparation.run model W A k values v hv small budget).2
  have h1 := GeneralPaperEqualFinalClosureCaller.work_owner_bound A _ result.1.1 result.1.2.1 result.1.2.2
    result.2.1 result.2.2.1 result.2.2.2
    (GeneralPaperEqualFirstGroupedPreparation.bit_work model W A k values v hv small budget)
  exact Nat.add_le_add h0 h1

def returnedPayload {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  GeneralPaperEqualRetainedStorage.footprint A (GeneralPaperEqualFirstGroupedPreparation.run model W A k values v hv small budget).1

theorem returned_payload_bound {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    returnedPayload model W A k values v hv small budget ≤
      GeneralPaperEqualNativeRetainedStorage.profile A n (k+1) (rationalWordWidth budget) :=
  GeneralPaperEqualFirstDescription.profile_bound model W A k values v hv small budget
    (GeneralPaperEqualFirstGroupedPreparation.run model W A k values v hv small budget).1 rfl rfl

def window {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualFinalClosureLifetime.Phase) : ℕ :=
  GeneralPaperEqualFinalClosureLifetime.window model A n (terminal (rounded true model W k values v hv) small).groups.length k budget
    (borrowed model W A k values v hv small budget) (returnedPayload model W A k values v hv small budget) phase

def profile {n : ℕ} (model : RationalCostModel) (W A k m c width : ℕ) (values : FixedArrayTable n ℚ) (budget : ℚ) : ℕ :=
  GeneralPaperEqualFinalClosureLifetime.profile model A n m k (rationalWordWidth budget)
    (borrowedProfile model W A k m c width values budget)
    (GeneralPaperEqualNativeRetainedStorage.profile A n (k+1) (rationalWordWidth budget))

theorem all_phases {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ)
    (phase : GeneralPaperEqualFinalClosureLifetime.Phase) :
    window model W A k values v hv small budget phase ≤
      profile model W A k (terminal (rounded true model W k values v hv) small).groups.length
        (count (lottery (rounded true model W k values v hv) small))
        (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget).rangeBits values budget := by
  have h := GeneralPaperEqualFinalClosureLifetime.all_phases model A n
    (terminal (rounded true model W k values v hv) small).groups.length k budget
    (borrowed model W A k values v hv small budget) (returnedPayload model W A k values v hv small budget) phase
  exact h.trans (GeneralPaperEqualFinalClosureLifetime.owner_mono model A n _ k _ _ _ _ _
    (borrowed_bound model W A k values v hv small budget) (returned_payload_bound model W A k values v hv small budget))

theorem source_prices {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let actual := (GeneralPaperEqualFirstGroupedPreparation.run model W A k values v hv small budget).2.2
    let b := GeneralPaperEqualFinalClosureLifetime.budgetWord model A budget
    let a := GeneralPaperEqualFinalClosureLifetime.address model A n
      (terminal (rounded true model W k values v hv) small).groups.length k budget
    (b.2,a.2,128*(A+b.1+1)) = actual := by
  simp only [GeneralPaperEqualFinalClosureLifetime.budgetWord,GeneralPaperEqualFinalClosureLifetime.address,
    GeneralPaperEqualFirstGroupedPreparation.run,GeneralPaperEqualAddressedClosure.run,FixedArrayTable.size]

end Blotto.GeneralPaperEqualFirstFinalClosureSpace
