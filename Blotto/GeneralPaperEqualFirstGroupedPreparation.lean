import Blotto.GeneralPaperEqualFirstPowerBooleanSpace

/-! Exact grouped source projections and measured component prices. This
observer exposes the same single continuation used by the corrected branch;
it does not add a replay, source traversal or runtime price certificate. -/
namespace Blotto.GeneralPaperEqualFirstGroupedPreparation
open GeneralPaperEqualFirstNativeFacts (rounded)
open GeneralPaperEqualFiniteKernel (terminal)
open GeneralPaperEqualFirstInitialPrefixLifetime (raw)
open GeneralPaperEqualFirstPackingCallerLifetime (lengths packing length_correct)
open GeneralPaperEqualFirstRouteCallerLifetime (routes)
open GeneralPaperEqualFirstSegmentCallerSpace (full)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 8192

def run {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :=
  let p := packing model W A k values v hv small
  let r := routes model W A k values v hv small
  let f := full model W A k values v hv small
  let cache := GeneralPaperEqualAddressedClosure.run r.1 f.1 p.1.groups.data.size p.1.groups.size model A k budget
  let work : GeneralPaperEqualCompactedPreparation.Work :=
    ⟨(raw model W k values).2,(lengths model W A k values).2,p.2,r.2,f.2,
      cache.2.1.compaction,cache.2.1.integerProduct,cache.2.1.integerCounts,cache.2.1.midpointPower⟩
  (cache.1,((work,cache.2.1.rejectionWidth,cache.2.1.booleanCache),cache.2.2))

theorem data {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run model W A k values v hv small budget).1 = GeneralPaperEqualStoredBitSampler.prepare
      (GeneralPaperEqualFirstNativeCache.prepare true model W k values v hv small budget) k rfl :=
  GeneralPaperEqualAddressedClosure.data (routes model W A k values v hv small).1
    (full model W A k values v hv small).1 (packing model W A k values v hv small).1.groups.data.size
    (packing model W A k values v hv small).1.groups.size model A k budget

theorem same_return {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run model W A k values v hv small budget).1 =
      (GeneralPaperEqualBitContinuation.run model A k (rounded true model W k values v hv) small
        (lengths model W A k values).1 (length_correct model W A k values v hv small) budget).1 :=
  (data model W A k values v hv small budget).trans
    (GeneralPaperEqualBitContinuation.data model A k _ small _ _ budget).symm

theorem price_join {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := (run model W A k values v hv small budget).2
    GeneralPaperEqualBitPreparationLedger.total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2 =
      (raw model W k values).2+(lengths model W A k values).2+
        (GeneralPaperEqualBitContinuation.run model A k (rounded true model W k values v hv) small
          (lengths model W A k values).1 (length_correct model W A k values v hv small) budget).2 := by
  dsimp only [run,GeneralPaperEqualBitPreparationLedger.total,GeneralPaperEqualBitContinuation.run,
    packing,routes,full]
  omega

def profile {n : ℕ} (model : RationalCostModel) (W A k : ℕ) (values : FixedArrayTable n ℚ) (b : ℕ) : ℕ :=
  GeneralPaperEqualFirstPreparationRates.profile model W A n k (GeneralPaperValueRoundingInputPrice.inputSize values) b

theorem bit_work {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := (run model W A k values v hv small budget).2
    GeneralPaperEqualBitPreparationLedger.total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2 ≤
      profile model W A k values (rationalWordWidth budget) := by
  dsimp only
  rw [price_join]
  have h0 := GeneralPaperEqualFirstPrefixRates.prefix_work model W A k values v hv
  have h1 := GeneralPaperEqualFirstPreparationWork.continuation_work model W A k values v hv small
    (lengths model W A k values).1 (length_correct model W A k values v hv small) budget
  have h := Nat.add_le_add h0 h1
  apply h.trans
  change _ ≤ GeneralPaperEqualFirstPreparationRates.profile model W A n k
    (GeneralPaperValueRoundingInputPrice.inputSize values) (rationalWordWidth budget)
  rw [← GeneralPaperEqualFirstPreparationRates.ledger_eq]
  unfold GeneralPaperEqualFirstPreparationWork.bound
  omega

theorem prepared_projection {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    (run model W A k values v hv small budget).1.prepared =
      GeneralPaperEqualFirstPowerBooleanSpace.prepared model W A k values v hv small budget := by
  rw [data,GeneralPaperEqualFirstPowerBooleanSpace.prepared_eq]
  rfl

theorem boolean_return_and_price {n : ℕ} (model : RationalCostModel) (W A k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2*(rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) :
    let result := run model W A k values v hv small budget
    let actual := GeneralPaperStoredBooleanCache.run
      (GeneralPaperEqualFirstPowerBooleanSpace.prepared model W A k values v hv small budget) model A
    actual.1 = result.1.categorical ∧ actual.2 = result.2.1.2.2 := by
  exact ⟨rfl,rfl⟩

end Blotto.GeneralPaperEqualFirstGroupedPreparation
