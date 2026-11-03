import Blotto.RationalLottoSharedBitPrices
import Blotto.RationalPRGSourceReaderLedger

/-! Both primary paper packets carry source operand and input-derivation
prices. Their event observer equals the retained serial ledger. The Boolean
controller allowance, terminal work and physical ownership are excluded. -/

namespace Blotto.RationalLottoResourceSystem

def sharedPaperSourceCallbackWork {n : ℕ} (i : RationalLottoResourceSystem n)
    (charge : RationalResourceCursor i.length → ℕ) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) : ℕ :=
  let inner := firstBitBlock (innerBitBudget n K) K bits
  i.sharedSourceCallbackWork charge (coinBitBudget n K)
    (firstBitBlock (coinBitBudget n K) K inner)

theorem sharedPaperSourceCallbackWork_refines {n : ℕ} (i : RationalLottoResourceSystem n)
    (charge : RationalResourceCursor i.length → ℕ) (K : ℕ)
    (bits : Fin (sampleBitBudget n K) → Bool) :
    i.sharedPaperSourceCallbackWork charge K bits =
      let inner := firstBitBlock (innerBitBudget n K) K bits
      let outer := secondBitBlock (innerBitBudget n K) K bits
      let scalar := secondBitBlock (coinBitBudget n K) K inner
      (i.machine K outer scalar).runCachedCallbackWork
        (WordStateMachine.serialSourceCharge (fun q : i.PhaseCursor => charge q.1))
        (coinBitBudget n K) (i.samplingStart K outer scalar)
        (firstBitBlock (coinBitBudget n K) K inner) :=
  i.sharedSourceCallbackWork_refines charge K _ _ _ _

end Blotto.RationalLottoResourceSystem
namespace Blotto.RationalPRGInput

def richSharedSourceDataAndReaderCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.richInitialDataBitCost model +
    i.richNativeSystem.sharedPaperSourceCallbackWork (rationalResourcePairRequestCharge model) K bits +
    i.richNativeSystem.sharedPaperSourceCallbackWork (rationalResourceStoreBitCharge model copyResources) K bits +
    i.richNativeSystem.sharedPaperSourceCallbackWork (rationalResourceRetainedBitCharge model) K bits +
    (i.richInitialReaderTotal model + i.richNativeSystem.sharedPaperSourceCallbackWork (i.sourceReaderCharge model) K bits)

def poorSharedSourceDataAndReaderCost {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) : ℕ :=
  i.poorInitialDataBitCost model +
    i.poorNativeSystem.sharedPaperSourceCallbackWork (rationalResourcePairRequestCharge model) K bits +
    i.poorNativeSystem.sharedPaperSourceCallbackWork (rationalResourceStoreBitCharge model copyResources) K bits +
    i.poorNativeSystem.sharedPaperSourceCallbackWork (rationalResourceRetainedBitCharge model) K bits +
    (i.poorInitialReaderTotal model + i.poorNativeSystem.sharedPaperSourceCallbackWork (i.sourceReaderCharge model) K bits)

theorem richSharedSourceDataAndReaderCost_refines {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedSourceDataAndReaderCost model copyResources K bits =
      i.richSourceDataAndReaderCost model copyResources K bits := by
  rw [richSharedSourceDataAndReaderCost,
    i.richNativeSystem.sharedPaperSourceCallbackWork_refines (i.sourceReaderCharge model) K bits]
  simp only [RationalLottoResourceSystem.sharedPaperSourceCallbackWork_refines]
  rfl

theorem poorSharedSourceDataAndReaderCost_refines {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceDataAndReaderCost model copyResources K bits =
      i.poorSourceDataAndReaderCost model copyResources K bits := by
  rw [poorSharedSourceDataAndReaderCost,
    i.poorNativeSystem.sharedPaperSourceCallbackWork_refines (i.sourceReaderCharge model) K bits]
  simp only [RationalLottoResourceSystem.sharedPaperSourceCallbackWork_refines]
  rfl

theorem richSharedSourceDataAndReaderCost_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (copyResources : Bool) (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.richSharedSourceDataAndReaderCost model copyResources K bits ≤ 15 * n * model.rat (8 * i.inputWordWidth + 31) := by
  rw [i.richSharedSourceDataAndReaderCost_refines]
  exact i.richSourceDataAndReaderCost_bound model copyResources K bits

theorem poorSharedSourceDataAndReaderCost_logical_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceDataAndReaderCost model false K bits ≤ 175 * n * model.rat (8 * i.inputWordWidth + 31) := by
  rw [i.poorSharedSourceDataAndReaderCost_refines]
  exact i.poorSourceDataAndReaderCost_logical_bound model K bits

theorem poorSharedSourceDataAndReaderCost_fullCopy_bound {n : ℕ} (i : RationalPRGInput n) (model : RationalCostModel)
    (K : ℕ) (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    i.poorSharedSourceDataAndReaderCost model true K bits ≤ (2 * n * n + 171 * n) * model.rat (8 * i.inputWordWidth + 31) := by
  rw [i.poorSharedSourceDataAndReaderCost_refines]
  exact i.poorSourceDataAndReaderCost_fullCopy_bound model K bits

end Blotto.RationalPRGInput
