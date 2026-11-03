import Blotto.GeneralPaperActualRoundPrice

/-! One local epoch controller retains each already-produced candidate row
by one array push. Capacity is the retained period, not a length census.
All counter, branch, descriptor and bounded-buffer controls are explicit. -/
namespace Blotto.GeneralPaperLocalEpochExecution
open GeneralPaperCatalogueEpochCache
open GeneralPaperSummaryArrayExecution (arrayWord)
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def control (index : ℕ → ℕ) (A count : ℕ) : ℕ :=
  GeneralPaperIntegerWordPrice.compare index count 0+
    GeneralPaperNaturalPrimitivePrice.binary index (fun a b => a-b) count 1+128*A

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (capacity : ℕ) :
    ℕ → (State cache × Array (FixedArrayTable m ℕ)) × ℕ
  | 0 => ((first,#[]),PaperIndexedArrayConstruction.initialWork index (if bits then arrayWord W (capacity+2) else W) capacity+
      GeneralPaperIntegerWordPrice.compare index 0 0+64*(if bits then arrayWord W (capacity+2) else W))
  | count+1 =>
    let A := if bits then arrayWord W (capacity+2) else W
    let previous := run bits index price W c cache profit T weights Bc Br first capacity count
    let next := GeneralPaperRoundExecution.run bits index price W c cache profit T weights Bc Br previous.1.1
    ((next.1.state,previous.1.2.push next.1.candidate),previous.2+next.2+
      PaperIndexedArrayConstruction.stepWork index A previous.1.2.size+control index A (count+1))

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (first : State cache) (capacity count : ℕ) (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (run bits index price W c cache profit T weights Bc Br first capacity count).1=
      GeneralPaperCatalogueEpoch.execute cache c.powers profit T weights Bc Br first count := by
  induction count with
  | zero => rfl
  | succ count ih =>
    simp only [run,ih,GeneralPaperRoundExecution.data bits index price W lambda Qv c hc cache profit T weights Bc Br _ hSpan,
      GeneralPaperCatalogueEpoch.execute]

theorem size {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (capacity count : ℕ) :
    (run bits index price W c cache profit T weights Bc Br first capacity count).1.2.size=count := by
  induction count with
  | zero => rfl
  | succ count ih => simp only [run,Array.size_push,ih]

def execute {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (capacity count : ℕ) :
    (State cache × Array (FixedArrayTable m ℕ)) × ℕ :=
  let first := GeneralPaperEpochInitialFamilyPrice.run bits index (if bits then price else fun _ => 1) W cache
  let computed := run bits index price W c cache profit T weights Bc Br first.1 capacity count
  (computed.1,first.2+computed.2+128*W)

theorem execute_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br : ℚ) (capacity count : ℕ) (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (execute bits index price W c cache profit T weights Bc Br capacity count).1=
      GeneralPaperCatalogueEpoch.execute cache c.powers profit T weights Bc Br (GeneralPaperCatalogueEpochCache.initial cache) count := by
  simp only [execute,data bits index price W lambda Qv c hc cache profit T weights Bc Br _ capacity count hSpan,
    GeneralPaperEpochInitialFamilyPrice.data]

theorem prefix_capacity {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (first : State cache) (capacity count : ℕ) (hc : count≤capacity) :
    (run bits index price W c cache profit T weights Bc Br first capacity count).1.2.size≤capacity := by rw [size]; exact hc

end Blotto.GeneralPaperLocalEpochExecution
