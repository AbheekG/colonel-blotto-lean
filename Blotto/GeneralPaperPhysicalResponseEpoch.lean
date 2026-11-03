import Blotto.GeneralPaperPhysicalResponseRates

/-! Execute a local epoch with the physical response check in every round.
The shared shift is borrowed throughout; candidate rows, state updates and
controller operations are preserved. One flag records all native checks. -/
namespace Blotto.GeneralPaperPhysicalResponseEpoch
open GeneralPaperCatalogueEpochCache GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

def run {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (first : State cache) (capacity : ℕ) :
    ℕ → ((State cache × Array (FixedArrayTable m ℕ)) × Bool) × ℕ
  | 0 => (((first,#[]),true),PaperIndexedArrayConstruction.initialWork index (if bits then arrayWord W (capacity+2) else W) capacity+
      GeneralPaperIntegerWordPrice.compare index 0 0+64*(if bits then arrayWord W (capacity+2) else W))
  | count+1 =>
    let A := if bits then arrayWord W (capacity+2) else W
    let previous := run bits index price model W c cache profit T weights Bc Br delta first capacity count
    let next := GeneralPaperPhysicalResponseRound.run bits index price model W c cache profit T weights Bc Br delta previous.1.1.1
    (((next.1.1.state,previous.1.1.2.push next.1.1.candidate),previous.1.2 && next.1.2),previous.2+next.2+
      PaperIndexedArrayConstruction.stepWork index A previous.1.1.2.size+
      GeneralPaperLocalEpochExecution.control index A (count+1)+32*A)

theorem base_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (first : State cache) (capacity count : ℕ) :
    (run bits index price model W c cache profit T weights Bc Br delta first capacity count).1.1=
      (GeneralPaperLocalEpochExecution.run bits index price W c cache profit T weights Bc Br first capacity count).1 := by
  induction count with
  | zero => rfl
  | succ count ih =>
    rw [run,GeneralPaperLocalEpochExecution.run]
    dsimp only
    simp only [GeneralPaperPhysicalResponseRound.base_data,ih]

theorem data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (first : State cache) (capacity count : ℕ)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (run bits index price model W c cache profit T weights Bc Br delta first capacity count).1.1=
      GeneralPaperCatalogueEpoch.execute cache c.powers profit T weights Bc Br first count := by
  rw [base_data]
  exact GeneralPaperLocalEpochExecution.data bits index price W lambda Qv c hc cache profit T weights Bc Br first capacity count hSpan

theorem checked {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W Qv q qbar capacity count : ℕ)
    (cache : Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv) (hB : 0≤Br) (hDen : Br.den∣q)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    (run bits index price model W c cache profit T weights Bc Br
      (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C) (initial cache) capacity count).1.2=true := by
  dsimp only
  let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
  let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
  have hSpan : profit.parameters.leafCount=2^profit.parameters.height :=
    GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv
  have hp : c.powers=GeneralPaperPreparedPowers.prepare cache.alphabet.lambda k := by rw [hc]; rfl
  induction count with
  | zero => rfl
  | succ count ih =>
    have hi := ih (by omega)
    have hs := congrArg Prod.fst (data bits index price model W cache.alphabet.lambda Qv c hc cache profit T
      weights Bc Br (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C) (initial cache) capacity count hSpan)
    rw [hp] at hs
    have hr := GeneralPaperPhysicalResponseRound.checked_reached bits index price model W Qv q qbar count cache c hc
      weights Bc Br hm hQv hq hCap hw hB hDen (by omega)
    rw [run]
    dsimp only
    rw [hi,Bool.true_and,hs]
    exact hr

theorem bit_extra {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t capacity count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (first : State cache)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight Br t) :
    (run true (fun w => w) model.rat model W c cache profit T weights Bc Br delta first capacity count).2≤
      (GeneralPaperLocalEpochExecution.run true (fun w => w) model.rat W c cache profit T weights Bc Br first capacity count).2+
      count*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t cache.alphabet+
        128*W+32*arrayWord W (capacity+2)) := by
  induction count with
  | zero => simp only [run,GeneralPaperLocalEpochExecution.run,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ count ih =>
    have hs := base_data true (fun w => w) model.rat model W c cache profit T weights Bc Br delta first capacity count
    have hr := GeneralPaperPhysicalResponseRound.bit_overhead model W lambda Qv qbar t c hc cache profit T weights Bc Br delta
      (GeneralPaperLocalEpochExecution.run true (fun w => w) model.rat W c cache profit T weights Bc Br first capacity count).1.1 hSpan hd hBr
    rw [run,GeneralPaperLocalEpochExecution.run]
    dsimp only
    rw [hs]
    simp only [ite_true]
    nlinarith only [ih,hr]

theorem arithmetic_extra {m k : ℕ} (price : ℕ → ℕ) (model : RationalCostModel) (capacity count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (first : State cache) :
    (run false (fun _ => 1) price model 1 c cache profit T weights Bc Br delta first capacity count).2≤
      (GeneralPaperLocalEpochExecution.run false (fun _ => 1) price 1 c cache profit T weights Bc Br first capacity count).2+
      count*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m cache.alphabet+160) := by
  induction count with
  | zero => simp only [run,GeneralPaperLocalEpochExecution.run,Nat.zero_mul,Nat.add_zero,le_refl]
  | succ count ih =>
    have hs := base_data false (fun _ => 1) price model 1 c cache profit T weights Bc Br delta first capacity count
    have hr := GeneralPaperPhysicalResponseRound.arithmetic_overhead price model c cache profit T weights Bc Br delta
      (GeneralPaperLocalEpochExecution.run false (fun _ => 1) price 1 c cache profit T weights Bc Br first capacity count).1.1
    rw [run,GeneralPaperLocalEpochExecution.run]
    dsimp only
    rw [hs]
    simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
    nlinarith only [ih,hr]

def execute {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (capacity count : ℕ) :
    ((State cache × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  let first := GeneralPaperEpochInitialFamilyPrice.run bits index (if bits then price else fun _ => 1) W cache
  let produced := run bits index price model W c cache profit T weights Bc Br delta first.1 capacity count
  (produced.1,first.2+produced.2+128*W)

theorem execute_data {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W lambda Qv : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (capacity count : ℕ)
    (hSpan : profit.parameters.leafCount=2^profit.parameters.height) :
    (execute bits index price model W c cache profit T weights Bc Br delta capacity count).1.1=
      GeneralPaperCatalogueEpoch.execute cache c.powers profit T weights Bc Br (initial cache) count := by
  unfold execute
  dsimp only
  rw [data bits index price model W lambda Qv c hc cache profit T weights Bc Br delta _ capacity count hSpan,
    GeneralPaperEpochInitialFamilyPrice.data]

theorem execute_checked {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W Qv q qbar capacity count : ℕ)
    (cache : Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv) (hB : 0≤Br) (hDen : Br.den∣q)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    (execute bits index price model W c cache
      (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights Bc Br
      (GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C) capacity count).1.2=true := by
  unfold execute
  dsimp only
  rw [GeneralPaperEpochInitialFamilyPrice.data]
  exact checked bits index price model W Qv q qbar capacity count cache c hc weights Bc Br hm hQv hq hCap hw hB hDen hCount

theorem models_data {m k : ℕ} (model : RationalCostModel) (W Qv q qbar capacity count : ℕ)
    (cache : Cache m k) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m cache.alphabet.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (hm : 0<m) (hQv : 0<Qv) (hq : 0<q)
    (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv) (hB : 0≤Br) (hDen : Br.den∣q)
    (hCount : count≤(GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).period) :
    let profit := GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv
    let T := (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows
    let delta := GeneralPaperTagBudgetTransfer.shift m qbar cache.alphabet.C
    (execute true (fun w => w) model.rat model W c cache profit T weights Bc Br delta capacity count).1=
      (execute false (fun _ => 1) (fun _ => 1) model 1 c cache profit T weights Bc Br delta capacity count).1 := by
  dsimp only
  have hSpan := GeneralPaperProfitParameters.leaf_count_spec m cache.alphabet.lambda k Qv
  apply Prod.ext
  · exact (execute_data true (fun w => w) model.rat model W cache.alphabet.lambda Qv c hc cache
      (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
      (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights Bc Br _ capacity count hSpan).trans
        (execute_data false (fun _ => 1) (fun _ => 1) model 1 cache.alphabet.lambda Qv c hc cache
          (GeneralPaperProfitParameters.prepare m cache.alphabet.lambda k Qv)
          (GeneralPaperTrajectoryParameters.prepare cache.alphabet.lambda k).rows weights Bc Br _ capacity count hSpan).symm
  · rw [execute_checked true (fun w => w) model.rat model W Qv q qbar capacity count cache c hc weights Bc Br hm hQv hq hCap hw hB hDen hCount,
      execute_checked false (fun _ => 1) (fun _ => 1) model 1 Qv q qbar capacity count cache c hc weights Bc Br hm hQv hq hCap hw hB hDen hCount]

end Blotto.GeneralPaperPhysicalResponseEpoch
