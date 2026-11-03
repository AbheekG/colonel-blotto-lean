import Blotto.GeneralPaperPhysicalResponseEpoch

/-! Extend the actual tree epoch with the checked local epoch. The same
prepared cache and returned final fields feed the existing forest update;
one flag carries every physical response check back to the source caller. -/
namespace Blotto.GeneralPaperPhysicalResponseOuterEpoch
open GeneralPaperCodeAlphabet GeneralPaperCatalogueTreeCache GeneralPaperCatalogueShared
open GeneralPaperCatalogueEpochCache GeneralPaperCatalogueOuterLoop GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 2200000
set_option maxRecDepth 8192

theorem local_base {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared)
    (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (capacity count : ℕ) :
    (GeneralPaperPhysicalResponseEpoch.execute bits index price model W c cache profit T weights Bc Br delta capacity count).1.1=
      (GeneralPaperLocalEpochExecution.execute bits index price W c cache profit T weights Bc Br capacity count).1 := by
  unfold GeneralPaperPhysicalResponseEpoch.execute GeneralPaperLocalEpochExecution.execute
  dsimp only
  exact GeneralPaperPhysicalResponseEpoch.base_data bits index price model W c cache profit T weights Bc Br delta _ capacity count

def finish {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (ha : cache.alphabet=a)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    ((Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  let localResult := GeneralPaperPhysicalResponseEpoch.execute bits index price model W c cache shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br delta shared.trajectory.period shared.trajectory.period
  let inputTrees : Trees m cache.alphabet.lambda := ha.symm ▸ trees
  let updated := GeneralPaperForestUpdateExecution.run bits index price W c shared inputTrees localResult.1.1.1
  (((ha ▸ updated.1,localResult.1.1.2),localResult.1.2),localResult.2+updated.2+256*W+32*W)

def run {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    ((Trees m a.lambda × Array (FixedArrayTable m ℕ)) × Bool) × ℕ :=
  let prepared := GeneralPaperTreeEpochPreparation.run bits index model W m k Qv a c hc shared.wordWidth trees
  let computed := finish bits index model.rat model W a c prepared.1 rfl shared delta trees
  (computed.1,prepared.2+computed.2+128*W+32*W)

theorem finish_base {m k : ℕ} (bits : Bool) (index price : ℕ → ℕ) (model : RationalCostModel) (W : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (ha : cache.alphabet=a)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    (finish bits index price model W a c cache ha shared delta trees).1.1=
      (GeneralPaperOuterEpochExecution.finish bits index price W a c cache ha shared trees).1 := by
  unfold finish GeneralPaperOuterEpochExecution.finish
  dsimp only
  rw [local_base]

theorem base_data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    (run bits index model W k Qv a c hc shared delta trees).1.1=
      (GeneralPaperOuterEpochExecution.run bits index model W k Qv a c hc shared trees).1 := by
  unfold run GeneralPaperOuterEpochExecution.run
  dsimp only
  exact finish_base bits index model.rat model W a c _ rfl shared delta trees

theorem data {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (epoch : ℕ)
    (he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (run bits index model W k Qv a c hc shared delta trees).1.1=GeneralPaperCatalogueOuterLoop.epoch shared a k trees := by
  dsimp only
  rw [base_data]
  exact GeneralPaperOuterEpochExecution.data bits index model W k Qv a c hc weights Bc Br epoch he

theorem checked {m : ℕ} (bits : Bool) (index : ℕ → ℕ) (model : RationalCostModel) (W k Qv q qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (epoch : ℕ)
    (hm : 0<m) (hQv : 0<Qv) (hq : 0<q) (hCap : q≤qbar) (hw : ∑ j,weights.read j=Qv)
    (hB : 0≤Br) (hDen : Br.den∣q)
    (_he : epoch+1≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) :
    let shared := prepare a k Qv weights Bc Br
    let trees := treesAt shared a k epoch
    (run bits index model W k Qv a c hc shared (GeneralPaperTagBudgetTransfer.shift m qbar a.C) trees).1.2=true := by
  dsimp only
  unfold run finish
  dsimp only
  exact GeneralPaperPhysicalResponseEpoch.execute_checked bits index model.rat model W Qv q qbar
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period
    (GeneralPaperTrajectoryParameters.prepare a.lambda k).period _ c hc weights Bc Br hm hQv hq hCap hw hB hDen le_rfl

theorem local_bit_extra {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t capacity count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ)
    (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) (hSpan : profit.parameters.leafCount=2^profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight Br t) :
    (GeneralPaperPhysicalResponseEpoch.execute true (fun w => w) model.rat model W c cache profit T weights Bc Br delta capacity count).2≤
      (GeneralPaperLocalEpochExecution.execute true (fun w => w) model.rat W c cache profit T weights Bc Br capacity count).2+
      count*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t cache.alphabet+128*W+32*arrayWord W (capacity+2)) := by
  unfold GeneralPaperPhysicalResponseEpoch.execute GeneralPaperLocalEpochExecution.execute
  dsimp only
  have h := GeneralPaperPhysicalResponseEpoch.bit_extra model W lambda Qv qbar t capacity count c hc cache profit T
    weights Bc Br delta
    (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1 hSpan hd hBr
  simp only [ite_true]
  nlinarith only [h]

theorem finish_bit_extra {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (ha : cache.alphabet=a) (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight shared.Br t) :
    (finish true (fun w => w) model.rat model W a c cache ha shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.finish true (fun w => w) model.rat W a c cache ha shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t cache.alphabet+
        128*W+32*arrayWord W (shared.trajectory.period+2))+32*W := by
  have hl := local_bit_extra model W lambda Qv qbar t shared.trajectory.period shared.trajectory.period c hc cache
    shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta hSpan hd hBr
  have hData := local_base true (fun w => w) model.rat model W c cache shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br delta shared.trajectory.period shared.trajectory.period
  unfold finish GeneralPaperOuterEpochExecution.finish
  dsimp only
  rw [hData]
  nlinarith only [hl]

theorem bit_extra {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C))
    (hBr : RationalHeight shared.Br t) :
    (run true (fun w => w) model W k Qv a c hc shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.run true (fun w => w) model W k Qv a c hc shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t a+
        128*W+32*arrayWord W (shared.trajectory.period+2))+64*W := by
  let cache := (GeneralPaperTreeEpochPreparation.run true (fun w => w) model W m k Qv a c hc shared.wordWidth trees).1
  have hl : (finish true (fun w => w) model.rat model W a c cache rfl shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.finish true (fun w => w) model.rat W a c cache rfl shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.bitProfile model W m qbar t a+
        128*W+32*arrayWord W (shared.trajectory.period+2))+32*W :=
    finish_bit_extra model W a.lambda Qv qbar t a c hc cache rfl shared delta trees hSpan hd hBr
  unfold run GeneralPaperOuterEpochExecution.run
  dsimp only
  nlinarith only [hl]

theorem local_arithmetic_extra {m k : ℕ} (price : ℕ → ℕ) (model : RationalCostModel) (capacity count : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k)
    (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ) (Bc Br delta : ℚ) :
    (GeneralPaperPhysicalResponseEpoch.execute false (fun _ => 1) price model 1 c cache profit T weights Bc Br delta capacity count).2≤
      (GeneralPaperLocalEpochExecution.execute false (fun _ => 1) price 1 c cache profit T weights Bc Br capacity count).2+
      count*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m cache.alphabet+160) := by
  have h := GeneralPaperPhysicalResponseEpoch.arithmetic_extra price model capacity count c cache profit T weights Bc Br delta
    (GeneralPaperEpochInitialFamilyPrice.run false (fun _ => 1) (fun _ => 1) 1 cache).1
  unfold GeneralPaperPhysicalResponseEpoch.execute GeneralPaperLocalEpochExecution.execute
  dsimp only
  simp only [Bool.false_eq_true,ite_false,Nat.mul_one]
  nlinarith only [h]

theorem finish_arithmetic_extra {m k : ℕ} (price : ℕ → ℕ) (model : RationalCostModel) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (cache : Cache m k) (ha : cache.alphabet=a)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    (finish false (fun _ => 1) price model 1 a c cache ha shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.finish false (fun _ => 1) price 1 a c cache ha shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m cache.alphabet+160)+32 := by
  have hl := local_arithmetic_extra price model shared.trajectory.period shared.trajectory.period c cache
    shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta
  have hData := local_base false (fun _ => 1) price model 1 c cache shared.profit shared.trajectory.rows
    shared.weights shared.Bc shared.Br delta shared.trajectory.period shared.trajectory.period
  unfold finish GeneralPaperOuterEpochExecution.finish
  dsimp only
  rw [hData]
  nlinarith only [hl]

theorem arithmetic_extra {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : Trees m a.lambda) :
    (run false (fun _ => 1) model 1 k Qv a c hc shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.run false (fun _ => 1) model 1 k Qv a c hc shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m a+160)+64 := by
  let cache := (GeneralPaperTreeEpochPreparation.run false (fun _ => 1) model 1 m k Qv a c hc shared.wordWidth trees).1
  have hl : (finish false (fun _ => 1) model.rat model 1 a c cache rfl shared delta trees).2≤
      (GeneralPaperOuterEpochExecution.finish false (fun _ => 1) model.rat 1 a c cache rfl shared trees).2+
      shared.trajectory.period*(GeneralPaperPhysicalResponseExecution.arithmeticProfile m a+160)+32 :=
    finish_arithmetic_extra model.rat model a c cache rfl shared delta trees
  unfold run GeneralPaperOuterEpochExecution.run
  dsimp only
  nlinarith only [hl]

end Blotto.GeneralPaperPhysicalResponseOuterEpoch
