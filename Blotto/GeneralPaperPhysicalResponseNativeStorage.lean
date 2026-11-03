import Blotto.GeneralPaperPhysicalResponseStorageRates

/-! Finite erased child windows follow actual checked local-prefix states,
actual prepared epoch caches and the actual checked source's returned forest.
Child payload peaks are maxima across time/epochs. Only flag/reference caller
frames accumulate; the once-built shift remains a single shared resident. -/
namespace Blotto.GeneralPaperPhysicalResponseNativeStorage
open GeneralPaperCodeAlphabet GeneralPaperCatalogueShared GeneralPaperCatalogueEpochCache
open GeneralPaperFiniteStorageWindows GeneralPaperSummaryArrayExecution
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 8192

def roundWindow {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (state : State cache) : ℕ :=
  let selected := GeneralPaperRoundExecution.run true (fun w => w) model.rat W c cache profit T weights Bc Br state
  GeneralPaperPhysicalResponseStorage.window model W cache.alphabet delta selected.1.response Br

theorem round_bound {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (state : State cache) (hSpan : profit.parameters.leafCount=2^profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight Br t) :
    roundWindow model W c cache profit T weights Bc Br delta state≤
      GeneralPaperPhysicalResponseStorage.profile model W m qbar t cache.alphabet :=
  GeneralPaperPhysicalResponseStorage.bounded model W qbar t cache.alphabet delta hd _
    (GeneralPaperPhysicalResponseRound.response_code_bound true (fun w => w) model.rat W lambda Qv c hc cache
      profit T weights Bc Br state hSpan) Br hBr

def epochChildren {m k : ℕ} (model : RationalCostModel) (W : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (capacity : ℕ) : ℕ :=
  let first := (GeneralPaperEpochInitialFamilyPrice.run true (fun w => w) model.rat W cache).1
  maximum (fun time : Fin capacity =>
    let previous := GeneralPaperPhysicalResponseEpoch.run true (fun w => w) model.rat model W c cache profit T
      weights Bc Br delta first capacity time.val
    roundWindow model W c cache profit T weights Bc Br delta previous.1.1.1)

theorem epoch_bound {m k : ℕ} (model : RationalCostModel) (W lambda Qv qbar t : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (cache : Cache m k) (profit : GeneralPaperProfitParameters.Prepared) (T : ℕ) (weights : FixedArrayTable m ℕ)
    (Bc Br delta : ℚ) (capacity : ℕ) (hSpan : profit.parameters.leafCount=2^profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar cache.alphabet.C))
    (hBr : RationalHeight Br t) :
    epochChildren model W c cache profit T weights Bc Br delta capacity≤
      GeneralPaperPhysicalResponseStorage.profile model W m qbar t cache.alphabet := by
  apply maximum_bound
  intro time
  exact round_bound model W lambda Qv qbar t c hc cache profit T weights Bc Br delta _ hSpan hd hBr

def outerChildren {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda) : ℕ :=
  let cache := (GeneralPaperTreeEpochPreparation.run true (fun w => w) model W m k Qv a c hc shared.wordWidth trees).1
  epochChildren model W c cache shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta shared.trajectory.period

theorem outer_bound {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (delta : ℚ) (trees : GeneralPaperCatalogueTreeCache.Trees m a.lambda)
    (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hd : RationalHeight delta (GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C)) (hBr : RationalHeight shared.Br t) :
    outerChildren model W k Qv a c hc shared delta trees≤GeneralPaperPhysicalResponseStorage.profile model W m qbar t a :=
  epoch_bound model W a.lambda Qv qbar t c hc _ shared.profit shared.trajectory.rows shared.weights shared.Bc shared.Br delta
    shared.trajectory.period hSpan hd hBr

def sourceChildren {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) : ℕ :=
  let delta := (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1
  maximum (fun epoch : Fin count =>
    let previous := GeneralPaperPhysicalResponseSourceExecution.run true (fun w => w) model W k Qv a c hc shared delta epoch.val
    outerChildren model W k Qv a c hc shared delta previous.1.1.1)

theorem source_bound {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (shared : Shared m) (count : ℕ) (hSpan : shared.profit.parameters.leafCount=2^shared.profit.parameters.height)
    (hBr : RationalHeight shared.Br t) :
    sourceChildren model W k Qv qbar a c hc shared count≤GeneralPaperPhysicalResponseStorage.profile model W m qbar t a := by
  apply maximum_bound
  intro epoch
  exact outer_bound model W k Qv qbar t a c hc shared _ _ hSpan
    (GeneralPaperPhysicalShiftExecution.height true model W m qbar a.C) hBr

def flags (W lambda k : ℕ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  (t.epochs+t.period+64)*(256*arrayWord W (t.rows+t.epochs+t.period+2)+4)

def flagWindow (W lambda k count : ℕ) : ℕ :=
  let t := GeneralPaperTrajectoryParameters.prepare lambda k
  (count+t.period+16)*(128*arrayWord W (t.rows+t.epochs+t.period+2)+2)

theorem flags_bound (W lambda k count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare lambda k).epochs) :
    flagWindow W lambda k count≤flags W lambda k := by
  unfold flagWindow flags
  dsimp only
  exact Nat.mul_le_mul (by omega) (by omega)

def extraWindow {m : ℕ} (model : RationalCostModel) (W k Qv qbar : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ) : ℕ :=
  GeneralPaperPhysicalShiftStorage.window model W m qbar a.C+
    rationalWordWidth (GeneralPaperPhysicalShiftExecution.run true model W m qbar a.C).1+
    sourceChildren model W k Qv qbar a c hc (prepare a k Qv weights Bc Br) count+flagWindow W a.lambda k count

def extraProfile (model : RationalCostModel) (W m k qbar t : ℕ) (a : Alphabet) : ℕ :=
  GeneralPaperPhysicalShiftStorage.profile model W m qbar a.C+
    (1+2*GeneralPaperResponsePhysicalHeights.shiftHeight m qbar a.C)+
    GeneralPaperPhysicalResponseStorage.profile model W m qbar t a+flags W a.lambda k

theorem extra_bound {m : ℕ} (model : RationalCostModel) (W k Qv qbar t : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) (count : ℕ)
    (he : count≤(GeneralPaperTrajectoryParameters.prepare a.lambda k).epochs) (hBr : RationalHeight Br t) :
    extraWindow model W k Qv qbar a c hc weights Bc Br count≤extraProfile model W m k qbar t a := by
  have hShift := GeneralPaperPhysicalShiftStorage.bounded model W m qbar a.C a.scalePositive
  have hResident := GeneralPaperPhysicalShiftStorage.resident true model W m qbar a.C
  have hChild := source_bound model W k Qv qbar t a c hc (prepare a k Qv weights Bc Br) count
    (GeneralPaperProfitParameters.leaf_count_spec m a.lambda k Qv) hBr
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add hShift hResident) hChild) (flags_bound W a.lambda k count he)

end Blotto.GeneralPaperPhysicalResponseNativeStorage
