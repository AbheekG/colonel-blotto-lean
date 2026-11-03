import Blotto.BinaryTraceScalarBaseWork
import Blotto.BinaryWordCoinSourceMeasured
import Blotto.BinaryHeapLoopPrimitiveMeasured
import Blotto.BinaryCacheFinishPlan
import Blotto.BinaryBuildAllowancePlan
import Blotto.BinaryPackedPairPlan
import Blotto.BinaryWriteContinuationRequest

/-! Every additional direct emitter boundary found in the selected project-C
reference closure has its actual scalar-addition class priced here. Returned
records supply the ceilings; these are canonical Boolean scalar components. -/
namespace Blotto.BinaryDirectEmitterScalarWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured BinaryTraceScalarWork
open BinaryTraceScalarReturnedBound (ceiling charge finish_usage)
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGPhysicalRawRequestLifetime (Request)
set_option autoImplicit false
set_option maxHeartbeats 1000000
attribute [local irreducible] BinaryWriteContinuationInitial.sourceAtTraceWithWrites
attribute [local irreducible] BinaryWriteContinuationInitial.sourcePlanWithWritesAt
attribute [local irreducible] BinaryWriteContinuationRequest.nativeAtWithEmission

def coin (store : BinarySeedLookupTree.Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) : ℕ :=
  finishWork (BinaryWordCoinSourceMeasured.samplePlanAt store word pc hp depth).1.1.2 []

theorem coin_bound (store : BinarySeedLookupTree.Store) (word : SignedWord) (pc : FixedBinaryWord store.width)
    (hp : pc.value ≤ store.cap.value) (depth : ℕ) :
    coin store word pc hp depth ≤ ceiling (BinaryWordCoinSourceMeasured.sampleTraceMeasured store word pc hp depth).2
      (usage (BinaryWordCoinSourceMeasured.sampleTraceMeasured store word pc hp depth).1.1.1.2) := by
  simpa only [coin,BinaryWordCoinSourceMeasured.sampleTraceMeasured,charge] using
    finish_usage (BinaryWordCoinSourceMeasured.samplePlanAt store word pc hp depth).1.1.2 []

variable {n : ℕ}

def allowance (ruler first second : List Bool) : ℕ :=
  finishWork (BinaryBuildAllowancePlan.calculateAt ruler first second 0).1.2 []

theorem allowance_bound (ruler first second : List Bool) :
    allowance ruler first second ≤ ceiling (BinaryBuildAllowancePlan.calculateWithEmission ruler first second).2
      (usage (BinaryBuildAllowancePlan.calculateWithEmission ruler first second).1.1.2) := by
  simpa only [allowance,BinaryBuildAllowancePlan.calculateWithEmission,charge] using
    finish_usage (BinaryBuildAllowancePlan.calculateAt ruler first second 0).1.2 []

def cache {m : ℕ} (input : BinaryTerminalGrouping.Input m) (store : BinaryWordObjectArray.Store m) : ℕ :=
  finishWork (BinaryCacheFinishPlan.cacheAt input store 0).1.1.1.2 []

theorem cache_bound {m : ℕ} (input : BinaryTerminalGrouping.Input m) (store : BinaryWordObjectArray.Store m) :
    cache input store ≤ ceiling (BinaryCacheFinishPlan.cacheWithEmission input store).1.1.2
      (usage (BinaryCacheFinishPlan.cacheWithEmission input store).1.1.1.1.2) := by
  simpa only [cache,BinaryCacheFinishPlan.cacheWithEmission,charge] using
    finish_usage (BinaryCacheFinishPlan.cacheAt input store 0).1.1.1.2 []

def four (a b c d : Trace) : ℕ := finishWork (.join (.block [.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c) (.shifted 2 d))))) []

theorem four_bound (a b c d : Trace) : four a b c d ≤ ceiling (BinaryPackedPairPlan.four a b c d).2
    (usage (BinaryPackedPairPlan.four a b c d).1) := by
  simpa only [four,BinaryPackedPairPlan.four,charge] using finish_usage (.join (.block [.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c) (.shifted 2 d))))) []

def six (allocated : ℕ) (a b c d e f : Trace) : ℕ := finishWork (.join (.block [.listAllocation allocated,.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c)
      (.join (.shifted 2 d) (.join (.shifted 2 e) (.shifted 2 f))))))) []

theorem six_bound (allocated : ℕ) (a b c d e f : Trace) : six allocated a b c d e f ≤ ceiling (BinaryPackedPairPlan.six allocated a b c d e f).2
    (usage (BinaryPackedPairPlan.six allocated a b c d e f).1) := by
  simpa only [six,BinaryPackedPairPlan.six,charge] using finish_usage (.join (.block [.listAllocation allocated,.frames 2,.arrayAllocation 32])
    (.join (.shifted 2 a) (.join (.shifted 2 b) (.join (.shifted 2 c)
      (.join (.shifted 2 d) (.join (.shifted 2 e) (.shifted 2 f))))))) []

def source (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let writePlan := BinaryWriteContinuationInitial.sourcePlanWithWritesAt seed request rich pc hp 0
  let readPlan := writePlan.1
  let primitive := readPlan.1
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let planned := returned.1
  BinaryTraceScalarBaseWork.work planned.1.1.1.2 [] planned.2

theorem source_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    source seed request rich pc hp ≤ BinaryTraceScalarBaseWork.ceiling (BinaryWriteContinuationInitial.sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1.1.2
      (usage (BinaryWriteContinuationInitial.sourceAtTraceWithWrites seed request rich pc hp).1.1.1.1.1.1.1.1.1.1.1.2) := by
  unfold source BinaryWriteContinuationInitial.sourceAtTraceWithWrites
  dsimp only
  exact BinaryTraceScalarBaseWork.usage _ [] _

def native (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) : ℕ :=
  let selected := BinaryPRGResourceWork.resourceInput request.logical.request rich
  let writeSource := BinaryWriteContinuationInitial.sourceAtTraceWithWrites seed request rich pc hp
  let readSource := writeSource.1
  let primitive := readSource.1
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let produced := returned.1
  let drawn := produced.1.1
  match drawn.1.1.1.2.1 with
  | none =>
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 16])
        (.shifted 2 drawn.1.2)
      finishWork plan []
  | some state =>
      let readTerminal := BinaryPackedMaterializationPlan.materializeAt selected.length
        (BinaryPRGWordControllerBooleanResourceSource.capacityTable selected.length)
        drawn.1.1.1.1 (by simpa only [drawn,produced,returned,child,supplied,entry,construction,primitive,readSource,writeSource,BinaryWriteContinuationInitial.sourceAtTraceWithWrites_compat,
          BinaryPackedContinuationInitial.sourceAtTraceWithWrites_compat,
          BinaryPrimitiveInitial.sourceAtTraceWithWrites_compat,
          BinaryConstructionInitial.sourceAtTraceWithWrites_compat,
          BinaryEnumerationInitial.sourceAtTraceWithWrites_compat,
          BinaryCompleteInitialEmission.sourceAtTraceWithWrites_compat,
          BinaryAllowanceEmissionInitial.sourceAtTraceWithWrites_compat,
          BinaryPhysicalHeapAllowanceInitial.sourceAt,BinaryPhysicalHeapAllowanceInitial.sourceAtMeasured,
          BinaryPhysicalHeapAllowanceInitial.sourceAtTraceMeasured]
          using BinaryPhysicalHeapAllowanceInitial.sourceAt_cap seed request rich pc hp) state 2
      let terminal := readTerminal.1
      let plan := BinaryTracePlanMeasured.Plan.join (.block [.frames 2,.arrayAllocation 24])
        (.join (.shifted 2 drawn.1.2) terminal.1.2)
      finishWork plan []

theorem native_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) :
    native seed request rich pc hp ≤ ceiling (BinaryWriteContinuationRequest.nativeAtWithEmission seed request rich pc hp).1.1.1.1.1.1.1.2
      (usage (BinaryWriteContinuationRequest.nativeAtWithEmission seed request rich pc hp).1.1.1.1.1.1.1.1.1.1.1.2) := by
  unfold native BinaryWriteContinuationRequest.nativeAtWithEmission
  dsimp only
  split
  · rename_i hNone
    simp only [hNone]
    apply finish_usage
  · rename_i state hSome
    simp only [hSome]
    apply finish_usage

def run (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) : ℕ :=
  let writeSource := BinaryWriteContinuationRequest.nativeAtWithEmission seed request rich (BinaryWordIndexCoinController.zeroIndex seed)
    (by rw [BinaryWordIndexCoinController.zeroIndex_value]; omega)
  let readSource := writeSource.1
  let primitive := readSource.1
  let construction := primitive.1
  let entry := construction.1
  let supplied := entry.1
  let child := supplied.1
  let returned := child.1
  let drawn := returned.1.1.1
  let width := seed.cap.bits.length
  let plan := BinaryTracePlanMeasured.Plan.join
    (.block [.listAllocation width,.frames (width+2),.arrayAllocation 16,.frames 4,.arrayAllocation 24])
    (.shifted 4 drawn.1.2)
  finishWork plan []

theorem run_bound (seed : BinarySeedLookupTree.Store) (request : Request n) (rich : Bool) :
    run seed request rich ≤ ceiling (BinaryWriteContinuationRequest.runWithCharges seed request rich).1.1.1.1.1.1.1.2.wrappers
      (usage (BinaryWriteContinuationRequest.runWithCharges seed request rich).1.1.1.1.1.1.1.1.1.2) := by
  unfold run BinaryWriteContinuationRequest.runWithCharges
  dsimp only
  apply finish_usage

variable {capacity : Store} {hCount : n=capacity.cap.value}

def loop (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) : ℕ :=
  let planned := (BinaryHeapLoopPrimitiveMeasured.loopPlanWithWritesAt seed limits canonical fuel state pc hp depth).1
  BinaryTraceScalarBaseWork.work planned.1.1.1.2 [] planned.2

theorem loop_bound (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (canonical : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    loop seed limits canonical fuel state pc hp depth ≤
      BinaryTraceScalarBaseWork.ceiling (BinaryHeapLoopPrimitiveMeasured.loopTraceWithWrites seed limits canonical fuel state pc hp depth).1.2
        (usage (BinaryHeapLoopPrimitiveMeasured.loopTraceWithWrites seed limits canonical fuel state pc hp depth).1.1.1.1.2) := by
  simpa only [loop,BinaryHeapLoopPrimitiveMeasured.loopTraceWithWrites,BinaryTraceScalarBaseWork.total] using
    BinaryTraceScalarBaseWork.usage
      (BinaryHeapLoopPrimitiveMeasured.loopPlanWithWritesAt seed limits canonical fuel state pc hp depth).1.1.1.1.2 []
      (BinaryHeapLoopPrimitiveMeasured.loopPlanWithWritesAt seed limits canonical fuel state pc hp depth).1.2

end Blotto.BinaryDirectEmitterScalarWork
