import Blotto.BinaryHeapLoopPrimitiveMeasured
import Blotto.BinaryPackedUpdatePlan

/-! Actual planned pair/update reads feed the selected resource recursion.
The complete old plan/work/primitive/coin/write record is exact; a new price
sums only reached leaf/wrapper emissions. Parent emission remains unchanged. -/
namespace Blotto.BinaryPackedLoopPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished Result)
open BinaryPRGHeapTraceUsage
open BinaryTracePlanMeasured (Plan)
set_option autoImplicit false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency true

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

open BinaryHeapLoopPrimitiveMeasured (Prepared Draw Selection draw)
open BinaryTracePlanMeasured (payload)

@[irreducible] def prepare (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : Prepared hC state first second tail he × ℕ :=
  let packed := BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he
  let produced := packed.1
  (⟨⟨produced.1.1.1,produced.1.1.2,produced.1.2,by
    dsimp only [produced,packed]
    rw [BinaryPackedPairPlan.pair_compat,BinaryHeapPairSourceMeasured.pairMeasured_compat]
    exact BinaryHeapPairSourceMeasured.pair_value (hC := hC) limits state first second tail he⟩,produced.2⟩,packed.2)

theorem prepare_compat (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (prepare limits hC state first second tail he).1 = BinaryHeapLoopPrimitiveMeasured.prepare limits hC state first second tail he := by
  simp only [prepare,BinaryHeapLoopPrimitiveMeasured.prepare,BinaryPackedPairPlan.pair_compat]

theorem prepare_price (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (prepare limits hC state first second tail he).2 ≤ 150*(prepare limits hC state first second tail he).1.data.trace.length := by
  have h := BinaryPackedPairPlan.pair_price (hC := hC) limits state first second tail he
  simp only [prepare]
  omega

@[irreducible] def select (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : Selection state × ℕ :=
  let packed := BinaryPackedUpdatePlan.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch
  let measured := packed.1
  let produced := measured.1
  (⟨⟨produced.1.1.1,produced.1.1.2,produced.1.2.1,by
    dsimp only [produced,measured,packed]
    rw [BinaryPackedUpdatePlan.select_compat]
    change (BinaryHeapUpdateMeasured.select (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.active.length < state.active.length
    exact BinaryHeapUpdateMeasured.select_progress (hC := hC) limits state first second tail he outputs hOutputs branch⟩,
    produced.2+produced.1.2.2+9,measured.2⟩,packed.2)

theorem select_compat (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).1 =
      BinaryHeapLoopPrimitiveMeasured.select limits hC state first second tail he outputs hOutputs branch := by
  simp only [select,BinaryHeapLoopPrimitiveMeasured.select,BinaryPackedUpdatePlan.select_compat]

theorem select_price (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).2 ≤
      150*(select limits hC state first second tail he outputs hOutputs branch).1.data.trace.length := by
  have h := BinaryPackedUpdatePlan.select_price (hC := hC) limits state first second tail he outputs hOutputs branch
  simpa only [select] using h

def afterCoinPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → (((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (packedPrepared : Prepared hC state first second tail he × ℕ)
    (coin : Draw seed) (depth : ℕ) : (((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let prepared := packedPrepared.1
  match coin.data.outcome with
  | none =>
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join (.shifted (depth+2) prepared.data.trace) (.shifted (depth+2) coin.data.trace))
      (((((((none,coin.data.cursor),plan),prepared.data.work+coin.data.work+4),
        prepared.extra+coin.extra),coin.emission),0),packedPrepared.2)
  | some branch =>
      let packedSelected := select limits hC state first second tail he prepared.data.outputs prepared.data.valid branch
      let selected := packedSelected.1
      let packedReturned := resume selected.data.value coin.data.cursor coin.data.bounded (depth+2)
      let returned := packedReturned.1
      let later := returned.1
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.shifted (depth+2) prepared.data.trace)
          (.join (.shifted (depth+2) coin.data.trace)
            (.join (.shifted (depth+2) selected.data.trace) later.1.1.1.2)))
      ((((((later.1.1.1.1,plan),prepared.data.work+coin.data.work+selected.data.work+later.1.1.2+8),
        prepared.extra+coin.extra+selected.extra+later.1.2),coin.emission+later.2),selected.writeEmission+returned.2),packedPrepared.2+packedSelected.2+packedReturned.2)

def stepPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → (((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : (((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := prepare limits hC state first second tail he
      let coin := draw seed prepared.1.data.outputs.probability pc hp
      afterCoinPlanWithWritesAt seed limits hC resume state first second tail he prepared coin depth
  | _ => (((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0),0)

def loopPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  match fuel with
  | [] => (((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0),0)
  | _::rest => stepPlanWithWritesAt seed limits hC
      (fun state pc hp depth => loopPlanWithWritesAt seed limits hC rest state pc hp depth) state pc hp depth
termination_by structural fuel

theorem loop_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).1 =
      BinaryHeapLoopPrimitiveMeasured.loopPlanWithWritesAt seed limits hC fuel state pc hp depth := by
  induction fuel generalizing state pc depth with
  | nil => rfl
  | cons marker fuel ih =>
      rw [loopPlanWithWritesAt,BinaryHeapLoopPrimitiveMeasured.loopPlanWithWritesAt]
      rcases state with ⟨ruler,size,heap,root,valid,active,certified⟩
      cases active with
      | nil => rfl
      | cons first rest => cases rest with
        | nil => rfl
        | cons second tail =>
            simp only [stepPlanWithWritesAt,BinaryHeapLoopPrimitiveMeasured.stepPlanWithWritesAt,
              afterCoinPlanWithWritesAt,BinaryHeapLoopPrimitiveMeasured.afterCoinPlanWithWritesAt,
              prepare_compat,select_compat]
            split
            · rename_i hNone
              simp only [hNone]
            · rename_i branch hSome
              simp only [hSome,ih]

theorem loop_price (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).2 ≤
      150*payload (loopPlanWithWritesAt seed limits hC fuel state pc hp depth).1.1.1.1.1.2 := by
  induction fuel generalizing state pc depth with
  | nil => simp only [loopPlanWithWritesAt,payload,List.length_cons,List.length_nil]; omega
  | cons marker fuel ih =>
      unfold loopPlanWithWritesAt stepPlanWithWritesAt afterCoinPlanWithWritesAt
      dsimp only
      split
      · rename_i first second tail he
        let prepared := prepare limits hC state first second tail he
        let coin := draw seed prepared.1.data.outputs.probability pc hp
        have hp := prepare_price limits hC state first second tail he
        split
        · simp only [payload,List.length_cons,List.length_nil]
          omega
        · rename_i branch hSome
          let selected := select limits hC state first second tail he prepared.1.data.outputs prepared.1.data.valid branch
          have hs := select_price limits hC state first second tail he prepared.1.data.outputs prepared.1.data.valid branch
          have hl := ih selected.1.data.value coin.data.cursor coin.data.bounded (depth+2)
          dsimp only [selected,coin,prepared] at hl hs
          simp only [payload,List.length_cons,List.length_nil]
          omega
      · simp only [payload,List.length_cons,List.length_nil]; omega

def runPlanWithReadsAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) := loopPlanWithWritesAt seed limits hC state.active state pc hp depth

theorem run_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanWithReadsAt seed limits hC state pc hp depth).1 = BinaryHeapLoopPrimitiveMeasured.runPlanWithWritesAt seed limits hC state pc hp depth :=
  loop_compat seed limits hC state.active state pc hp depth

theorem run_price (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanWithReadsAt seed limits hC state pc hp depth).2 ≤
      150*payload (runPlanWithReadsAt seed limits hC state pc hp depth).1.1.1.1.1.2 :=
  loop_price seed limits hC state.active state pc hp depth

end Blotto.BinaryPackedLoopPlan
