import Blotto.BinaryPackedLoopPlan

/-! A resource selection backend consumes actual producers and preserves the
entire preceding selection/price record. The structural continuation forwards
only reached added prices. Concrete backends discharge refinement and bounds;
no backend premise is left in their instantiated execution contracts. -/
namespace Blotto.BinarySelectPriceContinuation
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

structure Backend (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) where
  run : ∀ (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool), (Selection state × ℕ) × ℕ
  compat : ∀ state first second tail he outputs hOutputs branch,
    (run state first second tail he outputs hOutputs branch).1 =
      BinaryPackedLoopPlan.select limits hC state first second tail he outputs hOutputs branch
  bound : ∀ state first second tail he outputs hOutputs branch,
    (run state first second tail he outputs hOutputs branch).2 ≤
      25*(run state first second tail he outputs hOutputs branch).1.1.data.trace.length

def afterCoinPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ((((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (packedPrepared : Prepared hC state first second tail he × ℕ)
    (coin : Draw seed) (depth : ℕ) : ((((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  let prepared := packedPrepared.1
  match coin.data.outcome with
  | none =>
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 24])
        (.join (.shifted (depth+2) prepared.data.trace) (.shifted (depth+2) coin.data.trace))
      ((((((((none,coin.data.cursor),plan),prepared.data.work+coin.data.work+4),
        prepared.extra+coin.extra),coin.emission),0),packedPrepared.2),0)
  | some branch =>
      let selectedProduced := backend.run state first second tail he prepared.data.outputs prepared.data.valid branch
      let packedSelected := selectedProduced.1
      let selected := packedSelected.1
      let returnedProduced := resume selected.data.value coin.data.cursor coin.data.bounded (depth+2)
      let packedReturned := returnedProduced.1
      let returned := packedReturned.1
      let later := returned.1
      let plan := Plan.join (.block [.frames (depth+2),.arrayAllocation 32])
        (.join (.shifted (depth+2) prepared.data.trace)
          (.join (.shifted (depth+2) coin.data.trace)
            (.join (.shifted (depth+2) selected.data.trace) later.1.1.1.2)))
      (((((((later.1.1.1.1,plan),prepared.data.work+coin.data.work+selected.data.work+later.1.1.2+8),
        prepared.extra+coin.extra+selected.extra+later.1.2),coin.emission+later.2),selected.writeEmission+returned.2),packedPrepared.2+packedSelected.2+packedReturned.2),selectedProduced.2+returnedProduced.2)

def stepPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (resume : (state : Finished capacity n hCount) → (pc : FixedBinaryWord seed.width) →
      pc.value ≤ seed.cap.value → ℕ → ((((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) : ((((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  match he : state.active with
  | first::second::tail =>
      let prepared := BinaryPackedLoopPlan.prepare limits hC state first second tail he
      let coin := draw seed prepared.1.data.outputs.probability pc hp
      afterCoinPlanWithWritesAt seed limits hC backend resume state first second tail he prepared coin depth
  | _ => ((((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0),0),0)

def loopPlanWithWritesAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    ((((((Result seed capacity n hCount × Plan) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ) × ℕ :=
  match fuel with
  | [] => ((((((((some state,pc),.block [.frames (depth+2),.arrayAllocation 16]),2),0),0),0),0),0)
  | _::rest => stepPlanWithWritesAt seed limits hC backend
      (fun state pc hp depth => loopPlanWithWritesAt seed limits hC backend rest state pc hp depth) state pc hp depth
termination_by structural fuel

theorem loop_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC backend fuel state pc hp depth).1 =
      BinaryPackedLoopPlan.loopPlanWithWritesAt seed limits hC fuel state pc hp depth := by
  induction fuel generalizing state pc depth with
  | nil => rfl
  | cons marker fuel ih =>
      rw [loopPlanWithWritesAt,BinaryPackedLoopPlan.loopPlanWithWritesAt]
      rcases state with ⟨ruler,size,heap,root,valid,active,certified⟩
      cases active with
      | nil => rfl
      | cons first rest => cases rest with
        | nil => rfl
        | cons second tail =>
            simp only [stepPlanWithWritesAt,BinaryPackedLoopPlan.stepPlanWithWritesAt,
              afterCoinPlanWithWritesAt,BinaryPackedLoopPlan.afterCoinPlanWithWritesAt,backend.compat]
            split
            · rename_i hNone
              simp only [hNone]
            · rename_i branch hSome
              simp only [hSome,ih]

theorem loop_price (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (fuel : List (Address capacity.width capacity.cap)) (state : Finished capacity n hCount)
    (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value) (depth : ℕ) :
    (loopPlanWithWritesAt seed limits hC backend fuel state pc hp depth).2 ≤
      25*payload (loopPlanWithWritesAt seed limits hC backend fuel state pc hp depth).1.1.1.1.1.1.2 := by
  induction fuel generalizing state pc depth with
  | nil => simp only [loopPlanWithWritesAt,payload,List.length_cons,List.length_nil]; omega
  | cons marker fuel ih =>
      unfold loopPlanWithWritesAt stepPlanWithWritesAt afterCoinPlanWithWritesAt
      dsimp only
      split
      · rename_i first second tail he
        let prepared := BinaryPackedLoopPlan.prepare limits hC state first second tail he
        let coin := draw seed prepared.1.data.outputs.probability pc hp
        split
        · simp only [payload,List.length_cons,List.length_nil]; omega
        · rename_i branch hSome
          let selected := backend.run state first second tail he prepared.1.data.outputs prepared.1.data.valid branch
          have hs := backend.bound state first second tail he prepared.1.data.outputs prepared.1.data.valid branch
          have hl := ih selected.1.1.data.value coin.data.cursor coin.data.bounded (depth+2)
          dsimp only [selected,coin,prepared] at hl hs
          simp only [payload,List.length_cons,List.length_nil]
          omega
      · simp only [payload,List.length_cons,List.length_nil]; omega

def runPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) := loopPlanWithWritesAt seed limits hC backend state.active state pc hp depth

theorem run_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC backend state pc hp depth).1 = BinaryPackedLoopPlan.runPlanWithReadsAt seed limits hC state pc hp depth :=
  loop_compat seed limits hC backend state.active state pc hp depth

theorem run_price (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (backend : Backend (hCount := hCount) limits hC)
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC backend state pc hp depth).2 ≤
      25*payload (runPlanAt seed limits hC backend state pc hp depth).1.1.1.1.1.1.2 :=
  loop_price seed limits hC backend state.active state pc hp depth

end Blotto.BinarySelectPriceContinuation
