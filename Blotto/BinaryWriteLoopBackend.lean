import Blotto.BinarySelectPriceContinuation
import Blotto.BinaryWriteUpdatePlan

/-! The concrete selection backend consumes the actual write-leaf producer,
retains the full preceding packed selection/price and discharges the reusable
continuation's refinement and bound. No backend premise remains in run theorems. -/
namespace Blotto.BinaryWriteLoopBackend
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

@[irreducible] def select (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : (Selection state × ℕ) × ℕ :=
  let leaves := BinaryWriteUpdatePlan.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch
  let packed := leaves.1
  let measured := packed.1
  let produced := measured.1
  ((⟨⟨produced.1.1.1,produced.1.1.2,produced.1.2.1,by
    dsimp only [produced,measured,packed,leaves]
    rw [BinaryWriteUpdatePlan.select_compat,BinaryPackedUpdatePlan.select_compat]
    change (BinaryHeapUpdateMeasured.select (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.active.length < state.active.length
    exact BinaryHeapUpdateMeasured.select_progress (hC := hC) limits state first second tail he outputs hOutputs branch⟩,
    produced.2+produced.1.2.2+9,measured.2⟩,packed.2),leaves.2)

theorem select_compat (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).1 =
      BinaryPackedLoopPlan.select limits hC state first second tail he outputs hOutputs branch := by
  simp only [select,BinaryPackedLoopPlan.select,BinaryWriteUpdatePlan.select_compat]

theorem select_price (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select limits hC state first second tail he outputs hOutputs branch).2 ≤
      25*(select limits hC state first second tail he outputs hOutputs branch).1.1.data.trace.length := by
  simpa only [select] using BinaryWriteUpdatePlan.select_price (hC := hC) limits state first second tail he outputs hOutputs branch

def backend (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)) :
    BinarySelectPriceContinuation.Backend (hCount := hCount) limits hC where
  run := select limits hC
  compat := select_compat limits hC
  bound := select_price limits hC

def runPlanAt (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) := BinarySelectPriceContinuation.runPlanAt seed limits hC (backend limits hC) state pc hp depth

theorem run_compat (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC state pc hp depth).1 = BinaryPackedLoopPlan.runPlanWithReadsAt seed limits hC state pc hp depth :=
  BinarySelectPriceContinuation.run_compat seed limits hC (backend limits hC) state pc hp depth

theorem run_price (seed : BinarySeedLookupTree.Store) (limits : Stored capacity.tree)
    (hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word))
    (state : Finished capacity n hCount) (pc : FixedBinaryWord seed.width) (hp : pc.value ≤ seed.cap.value)
    (depth : ℕ) :
    (runPlanAt seed limits hC state pc hp depth).2 ≤
      25*payload (runPlanAt seed limits hC state pc hp depth).1.1.1.1.1.1.2 :=
  BinarySelectPriceContinuation.run_price seed limits hC (backend limits hC) state pc hp depth

end Blotto.BinaryWriteLoopBackend
