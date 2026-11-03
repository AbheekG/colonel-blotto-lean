import Blotto.BinaryWriteLeafPlan
import Blotto.BinaryPackedUpdatePlan
import Blotto.BinaryPackedPairPlan
import Blotto.BinaryPrimitiveScanPlan
import Blotto.BinaryHeapUpdateMeasured
import Blotto.BinaryHeapWriteMeasured
import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryResourceOpcodePlan
import Blotto.BinaryHeapScanMeasured
import Blotto.BinaryPRGHeapLoopLifetime

/-! Actual emitted raw read/allocation leaves feed persistent writes used by
updates. The complete preceding data/trace/source/division/write record stays
exact. Reached planned opcode emissions join the existing packed counter;
write-leaf emissions remain separate and all old price bounds keep their constants. -/
namespace Blotto.BinaryWriteUpdatePlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
open BinaryPackedPairPlan (six six_trace six_length six_price)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option backward.isDefEq.respectTransparency true

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

@[irreducible] def updateTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : ((((((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) × ℕ :=
  let ap := BinaryPackedReadPlan.readWithEmission state.packed first.word
  let a := ap.1
  let bp := BinaryPackedReadPlan.readWithEmission state.packed second.word
  let b := bp.1
  let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
  let total := arithmetic.1.1
  let other := arithmetic.1.2
  let leaves := BinaryWriteLeafPlan.executeAtMeasured state.packed [(first.word,chosen),(second.word,other.1.1.1)] 0
  let written := leaves.1
  let next := written.1
  let scanned := BinaryPrimitiveScanPlan.scanWithEmission limits next.1.1 [first,second]
  let retained := scanned.1.1
  let emitted := six (2+retained.1.1.length) a.1.2 b.1.2 total.1.1.2 other.1.1.2 next.1.2 retained.1.2
  (((((((next.1.1,retained.1.1++tail),emitted.1),
    (a.2+b.2+total.1.2+other.1.2+(next.2.1.work-9)+retained.2.2+
      2*(first.word.bits.length+1)*(tail.length+2)+12,next.2.2)),total.2+other.2),written.2),ap.2+bp.2+scanned.1.2+scanned.2+emitted.2+arithmetic.2),leaves.2)

theorem update_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateTraceMeasured limits state first second tail chosen).1 = BinaryPackedUpdatePlan.updateTraceMeasured limits state first second tail chosen := by
  simp only [updateTraceMeasured,BinaryPackedUpdatePlan.updateTraceMeasured,BinaryWriteLeafPlan.execute_compat]

theorem update_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateTraceMeasured limits state first second tail chosen).2 ≤
      25*(updateTraceMeasured limits state first second tail chosen).1.1.1.1.1.2.length := by
  unfold updateTraceMeasured
  dsimp only
  refine (BinaryWriteLeafPlan.execute_price _ _ _).trans ?_
  simp only [six_length]
  omega


variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

@[irreducible] def selectTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (((((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ) × ℕ :=
  let packed := updateTraceMeasured limits state first second tail (if branch then outputs.upper else outputs.lower)
  let finished := BinaryPackedUpdatePlan.finishSelection (hC := hC) limits state first second tail he outputs hOutputs branch
    packed.1.1 (by rw [update_compat,BinaryPackedUpdatePlan.update_compat])
  ((finished.1,packed.1.2+finished.2),packed.2)

theorem select_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1 =
      BinaryPackedUpdatePlan.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch := by
  simp only [selectTraceMeasured,BinaryPackedUpdatePlan.selectTraceMeasured,update_compat]

theorem select_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).2 ≤
      25*(selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.1.1.1.2.length := by
  have h := update_price limits state first second tail (if branch then outputs.upper else outputs.lower)
  simp only [selectTraceMeasured,BinaryPackedUpdatePlan.finishSelection,BinaryWrapperEmission.one_length]
  omega

end Blotto.BinaryWriteUpdatePlan
