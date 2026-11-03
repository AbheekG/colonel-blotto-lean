import Blotto.BinaryPackedPairPlan
import Blotto.BinaryPrimitiveScanPlan
import Blotto.BinaryHeapUpdateMeasured
import Blotto.BinaryHeapWriteMeasured
import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryResourceOpcodePlan
import Blotto.BinaryHeapScanMeasured
import Blotto.BinaryPRGHeapLoopLifetime

/-! Actual packed-read plans and the reached planned rescan feed updates.
Preceding update/selection records and write/division/reversal counters are exact.
Reached read/rescan/wrapper and planned opcode emissions are returned in the
existing resource-loop counter; all existing bounds keep their constants. -/
namespace Blotto.BinaryPackedUpdatePlan
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

theorem scan_compat (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (BinaryPrimitiveScanPlan.scanWithEmission limits bids addresses).1.1 = BinaryHeapScanMeasured.scan limits bids addresses := by
  rw [BinaryPrimitiveScanPlan.scanWithEmission_compat,BinaryInitialScanPlan.scanWithEmission_compat]

theorem scan_price (limits : Stored capacity.tree) (bids : Packed capacity.width)
    (addresses : List (Address capacity.width capacity.cap)) :
    (BinaryPrimitiveScanPlan.scanWithEmission limits bids addresses).1.2+
      (BinaryPrimitiveScanPlan.scanWithEmission limits bids addresses).2 ≤
      50*(BinaryPrimitiveScanPlan.scanWithEmission limits bids addresses).1.1.1.2.length+5 := by
  have hr := BinaryInitialScanPlan.scanWithEmission_bound limits bids addresses
  have hl := BinaryPrimitiveScanPlan.scanWithEmission_price limits bids addresses
  rw [← BinaryPrimitiveScanPlan.scanWithEmission_compat] at hr
  omega

@[irreducible] def updateTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (((((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ :=
  let ap := BinaryPackedReadPlan.readWithEmission state.packed first.word
  let a := ap.1
  let bp := BinaryPackedReadPlan.readWithEmission state.packed second.word
  let b := bp.1
  let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
  let total := arithmetic.1.1
  let other := arithmetic.1.2
  let written := BinaryHeapWriteMeasured.executeAtMeasured state.packed [(first.word,chosen),(second.word,other.1.1.1)] 0
  let next := written.1
  let scanned := BinaryPrimitiveScanPlan.scanWithEmission limits next.1.1 [first,second]
  let retained := scanned.1.1
  let emitted := six (2+retained.1.1.length) a.1.2 b.1.2 total.1.1.2 other.1.1.2 next.1.2 retained.1.2
  ((((((next.1.1,retained.1.1++tail),emitted.1),
    (a.2+b.2+total.1.2+other.1.2+(next.2.1.work-9)+retained.2.2+
      2*(first.word.bits.length+1)*(tail.length+2)+12,next.2.2)),total.2+other.2),written.2),ap.2+bp.2+scanned.1.2+scanned.2+emitted.2+arithmetic.2)

theorem update_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateTraceMeasured limits state first second tail chosen).1 =
      BinaryHeapUpdateMeasured.updateTraceMeasured limits state first second tail chosen := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,updateTraceMeasured,BinaryHeapUpdateMeasured.updateTraceMeasured,
    BinaryPackedReadPlan.read_compat,scan_compat,six_trace,BinaryResourceOpcodePlan.pair_compat]

theorem update_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateTraceMeasured limits state first second tail chosen).2 ≤
      100*(updateTraceMeasured limits state first second tail chosen).1.1.1.1.2.length := by
  let a := (BinaryPackedReadPlan.readWithEmission state.packed first.word).1
  let b := (BinaryPackedReadPlan.readWithEmission state.packed second.word).1
  let arithmetic := BinaryResourceOpcodePlan.pair a.1.1 b.1.1 chosen
  let total := arithmetic.1.1
  let other := arithmetic.1.2
  let written := BinaryHeapWriteMeasured.executeAtMeasured state.packed [(first.word,chosen),(second.word,other.1.1.1)] 0
  let retained := (BinaryPrimitiveScanPlan.scanWithEmission limits written.1.1.1 [first,second]).1.1
  have ha := BinaryPackedReadPlan.read_emission_bound state.packed first.word
  have hb := BinaryPackedReadPlan.read_emission_bound state.packed second.word
  have hs := scan_price limits written.1.1.1 [first,second]
  have hp := BinaryResourceOpcodePlan.pair_price a.1.1 b.1.1 chosen
  have hw := six_price (2+retained.1.1.length) a.1.2 b.1.2 total.1.1.2 other.1.1.2 written.1.1.2 retained.1.2
  simp only [six_length] at hw
  simp only [updateTraceMeasured,six_length]
  dsimp only [a,b,arithmetic,total,other,written,retained] at hw hs hp
  omega


variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def finishSelection (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool)
    (produced : ((((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ) × ℕ)
    (hProduced : produced = BinaryHeapUpdateMeasured.updateTraceMeasured limits state first second tail
      (if branch then outputs.upper else outputs.lower)) :
    ((((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ :=
  let selected := produced.1
  have hSelected : selected = BinaryHeapUpdateMeasured.updateMeasured limits state first second tail
      (if branch then outputs.upper else outputs.lower) := by
    dsimp only [selected]
    rw [hProduced]
    rfl
  let emitted := BinaryWrapperEmission.one 16 2 selected.1.1.2
  (((((⟨selected.1.1.1.1.ruler,selected.1.1.1.1.size,selected.1.1.1.1.heap,selected.1.1.1.1.root,
    selected.1.1.1.1.valid,selected.1.1.1.2,by
      rw [hSelected,BinaryHeapUpdateMeasured.updateMeasured_compat,BinaryHeapUpdateMeasured.update_data]
      exact (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).1.certified⟩,
    emitted.1),selected.1.2),selected.2),produced.2),emitted.2)

@[irreducible] def selectTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    ((((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ) × ℕ) × ℕ :=
  let packed := updateTraceMeasured limits state first second tail (if branch then outputs.upper else outputs.lower)
  let finished := finishSelection (hC := hC) limits state first second tail he outputs hOutputs branch
    packed.1 (update_compat limits state first second tail _)
  (finished.1,packed.2+finished.2)

theorem select_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1 =
      BinaryHeapUpdateMeasured.selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch := by
  simp only [selectTraceMeasured,finishSelection,BinaryHeapUpdateMeasured.selectTraceMeasured,update_compat,BinaryWrapperEmission.one_trace]

theorem select_price (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).2 ≤
      150*(selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.1.1.2.length := by
  have h := update_price limits state first second tail (if branch then outputs.upper else outputs.lower)
  simp only [selectTraceMeasured,finishSelection,BinaryWrapperEmission.one_work,BinaryWrapperEmission.one_length]
  omega

end Blotto.BinaryPackedUpdatePlan
