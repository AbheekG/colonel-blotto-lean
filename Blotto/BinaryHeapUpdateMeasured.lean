import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryHeapWriteMeasured
import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryQuadraticMeasured
import Blotto.BinaryHeapScanMeasured
import Blotto.BinaryPRGHeapLoopLifetime

/-! The actual local physical update joins both operand reads, add/subtract,
two persistent writes and the reached rescan. Its old value/trace/source work
are exact. Actual opcode division work and write-address reversals return
separately; their joint ledger also pays the two-write sequence control.
The named extras have a factor-five bound against the old update charge.
Native observer/reference/allocator evaluation remains separate. -/
namespace Blotto.BinaryHeapUpdateMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 1000000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

theorem two_reversals_le_patch {depth : ℕ} (data : Packed depth)
    (first second : FixedBinaryWord depth) (chosen other : SignedWord) :
    (BinaryHeapWriteMeasured.execute data [(first,chosen),(second,other)]).2.2 ≤
      (BinaryHeapWriteMeasured.execute data [(first,chosen),(second,other)]).2.1.work-9 := by
  have hFirst := BinaryHeapWriteMeasured.writePlanAt_reversal_le_charge data first chosen 1
  have hSecond := BinaryHeapWriteMeasured.writePlanAt_reversal_le_charge
    (BinaryHeapWriteMeasured.writePlanAt data first chosen 1).1.1 second other 2
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryHeapWriteMeasured.execute,BinaryHeapWriteMeasured.executeAtMeasured,
    BinaryHeapWriteMeasured.executePlanAt,Nat.zero_add,Nat.reduceAdd]
  omega

def updateMeasuredReference (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ :=
  let a := BinaryHeapPackedReadMeasured.read state.packed first.word
  let b := BinaryHeapPackedReadMeasured.read state.packed second.word
  let total := BinaryPlannedQuadratic.applyMeasured .add a.1.1 b.1.1
  let other := BinaryPlannedQuadratic.applyMeasured .sub total.1.1.1 chosen
  let next := BinaryHeapWriteMeasured.execute state.packed [(first.word,chosen),(second.word,other.1.1.1)]
  let retained := BinaryHeapScanMeasured.scan limits next.1.1 [first,second]
  ((((next.1.1,retained.1.1++tail),wrapList (2+retained.1.1.length) 32 2
      [a.1.2,b.1.2,total.1.1.2,other.1.1.2,next.1.2,retained.1.2]),
    (a.2+b.2+total.1.2+other.1.2+(next.2.1.work-9)+retained.2.2+
      2*(first.word.bits.length+1)*(tail.length+2)+12,next.2.2)),total.2+other.2)


def updateTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : ((((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ) × ℕ :=
  let a := BinaryHeapPackedReadMeasured.read state.packed first.word
  let b := BinaryHeapPackedReadMeasured.read state.packed second.word
  let total := BinaryPlannedQuadratic.applyMeasured .add a.1.1 b.1.1
  let other := BinaryPlannedQuadratic.applyMeasured .sub total.1.1.1 chosen
  let written := BinaryHeapWriteMeasured.executeAtMeasured state.packed [(first.word,chosen),(second.word,other.1.1.1)] 0
  let next := written.1
  let retained := BinaryHeapScanMeasured.scan limits next.1.1 [first,second]
  (((((next.1.1,retained.1.1++tail),wrapList (2+retained.1.1.length) 32 2
      [a.1.2,b.1.2,total.1.1.2,other.1.1.2,next.1.2,retained.1.2]),
    (a.2+b.2+total.1.2+other.1.2+(next.2.1.work-9)+retained.2.2+
      2*(first.word.bits.length+1)*(tail.length+2)+12,next.2.2)),total.2+other.2),written.2)

def updateMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ)) × ℕ :=
  (updateTraceMeasured limits state first second tail chosen).1

theorem updateMeasured_eq_reference (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : updateMeasured limits state first second tail chosen =
      updateMeasuredReference limits state first second tail chosen := rfl


def update (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : ((Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace) × (ℕ × ℕ) :=
  (updateMeasured limits state first second tail chosen).1

theorem updateMeasured_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (updateMeasured limits state first second tail chosen).1 =
      update limits state first second tail chosen := rfl

theorem update_erases (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).1 = BinaryPRGHeapUpdateLifetime.updateWithTrace limits state first second tail chosen := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,updateMeasured_eq_reference,updateMeasuredReference,BinaryQuadraticMeasured.applyMeasured_compat,
    BinaryPRGHeapUpdateLifetime.updateWithTrace,BinaryHeapPackedReadMeasured.read_erases,
    BinaryQuadraticMeasured.apply_erases,BinaryHeapWriteMeasured.execute_erases,BinaryHeapScanMeasured.scan_trace]

theorem update_data (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).1.1 = (BinaryPRGHeapResourceLoop.updateWithWork limits state first second tail chosen).1 := by
  rw [update_erases,BinaryPRGHeapUpdateLifetime.updateWithTrace_erasure]

theorem update_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).2.1 = (BinaryPRGHeapResourceLoop.updateWithWork limits state first second tail chosen).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,updateMeasured_eq_reference,updateMeasuredReference,BinaryQuadraticMeasured.applyMeasured_compat,
    BinaryPRGHeapResourceLoop.updateWithWork,
    BinaryHeapPackedReadMeasured.read_data,BinaryHeapPackedReadMeasured.read_work,
    BinaryQuadraticMeasured.apply_data,BinaryQuadraticMeasured.apply_work,
    BinaryHeapWriteMeasured.execute_data,BinaryHeapWriteMeasured.execute_charge,
    BinaryPRGHeapWriteSequence.executeWithWork,BinaryHeapScanMeasured.scan_work]
  omega

theorem update_reversals_le_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).2.2 ≤ (update limits state first second tail chosen).2.1 := by
  have h := two_reversals_le_patch state.packed first.word second.word chosen
    (BinaryQuadraticMeasured.apply .sub
      (BinaryQuadraticMeasured.apply .add
        (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
        (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1).1.1 chosen).1.1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,updateMeasured_eq_reference,updateMeasuredReference,BinaryQuadraticMeasured.applyMeasured_compat]
  omega

theorem update_with_reversals_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).2.1+(update limits state first second tail chosen).2.2 ≤
      2*(BinaryPRGHeapResourceLoop.updateWithWork limits state first second tail chosen).2 := by
  have h := update_reversals_le_work limits state first second tail chosen
  rw [← update_work]
  omega

theorem update_write_overhead_le_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (update limits state first second tail chosen).2.2+9 ≤ (update limits state first second tail chosen).2.1 := by
  have h := two_reversals_le_patch state.packed first.word second.word chosen
    (BinaryQuadraticMeasured.apply .sub
      (BinaryQuadraticMeasured.apply .add
        (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
        (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1).1.1 chosen).1.1
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,updateMeasured_eq_reference,updateMeasuredReference,BinaryQuadraticMeasured.applyMeasured_compat]
  omega

variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

set_option cleanup.letToHave false in
def selectMeasuredReference (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : ((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ :=
  let chosen := if branch then outputs.upper else outputs.lower
  let selected := updateMeasured limits state first second tail chosen
  (((⟨selected.1.1.1.1.ruler,selected.1.1.1.1.size,selected.1.1.1.1.heap,selected.1.1.1.1.root,
    selected.1.1.1.1.valid,selected.1.1.1.2,by
      rw [updateMeasured_compat,update_data]
      exact (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).1.certified⟩,
    wrap 16 2 [selected.1.1.2]),selected.1.2),selected.2)


set_option cleanup.letToHave false in
def selectTraceMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : (((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ) × ℕ :=
  let chosen := if branch then outputs.upper else outputs.lower
  let produced := updateTraceMeasured limits state first second tail chosen
  let selected := produced.1
  have hSelected : selected = updateMeasured limits state first second tail chosen := rfl
  ((((⟨selected.1.1.1.1.ruler,selected.1.1.1.1.size,selected.1.1.1.1.heap,selected.1.1.1.1.root,
    selected.1.1.1.1.valid,selected.1.1.1.2,by
      rw [hSelected,updateMeasured_compat,update_data]
      exact (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).1.certified⟩,
    wrap 16 2 [selected.1.1.2]),selected.1.2),selected.2),produced.2)

def selectMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : ((Finished capacity n hCount × Trace) × (ℕ × ℕ)) × ℕ :=
  (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1

theorem selectMeasured_eq_reference (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch =
      selectMeasuredReference (hC := hC) limits state first second tail he outputs hOutputs branch := rfl


def select (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : (Finished capacity n hCount × Trace) × (ℕ × ℕ) :=
  (selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1

theorem selectMeasured_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1 =
      select (hC := hC) limits state first second tail he outputs hOutputs branch := rfl

theorem select_erases (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).1 =
      BinaryPRGHeapLoopLifetime.selectWithTrace (hC := hC) limits state first second tail he outputs hOutputs branch := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,select,selectMeasured_eq_reference,selectMeasuredReference,updateMeasured_compat,BinaryPRGHeapLoopLifetime.selectWithTrace,update_erases]

theorem select_data (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).1.1 =
      (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).1 := by
  rw [select_erases,BinaryPRGHeapLoopLifetime.selectWithTrace_erasure]

theorem select_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.1 =
      (BinaryPRGHeapResourceLoop.selectWithWork (hC := hC) limits state first second tail he outputs hOutputs branch).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,select,selectMeasured_eq_reference,selectMeasuredReference,updateMeasured_compat,BinaryPRGHeapResourceLoop.selectWithWork,update_work]

theorem select_progress (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).1.1.active.length < state.active.length := by
  rw [select_data]
  exact BinaryPRGHeapResourceLoop.selectWithWork_progress (hC := hC) limits state first second tail he outputs hOutputs branch

theorem select_reversals_le_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.2 ≤
      (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.1 :=
  update_reversals_le_work limits state first second tail _

theorem select_write_overhead_le_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.2+9 ≤
      (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.1 :=
  update_write_overhead_le_work limits state first second tail _

theorem updateMeasured_division_work_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateMeasured limits state first second tail chosen).2 ≤
      4*(update limits state first second tail chosen).2.1 := by
  have hTotal := BinaryQuadraticMeasured.applyMeasured_division_work_bound .add
    (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
    (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1
  have hOther := BinaryQuadraticMeasured.applyMeasured_division_work_bound .sub
    (BinaryQuadraticMeasured.applyMeasured .add
      (BinaryHeapPackedReadMeasured.read state.packed first.word).1.1
      (BinaryHeapPackedReadMeasured.read state.packed second.word).1.1).1.1.1 chosen
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,BinaryQuadraticMeasured.apply] at hTotal hOther
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,update,updateMeasured_eq_reference,updateMeasuredReference]
  omega

theorem updateMeasured_extras_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateMeasured limits state first second tail chosen).2+
      (update limits state first second tail chosen).2.2+9 ≤
      5*(update limits state first second tail chosen).2.1 := by
  have hd := updateMeasured_division_work_bound limits state first second tail chosen
  have hw := update_write_overhead_le_work limits state first second tail chosen
  omega

theorem selectMeasured_division_work_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).2 ≤
      4*(select (hC := hC) limits state first second tail he outputs hOutputs branch).2.1 :=
  updateMeasured_division_work_bound limits state first second tail _

theorem selectMeasured_extras_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) :
    (selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).2+
      (select (hC := hC) limits state first second tail he outputs hOutputs branch).2.2+9 ≤
      5*(select (hC := hC) limits state first second tail he outputs hOutputs branch).2.1 :=
  updateMeasured_extras_bound limits state first second tail _

theorem updateTraceMeasured_write_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (updateTraceMeasured limits state first second tail chosen).2 ≤
      32*(updateMeasured limits state first second tail chosen).1.2.1 := by
  let a := BinaryHeapPackedReadMeasured.read state.packed first.word
  let b := BinaryHeapPackedReadMeasured.read state.packed second.word
  let total := BinaryQuadraticMeasured.applyMeasured .add a.1.1 b.1.1
  let other := BinaryQuadraticMeasured.applyMeasured .sub total.1.1.1 chosen
  have h := BinaryHeapWriteMeasured.executeAtMeasured_emission state.packed
    [(first.word,chosen),(second.word,other.1.1.1)] 0
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,updateMeasured,updateTraceMeasured,BinaryHeapWriteMeasured.execute]
  dsimp only [a,b,total,other] at h
  omega

theorem selectTraceMeasured_write_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) (outputs : BinaryPRGWordControllerPairOutputs.Outputs)
    (hOutputs : outputs = (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs)
    (branch : Bool) : (selectTraceMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).2 ≤
      32*(selectMeasured (hC := hC) limits state first second tail he outputs hOutputs branch).1.2.1 := by
  have h := updateTraceMeasured_write_bound limits state first second tail
    (if branch then outputs.upper else outputs.lower)
  simpa only [selectTraceMeasured,selectMeasured,updateMeasured] using h

end Blotto.BinaryHeapUpdateMeasured
