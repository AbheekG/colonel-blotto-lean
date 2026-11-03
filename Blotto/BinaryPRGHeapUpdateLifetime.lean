import Blotto.BinaryPRGHeapScanLifetime
import Blotto.BinaryQuadraticLifetime

/-! The selected physical update retains traced operand reads, exact Boolean
arithmetic, both persistent writes and the two-address rescan. -/

namespace Blotto.BinaryPRGHeapUpdateLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (Packed)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}

theorem applyWithTrace_work (op : RealArithmeticOp) (a b : SignedWord) :
    (BinaryQuadraticLifetime.applyWithTrace op a b).1 = (BinaryQuadraticOpcode.applyWithWork op a b).1 :=
  (BinaryQuadraticLifetime.applyWithTrace_erases op a b).trans (BinaryQuadraticData.apply_erasure op a b).symm

def writesEnvelope (H depth : ℕ) : ℕ :=
  2 * (BinaryPRGHeapPackedLifetime.writeReservation H depth + 16) + 8 +
    BinaryPRGWordStoreHeapMachine.patchBound H depth + depth + 15

theorem twoWrites_usage {depth : ℕ} (data : Packed depth) (first second : FixedBinaryWord depth)
    (chosen other : SignedWord) (W P H : ℕ) (hChosen : width chosen ≤ W) (hOther : width other ≤ W)
    (hP : 0 < P)
    (hSpace : data.heap.tape.length + BinaryPRGHeapResourceUpdateBudget.growth depth W P ≤ H)
    (hRoom : H < 2^P) :
    usage (BinaryPRGHeapWriteLifetime.executeWithTrace data [(first,chosen),(second,other)]).2 ≤ writesEnvelope H depth := by
  let trace := (BinaryPRGHeapWriteLifetime.executeWithTrace data [(first,chosen),(second,other)]).2
  have h := BinaryPRGHeapWriteLifetime.selected_twoWrites_all_prefix data first second chosen other
    W P H hChosen hOther hP hSpace hRoom 0 trace.length
  change retainedHeap 0 trace trace.length ≤ _ ∧ framePeak (trace.take trace.length) ≤ _ at h
  simp only [retainedHeap,List.take_length,Nat.zero_add] at h
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells writesEnvelope
  change listCells trace + arraySlots trace + framePeak trace ≤ _
  omega

def updateWithTrace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) : (Packed capacity.width × List (Address capacity.width capacity.cap)) × Trace :=
  let a := BinaryPRGHeapPackedLifetime.readWithTrace state.packed first.word
  let b := BinaryPRGHeapPackedLifetime.readWithTrace state.packed second.word
  let total := BinaryQuadraticLifetime.applyWithTrace .add a.1 b.1
  let other := BinaryQuadraticLifetime.applyWithTrace .sub total.1 chosen
  let next := BinaryPRGHeapWriteLifetime.executeWithTrace state.packed [(first.word,chosen),(second.word,other.1)]
  let retained := BinaryPRGHeapScanLifetime.scanWithTrace limits next.1 [first,second]
  ((next.1,retained.1 ++ tail),wrapList (2 + retained.1.length) 32 2
    [a.2,b.2,total.2,other.2,next.2,retained.2])

theorem updateWithTrace_erasure (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) :
    (updateWithTrace limits state first second tail chosen).1 =
      (BinaryPRGHeapResourceLoop.updateWithWork limits state first second tail chosen).1 := by
  simp only [updateWithTrace,BinaryPRGHeapResourceLoop.updateWithWork,
    BinaryPRGHeapPackedLifetime.readWithTrace_erasure,applyWithTrace_work,
    BinaryPRGHeapWriteLifetime.executeWithTrace_erasure,BinaryPRGHeapWriteSequence.executeWithWork,
    BinaryPRGHeapScanLifetime.scanWithTrace_erasure]

def updateEnvelope (C H depth W : ℕ) : ℕ :=
  2 * readEnvelope H depth + 2 * (BinaryQuadraticLifetime.opcodeBound W + BinaryQuadraticLifetime.opcodeFrames W) +
    writesEnvelope H depth + BinaryPRGHeapScanLifetime.scanEnvelope C H depth W 2 + 64

theorem updateWithTrace_usage (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (chosen : SignedWord) (C H W P : ℕ) (hC : limits.heap.tape.length ≤ C) (hW : 1 ≤ W) (hP : 0 < P)
    (hSpace : state.heap.tape.length + BinaryPRGHeapResourceUpdateBudget.growth capacity.width W P ≤ H)
    (hRoom : H < 2^P)
    (hOld : ∀ address : Address capacity.width capacity.cap,width (state.packed.readWithWork address.word).1 ≤ W)
    (hLimit : ∀ address : Address capacity.width capacity.cap,width (BinaryPRGHeapStoredTree.readWithWork limits address.word).1 ≤ W)
    (hChosen : width chosen ≤ W) :
    let a := state.packed.readWithWork first.word
    let b := state.packed.readWithWork second.word
    let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
    let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
    let next := ((state.packed.writeWithWork first.word chosen).1.writeWithWork second.word other.1).1
    width total.1 ≤ W → width other.1 ≤ W →
      (∀ address : Address capacity.width capacity.cap,width (next.readWithWork address.word).1 ≤ W) →
      usage (updateWithTrace limits state first second tail chosen).2 ≤ updateEnvelope C H capacity.width W := by
  dsimp only
  intro hTotal hOther hNext
  let a := state.packed.readWithWork first.word
  let b := state.packed.readWithWork second.word
  let total := BinaryQuadraticOpcode.applyWithWork .add a.1 b.1
  let other := BinaryQuadraticOpcode.applyWithWork .sub total.1 chosen
  let next := ((state.packed.writeWithWork first.word chosen).1.writeWithWork second.word other.1).1
  have hHeap : state.packed.heap.tape.length ≤ H := by change state.heap.tape.length ≤ H; omega
  have hWrites := BinaryPRGHeapResourceUpdateBudget.twoWrites_controlled state.packed first.word second.word
    chosen other.1 W P H hChosen hOther hP hSpace hRoom
  have hNextHeap : next.heap.tape.length ≤ H := hWrites.1.trans hSpace
  have hA := read_usage state.packed first.word H hHeap
  have hB := read_usage state.packed second.word H hHeap
  have hAdd := BinaryQuadraticLifetime.applyWithTrace_bounds .add a.1 b.1 W (hOld first) (hOld second)
  have hSub := BinaryQuadraticLifetime.applyWithTrace_bounds .sub total.1 chosen W hTotal hChosen
  have hWriteUsage := twoWrites_usage state.packed first.word second.word chosen other.1 W P H
    hChosen hOther hP hSpace hRoom
  have hScan := BinaryPRGHeapScanLifetime.scanWithTrace_usage limits next [first,second] C H W hC hNextHeap hW hNext hLimit
  have hLength : (BinaryPRGHeapScanLifetime.scanWithTrace limits next [first,second]).1.length ≤ 2 := by
    rw [BinaryPRGHeapScanLifetime.scanWithTrace_erasure]
    rw [BinaryPRGHeapResourceLoop.scanWithWork_value limits next
      (BinaryPRGHeapPackedStore.Packed.writeWithWork_realizes _
        (BinaryPRGHeapPackedStore.Packed.writeWithWork_realizes _ state.packed_realizes first.word chosen) second.word other.1)]
    exact (List.length_filter_le _ _).trans_eq (by simp)
  have hw := wrapList_usage (2 + (BinaryPRGHeapScanLifetime.scanWithTrace limits next [first,second]).1.length) 32 2
    [(BinaryPRGHeapPackedLifetime.readWithTrace state.packed first.word).2,
      (BinaryPRGHeapPackedLifetime.readWithTrace state.packed second.word).2,
      (BinaryQuadraticLifetime.applyWithTrace .add a.1 b.1).2,
      (BinaryQuadraticLifetime.applyWithTrace .sub total.1 chosen).2,
      (BinaryPRGHeapWriteLifetime.executeWithTrace state.packed [(first.word,chosen),(second.word,other.1)]).2,
      (BinaryPRGHeapScanLifetime.scanWithTrace limits next [first,second]).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  unfold updateWithTrace
  simp only [BinaryPRGHeapPackedLifetime.readWithTrace_erasure,applyWithTrace_work,
    BinaryPRGHeapWriteLifetime.executeWithTrace_erasure,BinaryPRGHeapWriteSequence.executeWithWork]
  change usage (wrapList (2 + (BinaryPRGHeapScanLifetime.scanWithTrace limits next [first,second]).1.length) 32 2
    [(BinaryPRGHeapPackedLifetime.readWithTrace state.packed first.word).2,
      (BinaryPRGHeapPackedLifetime.readWithTrace state.packed second.word).2,
      (BinaryQuadraticLifetime.applyWithTrace .add a.1 b.1).2,
      (BinaryQuadraticLifetime.applyWithTrace .sub total.1 chosen).2,
      (BinaryPRGHeapWriteLifetime.executeWithTrace state.packed [(first.word,chosen),(second.word,other.1)]).2,
      (BinaryPRGHeapScanLifetime.scanWithTrace limits next [first,second]).2]) ≤ _
  unfold updateEnvelope usage BinaryPRGHeapPrimitiveLifetime.cells at *
  simp only [List.length_cons,List.length_nil,Nat.reduceAdd] at hScan
  omega

end Blotto.BinaryPRGHeapUpdateLifetime
