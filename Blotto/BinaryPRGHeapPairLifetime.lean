import Blotto.BinaryPRGHeapTraceUsage
import Blotto.BinaryPRGHeapResourceLoop
import Blotto.BinaryQuadraticResourcePairLifetime

/-! Physical resource pair preparation consumes four traced tape reads and
the actual quadratic register program; logical states occur only in proofs. -/

namespace Blotto.BinaryPRGHeapPairLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option maxHeartbeats 1500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def sourceWithTrace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : BinaryRationalPairProgram.Source × Trace :=
  let a := BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) first.word
  let b := BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) second.word
  let c := BinaryPRGHeapPackedLifetime.readWithTrace state.packed first.word
  let d := BinaryPRGHeapPackedLifetime.readWithTrace state.packed second.word
  have hA := (BinaryPRGHeapPackedLifetime.readWithTrace_erasure (pack limits) first.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits first.word)
  have hB := (BinaryPRGHeapPackedLifetime.readWithTrace_erasure (pack limits) second.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits second.word)
  have hCRead := (BinaryPRGHeapPackedLifetime.readWithTrace_erasure state.packed first.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes first.word)
  have hD := (BinaryPRGHeapPackedLifetime.readWithTrace_erasure state.packed second.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes second.word)
  have hActive : state.reference.state.active = first :: second :: tail :=
    state.certified.choose_spec.2.symm.trans he
  (⟨a.1,b.1,c.1,d.1,
    (by rw [hA]; exact hC first),(by rw [hB]; exact hC second),
    (by rw [hCRead]; exact state.reference.canonical first),(by rw [hD]; exact state.reference.canonical second),
    (by rw [hCRead,hA]; exact state.reference.interior first (by
      rw [hActive]; simp)),
    (by rw [hD,hB]; exact state.reference.interior second (by
      rw [hActive]; simp))⟩,
    wrap 32 2 [a.2,b.2,c.2,d.2])

theorem sourceWithTrace_erasure (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (sourceWithTrace (hC := hC) limits state first second tail he).1 =
      (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1 := by
  unfold sourceWithTrace BinaryPRGHeapResourceLoop.sourceWithWork
  dsimp only
  simp only [BinaryPRGHeapPackedLifetime.readWithTrace_erasure]
  rfl

theorem sourceWithTrace_usage (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (C H : ℕ)
    (hCHeap : limits.heap.tape.length ≤ C) (hH : state.heap.tape.length ≤ H) :
    usage (sourceWithTrace (hC := hC) limits state first second tail he).2 ≤
      2 * readEnvelope C capacity.width + 2 * readEnvelope H capacity.width + 42 := by
  have ha := read_usage (pack limits) first.word C hCHeap
  have hb := read_usage (pack limits) second.word C hCHeap
  have hc := read_usage state.packed first.word H hH
  have hd := read_usage state.packed second.word H hH
  have hWrap := wrap_usage 32 2
    [(BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) first.word).2,
      (BinaryPRGHeapPackedLifetime.readWithTrace (pack limits) second.word).2,
      (BinaryPRGHeapPackedLifetime.readWithTrace state.packed first.word).2,
      (BinaryPRGHeapPackedLifetime.readWithTrace state.packed second.word).2]
  unfold sourceWithTrace
  dsimp only
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  omega

def pairWithTrace (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : BinaryPRGWordControllerPairOutputs.Outputs × Trace :=
  let input := sourceWithTrace (hC := hC) limits state first second tail he
  let outputs := BinaryQuadraticResourcePairLifetime.outputsWithTrace input.1
  (outputs.1,wrap 16 2 [input.2,outputs.2])

theorem pairWithTrace_erasure (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) :
    (pairWithTrace (hC := hC) limits state first second tail he).1 =
      (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits state first second tail he).1 := by
  simp only [pairWithTrace,BinaryPRGHeapResourceLoop.pairWithWork,BinaryQuadraticResourcePairLifetime.outputsWithTrace_erases,
    sourceWithTrace_erasure,BinaryPRGWordControllerPairOutputs.prepareWithWork_erasure]

def pairEnvelope (C H depth W : ℕ) : ℕ :=
  2 * readEnvelope C depth + 2 * readEnvelope H depth +
    BinaryQuadraticResourcePairLifetime.outputsBound W + BinaryQuadraticResourcePairLifetime.outputsFrames W + 100

theorem pairWithTrace_usage (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) (C H W : ℕ)
    (hCHeap : limits.heap.tape.length ≤ C) (hH : state.heap.tape.length ≤ H)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code
      (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1.inputs W) :
    usage (pairWithTrace (hC := hC) limits state first second tail he).2 ≤ pairEnvelope C H capacity.width W := by
  let input := sourceWithTrace (hC := hC) limits state first second tail he
  have hSource := sourceWithTrace_usage (hC := hC) limits state first second tail he C H hCHeap hH
  have hTrace' : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code input.1.inputs W := by
    simpa only [input,sourceWithTrace_erasure] using hTrace
  have hOutputs := BinaryQuadraticResourcePairLifetime.outputsWithTrace_bounds input.1 W hTrace'
  have hWrap := wrap_usage 16 2 [input.2,(BinaryQuadraticResourcePairLifetime.outputsWithTrace input.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hWrap
  unfold pairWithTrace pairEnvelope
  change usage (wrap 16 2 [input.2,(BinaryQuadraticResourcePairLifetime.outputsWithTrace input.1).2]) ≤ _
  change usage input.2 ≤ _ at hSource
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells at *
  omega

end Blotto.BinaryPRGHeapPairLifetime
