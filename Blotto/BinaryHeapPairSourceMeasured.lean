import Blotto.BinaryHeapPackedReadMeasured
import Blotto.BinaryHeapPairRegistersMeasured
import Blotto.BinaryPRGHeapPairLifetime

/-! The actual four physical reads feed a single measured pair register run.
Every returned old value/trace/source charge is exact, and actual opcode
division charges pass through the returned pair. Logical source witnesses
are erased; native observer/reference/allocator costs remain separate. -/
namespace Blotto.BinaryHeapPairSourceMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapPackedStore (pack)
open BinaryPRGHeapResourceLoop (Finished)
open BinaryPRGHeapTraceUsage
set_option autoImplicit false
set_option maxHeartbeats 2500000

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,CanonicalWord (lookup capacity.tree address.word)}

def source (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first :: second :: tail) : (BinaryRationalPairProgram.Source × Trace) × ℕ :=
  let a := BinaryHeapPackedReadMeasured.read (pack limits) first.word
  let b := BinaryHeapPackedReadMeasured.read (pack limits) second.word
  let c := BinaryHeapPackedReadMeasured.read state.packed first.word
  let d := BinaryHeapPackedReadMeasured.read state.packed second.word
  have hA := (BinaryHeapPackedReadMeasured.read_data (pack limits) first.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits first.word)
  have hB := (BinaryHeapPackedReadMeasured.read_data (pack limits) second.word).trans
    (BinaryPRGHeapStoredTree.readWithWork_value limits second.word)
  have hCRead := (BinaryHeapPackedReadMeasured.read_data state.packed first.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes first.word)
  have hD := (BinaryHeapPackedReadMeasured.read_data state.packed second.word).trans
    (BinaryPRGHeapPackedStore.Packed.readWithWork_value state.packed state.packed_realizes second.word)
  have hActive : state.reference.state.active = first :: second :: tail :=
    state.certified.choose_spec.2.symm.trans he
  ((⟨a.1.1,b.1.1,c.1.1,d.1.1,
    (by rw [hA]; exact hC first),(by rw [hB]; exact hC second),
    (by rw [hCRead]; exact state.reference.canonical first),(by rw [hD]; exact state.reference.canonical second),
    (by rw [hCRead,hA]; exact state.reference.interior first (by
      rw [hActive]; simp)),
    (by rw [hD,hB]; exact state.reference.interior second (by
      rw [hActive]; simp))⟩,
    wrap 32 2 [a.1.2,b.1.2,c.1.2,d.1.2]),a.2+b.2+c.2+d.2+8)


theorem source_erases (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (source (hC := hC) limits state first second tail he).1 =
      BinaryPRGHeapPairLifetime.sourceWithTrace (hC := hC) limits state first second tail he := by
  simp only [source,BinaryPRGHeapPairLifetime.sourceWithTrace,BinaryHeapPackedReadMeasured.read_erases]

theorem source_data (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (source (hC := hC) limits state first second tail he).1.1 =
      (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).1 := by
  rw [source_erases,BinaryPRGHeapPairLifetime.sourceWithTrace_erasure]

theorem source_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (source (hC := hC) limits state first second tail he).2 =
      (BinaryPRGHeapResourceLoop.sourceWithWork (hC := hC) limits state first second tail he).2 := by
  simp only [source,BinaryPRGHeapResourceLoop.sourceWithWork,BinaryHeapPackedReadMeasured.read_work]
  rfl

@[irreducible] def pairMeasured (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : ((BinaryPRGWordControllerPairOutputs.Outputs × Trace) × ℕ) × ℕ :=
  let input := source (hC := hC) limits state first second tail he
  let outputs := BinaryHeapPairRegistersMeasured.outputsMeasured input.1.1
  (((outputs.1.1.1,wrap 16 2 [input.1.2,outputs.1.1.2]),
    input.2+input.1.1.sourcePayloadWork+outputs.1.2+4),outputs.2)

@[irreducible] def pair (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : (BinaryPRGWordControllerPairOutputs.Outputs × Trace) × ℕ :=
  (pairMeasured (hC := hC) limits state first second tail he).1

theorem pairMeasured_compat (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pairMeasured (hC := hC) limits state first second tail he).1 =
      pair (hC := hC) limits state first second tail he := by rw [pair]

theorem pair_erases (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pair (hC := hC) limits state first second tail he).1 =
      BinaryPRGHeapPairLifetime.pairWithTrace (hC := hC) limits state first second tail he := by
  simp only [pair,pairMeasured,BinaryHeapPairRegistersMeasured.outputsMeasured_compat,
    BinaryPRGHeapPairLifetime.pairWithTrace,source_erases,BinaryHeapPairRegistersMeasured.outputs_erases]

theorem pair_data (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pair (hC := hC) limits state first second tail he).1.1 =
      (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits state first second tail he).1 := by
  rw [pair_erases,BinaryPRGHeapPairLifetime.pairWithTrace_erasure]

theorem pair_work (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pair (hC := hC) limits state first second tail he).2 =
      (BinaryPRGHeapResourceLoop.pairWithWork (hC := hC) limits state first second tail he).2 := by
  simp only [pair,pairMeasured,BinaryHeapPairRegistersMeasured.outputsMeasured_compat,
    BinaryPRGHeapResourceLoop.pairWithWork,source_data,source_work,BinaryHeapPairRegistersMeasured.outputs_work]

theorem pairMeasured_division_work_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pairMeasured (hC := hC) limits state first second tail he).2 ≤
      4*(pair (hC := hC) limits state first second tail he).2 := by
  have h := BinaryHeapPairRegistersMeasured.outputsMeasured_division_work_bound
    (source (hC := hC) limits state first second tail he).1.1
  simp only [BinaryHeapPairRegistersMeasured.outputs] at h
  simp only [pair,pairMeasured]
  omega

theorem pair_value (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    (pair (hC := hC) limits state first second tail he).1.1 =
      (BinaryPRGHeapResourceLoop.logicalChoice (hC := hC) state first second tail he).outputs :=
  (pair_data (hC := hC) limits state first second tail he).trans
    (BinaryPRGHeapResourceLoop.pairWithWork_value (hC := hC) limits state first second tail he)

end Blotto.BinaryHeapPairSourceMeasured
