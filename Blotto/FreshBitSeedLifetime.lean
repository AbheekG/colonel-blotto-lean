import Blotto.BinaryPRGHeapTraceUsage

/-! A named fresh-bit loop forms the actual seed list, in draw order. The
primitive returns one Boolean and its private state; it is called once per
iteration. All accumulator/reversal cells and source activations are retained.
The deterministic tape interpretation is a refinement, not a fairness premise.
The independent fair interpretation is supplied separately. Primitive internals,
native scalar/pointer layouts and observer materialization are outside this
source-cell model. -/
namespace Blotto.FreshBitSeedLifetime
open BinarySeedPreparationSpace BinaryPRGHeapTraceUsage

def loopWithTrace {S : Type*} (fresh : S → Bool × S) :
    ℕ → List Bool → S → (List Bool × S) × Trace
  | 0, reversed, state =>
      let result := reverseWithTrace reversed []
      ((result.1,state),wrap 8 1 [result.2])
  | count+1, reversed, state =>
      let bit := fresh state
      let next := loopWithTrace fresh count (bit.1::reversed) bit.2
      (next.1,wrapList 1 16 2 [next.2])

def generateWithTrace {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) :
    (List Bool × S) × Trace := loopWithTrace fresh count [] state

theorem loop_length {S : Type*} (fresh : S → Bool × S) (count : ℕ) (reversed : List Bool) (state : S) :
    (loopWithTrace fresh count reversed state).1.1.length = count+reversed.length := by
  induction count generalizing reversed state with
  | zero => simp [loopWithTrace,reverseWithTrace_result,List.reverseAux_eq]
  | succ count ih => simpa only [loopWithTrace,List.length_cons,Nat.add_assoc,Nat.add_comm 1 reversed.length] using ih ((fresh state).1::reversed) (fresh state).2

theorem generate_length {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) :
    (generateWithTrace fresh count state).1.1.length = count := by
  simpa only [generateWithTrace,List.length_nil,Nat.add_zero] using loop_length fresh count [] state

theorem list_of_length (seed : List Bool) (count : ℕ) (h : seed.length = count) :
    ∃ bits : Fin count → Bool,seed = List.ofFn bits := by
  subst count
  exact ⟨seed.get,(List.ofFn_get seed).symm⟩

theorem generate_ofFn {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) :
    ∃ bits : Fin count → Bool,(generateWithTrace fresh count state).1.1 = List.ofFn bits :=
  list_of_length _ count (generate_length fresh count state)

theorem reverse_usage (bits : List Bool) : usage (reverseWithTrace bits []).2 ≤ 2*bits.length+1 := by
  have hc := reverseWithTrace_cells bits []
  have ha := reverseWithTrace_arrays bits []
  have hf := reverseWithTrace_frames bits []
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells
  omega

theorem loop_usage {S : Type*} (fresh : S → Bool × S) (count : ℕ) (reversed : List Bool) (state : S) :
    usage (loopWithTrace fresh count reversed state).2 ≤ 24*count+2*reversed.length+16 := by
  induction count generalizing reversed state with
  | zero =>
      have hr := reverse_usage reversed
      have hw := wrap_usage 8 1 [(reverseWithTrace reversed []).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrap 8 1 [(reverseWithTrace reversed []).2]) ≤ _
      omega
  | succ count ih =>
      have hn := ih ((fresh state).1::reversed) (fresh state).2
      have hw := wrapList_usage 1 16 2 [(loopWithTrace fresh count ((fresh state).1::reversed) (fresh state).2).2]
      simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
      change usage (wrapList 1 16 2 [(loopWithTrace fresh count ((fresh state).1::reversed) (fresh state).2).2]) ≤ _
      simp only [List.length_cons] at hn
      omega

theorem generate_usage {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) :
    usage (generateWithTrace fresh count state).2 ≤ 24*count+16 := by
  simpa only [generateWithTrace,List.length_nil,mul_zero,Nat.add_zero] using loop_usage fresh count [] state

-- Instrumentation counts actual primitive invocations; it does not modify the
-- producer or assume a supplied number of draws.
def countedFresh {S : Type*} (fresh : S → Bool × S) (state : S × ℕ) : Bool × (S × ℕ) :=
  let bit := fresh state.1
  (bit.1,(bit.2,state.2+1))

theorem loop_counted {S : Type*} (fresh : S → Bool × S) (count : ℕ) (reversed : List Bool) (state : S) (calls : ℕ) :
    (loopWithTrace (countedFresh fresh) count reversed (state,calls)).1 =
      ((loopWithTrace fresh count reversed state).1.1,((loopWithTrace fresh count reversed state).1.2,calls+count)) := by
  induction count generalizing reversed state calls with
  | zero => rfl
  | succ count ih =>
      simpa only [loopWithTrace,countedFresh,Nat.add_assoc,Nat.add_comm 1 count] using
        ih ((fresh state).1::reversed) (fresh state).2 (calls+1)

theorem generate_counted {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) (calls : ℕ) :
    (generateWithTrace (countedFresh fresh) count (state,calls)).1 =
      ((generateWithTrace fresh count state).1.1,((generateWithTrace fresh count state).1.2,calls+count)) :=
  loop_counted fresh count [] state calls

def tapeFresh (tape : ℕ → Bool) (position : ℕ) : Bool × ℕ := (tape position,position+1)

theorem loop_tape (tape : ℕ → Bool) (count : ℕ) (reversed : List Bool) (position : ℕ) :
    (loopWithTrace (tapeFresh tape) count reversed position).1 =
      (reversed.reverse++List.ofFn (fun i : Fin count => tape (position+i.val)),position+count) := by
  induction count generalizing reversed position with
  | zero => simp [loopWithTrace,reverseWithTrace_result,List.reverseAux_eq]
  | succ count ih =>
      rw [loopWithTrace]
      dsimp only [tapeFresh]
      rw [ih]
      simp only [List.reverse_cons,List.ofFn_succ,List.append_assoc,List.singleton_append,
        Fin.val_zero,Fin.val_succ,Nat.add_zero,Nat.add_assoc,Nat.add_comm 1 count,
        Nat.add_comm 1 (Fin.val _)]

theorem generate_tape (tape : ℕ → Bool) (count position : ℕ) :
    (generateWithTrace (tapeFresh tape) count position).1 =
      (List.ofFn (fun i : Fin count => tape (position+i.val)),position+count) := by
  simpa only [generateWithTrace,List.reverse_nil,List.nil_append] using loop_tape tape count [] position

def vectorTape {N : ℕ} (bits : Fin N → Bool) (position : ℕ) : Bool :=
  if h : position < N then bits ⟨position,h⟩ else false

theorem generate_vector {N : ℕ} (bits : Fin N → Bool) :
    (generateWithTrace (tapeFresh (vectorTape bits)) N 0).1 = (List.ofFn bits,N) := by
  rw [generate_tape]
  simp only [Nat.zero_add,vectorTape,dite_eq_left (Fin.isLt _),Fin.eta]

theorem all_prefix {S : Type*} (fresh : S → Bool × S) (count : ℕ) (state : S) (borrowed steps : ℕ) :
    retainedHeap borrowed (generateWithTrace fresh count state).2 steps ≤ borrowed+24*count+16 ∧
      framePeak ((generateWithTrace fresh count state).2.take steps) ≤ 24*count+16 := by
  simpa only [Nat.add_assoc] using BinaryPRGHeapTraceUsage.all_prefix _ _ (generate_usage fresh count state) borrowed steps

end Blotto.FreshBitSeedLifetime
