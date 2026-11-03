import Blotto.BinaryPRGSeedPreparedRun

/-! Source-level allocation and control-frame semantics for reached seed
preparation. Every allocated list cell and every array version stays live until
preparation returns. The original seed is borrowed and counted once, including
caller aliases and shared suffixes. There is no uniqueness or reclamation premise.

The trace charges accumulator conses, terminal reversal cells, both rulers, and
initial/old/new array regions of the final capacity at every push. It follows
actual cursor/read branches, EOF and deferred conversions, including truncation
and surplus rejection. The trace is ghost execution evidence; materializing the observer is outside
the modeled producer. Source activations are retained even across tail calls;
frame counts are abstract activations, not compiled stack bytes. Every trace
prefix is bounded, not merely the returned table inventory.

Representation prices interpret cells, reserved slots and source activations.
Native allocator capacity/record layout, scalar bit payloads, compiler stack realization, GC
and the downstream sampler remain separate. An arbitrarily long rejected seed
contributes its borrowed storage; only new preparation workspace is frame-bounded.
-/
namespace Blotto.BinarySeedPreparationSpace
open RationalLottoResourceSystem

inductive Event where
  | listAllocation (cells : ℕ)
  | arrayAllocation (slots : ℕ)
  | frames (count : ℕ)
  deriving Repr, DecidableEq
abbrev Trace := List Event

def listCells : Trace → ℕ
  | [] => 0
  | .listAllocation n :: rest => n + listCells rest
  | _ :: rest => listCells rest

def arraySlots : Trace → ℕ
  | [] => 0
  | .arrayAllocation n :: rest => n + arraySlots rest
  | _ :: rest => arraySlots rest

-- Array headers count even for zero-capacity scalar/outer arrays.
def arrayRecords : Trace → ℕ
  | [] => 0
  | .arrayAllocation _ :: rest => 1 + arrayRecords rest
  | _ :: rest => arrayRecords rest

def framePeak : Trace → ℕ
  | [] => 0
  | .frames n :: rest => max n (framePeak rest)
  | _ :: rest => framePeak rest

def shiftEvent (depth : ℕ) : Event → Event
  | .frames n => .frames (depth + n)
  | e => e

def under (depth : ℕ) (trace : Trace) : Trace := trace.map (shiftEvent depth)

@[simp] theorem listCells_append (a b : Trace) : listCells (a ++ b) = listCells a + listCells b := by
  induction a with
  | nil => simp [listCells]
  | cons e rest ih => cases e <;> simp [listCells, ih, Nat.add_assoc]

@[simp] theorem arraySlots_append (a b : Trace) : arraySlots (a ++ b) = arraySlots a + arraySlots b := by
  induction a with
  | nil => simp [arraySlots]
  | cons e rest ih => cases e <;> simp [arraySlots, ih, Nat.add_assoc]

@[simp] theorem arrayRecords_append (a b : Trace) : arrayRecords (a ++ b) = arrayRecords a + arrayRecords b := by
  induction a with
  | nil => simp [arrayRecords]
  | cons e rest ih => cases e <;> simp [arrayRecords, ih, Nat.add_assoc]

@[simp] theorem framePeak_append (a b : Trace) : framePeak (a ++ b) = max (framePeak a) (framePeak b) := by
  induction a with
  | nil => simp [framePeak]
  | cons e rest ih => cases e <;> simp [framePeak, ih, Nat.max_assoc]

@[simp] theorem listCells_under (depth : ℕ) (trace : Trace) : listCells (under depth trace) = listCells trace := by
  induction trace with
  | nil => rfl
  | cons e rest ih => cases e <;> simp [under, shiftEvent, listCells, under] at ih ⊢ <;> omega

@[simp] theorem arraySlots_under (depth : ℕ) (trace : Trace) : arraySlots (under depth trace) = arraySlots trace := by
  induction trace with
  | nil => rfl
  | cons e rest ih => cases e <;> simp [under, shiftEvent, arraySlots, under] at ih ⊢ <;> omega

@[simp] theorem arrayRecords_under (depth : ℕ) (trace : Trace) : arrayRecords (under depth trace) = arrayRecords trace := by
  induction trace with
  | nil => rfl
  | cons e rest ih => cases e <;> simp [under, shiftEvent, arrayRecords, under] at ih ⊢ <;> omega

theorem framePeak_under (depth : ℕ) (trace : Trace) : framePeak (under depth trace) ≤ depth + framePeak trace := by
  induction trace with
  | nil => simp [under, framePeak]
  | cons e rest ih =>
      cases e <;> simp only [under, List.map_cons, shiftEvent, framePeak] at ih ⊢ <;> omega

-- Follows List.reverseAux, retaining source parents despite tail position.
def reverseWithTrace : List Bool → List Bool → List Bool × Trace
  | [], acc => (acc,[.frames 1])
  | bit :: bits, acc =>
      let next := reverseWithTrace bits (bit :: acc)
      (next.1,[.frames 1,.listAllocation 1] ++ under 1 next.2)

theorem reverseWithTrace_result (bits acc : List Bool) :
    (reverseWithTrace bits acc).1 = List.reverseAux bits acc := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => exact ih (bit :: acc)

theorem reverseWithTrace_cells (bits acc : List Bool) :
    listCells (reverseWithTrace bits acc).2 = bits.length := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp [reverseWithTrace, listCells, ih, Nat.add_comm]

theorem reverseWithTrace_arrays (bits acc : List Bool) :
    arraySlots (reverseWithTrace bits acc).2 = 0 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp [reverseWithTrace, arraySlots, ih]

theorem reverseWithTrace_frames (bits acc : List Bool) :
    framePeak (reverseWithTrace bits acc).2 ≤ bits.length + 1 := by
  induction bits generalizing acc with
  | nil => simp [reverseWithTrace, framePeak]
  | cons bit bits ih =>
      have hu := framePeak_under 1 (reverseWithTrace bits (bit :: acc)).2
      have ht := ih (bit :: acc)
      simp only [reverseWithTrace, framePeak_append, framePeak, List.length_cons]
      omega

def cursorWithTrace : List Bool → List Bool → List Bool → Option (List Bool × List Bool) × Trace
  | [], bits, reversed =>
      let result := reverseWithTrace reversed []
      (some (result.1,bits),[.frames 1] ++ under 1 result.2)
  | _ :: _, [], _ => (none,[.frames 1])
  | _ :: ruler, bit :: bits, reversed =>
      let next := cursorWithTrace ruler bits (bit :: reversed)
      (next.1,[.frames 1,.listAllocation 1] ++ under 1 next.2)

theorem cursorWithTrace_result (ruler bits reversed : List Bool) :
    (cursorWithTrace ruler bits reversed).1 = BinarySeedCursor.loop ruler bits reversed := by
  induction ruler generalizing bits reversed with
  | nil => simp [cursorWithTrace, BinarySeedCursor.loop, reverseWithTrace_result, List.reverseAux_eq]
  | cons cell ruler ih =>
      cases bits with
      | nil => rfl
      | cons bit bits => exact ih bits (bit :: reversed)

theorem cursorWithTrace_cells (ruler bits reversed : List Bool) :
    listCells (cursorWithTrace ruler bits reversed).2 ≤ 2 * ruler.length + reversed.length := by
  induction ruler generalizing bits reversed with
  | nil => simp [cursorWithTrace, listCells, reverseWithTrace_cells]
  | cons cell ruler ih =>
      cases bits with
      | nil => simp [cursorWithTrace, listCells]
      | cons bit bits =>
          have ht := ih bits (bit :: reversed)
          simp only [cursorWithTrace, listCells_append, listCells, listCells_under, List.length_cons] at ht ⊢
          omega

theorem cursorWithTrace_arrays (ruler bits reversed : List Bool) :
    arraySlots (cursorWithTrace ruler bits reversed).2 = 0 := by
  induction ruler generalizing bits reversed with
  | nil => simp [cursorWithTrace, arraySlots, reverseWithTrace_arrays]
  | cons cell ruler ih =>
      cases bits with
      | nil => rfl
      | cons bit bits => simp [cursorWithTrace, arraySlots, ih]

theorem cursorWithTrace_frames (ruler bits reversed : List Bool) :
    framePeak (cursorWithTrace ruler bits reversed).2 ≤ 2 * ruler.length + reversed.length + 2 := by
  induction ruler generalizing bits reversed with
  | nil =>
      have hu := framePeak_under 1 (reverseWithTrace reversed []).2
      have ht := reverseWithTrace_frames reversed []
      simp only [cursorWithTrace, framePeak_append, framePeak, List.length_nil, Nat.mul_zero, Nat.zero_add]
      omega
  | cons cell ruler ih =>
      cases bits with
      | nil => simp [cursorWithTrace, framePeak]
      | cons bit bits =>
          have hu := framePeak_under 1 (cursorWithTrace ruler bits (bit :: reversed)).2
          have ht := ih bits (bit :: reversed)
          simp only [cursorWithTrace, framePeak_append, framePeak, List.length_cons] at ht ⊢
          omega

-- consume also evaluates visits after the cursor: no new list/array cells,
-- but conservative source frames for that reached observer are included.
def consumeTrace (ruler bits : List Bool) : Trace :=
  (cursorWithTrace ruler bits []).2 ++ [.frames (BinarySeedCursor.visits ruler bits)]

theorem consumeTrace_bounds (ruler bits : List Bool) :
    listCells (consumeTrace ruler bits) ≤ 2 * ruler.length ∧
    arraySlots (consumeTrace ruler bits) = 0 ∧
    framePeak (consumeTrace ruler bits) ≤ 2 * ruler.length + 2 := by
  have hc := cursorWithTrace_cells ruler bits []
  have hf := cursorWithTrace_frames ruler bits []
  have hv := BinarySeedCursor.visits_bound ruler bits
  simp only [List.length_nil, Nat.add_zero] at hc hf
  simp only [consumeTrace, listCells_append, arraySlots_append, framePeak_append, listCells, arraySlots,
    framePeak, cursorWithTrace_arrays, Nat.add_zero, Nat.max_zero]
  exact ⟨hc,trivial,max_le hf (by omega)⟩

@[simp] theorem reverseWithTrace_records (bits acc : List Bool) : arrayRecords (reverseWithTrace bits acc).2 = 0 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp [reverseWithTrace,arrayRecords,ih]

@[simp] theorem cursorWithTrace_records (ruler bits reversed : List Bool) :
    arrayRecords (cursorWithTrace ruler bits reversed).2 = 0 := by
  induction ruler generalizing bits reversed with
  | nil => simp [cursorWithTrace,arrayRecords]
  | cons cell ruler ih =>
      cases bits with
      | nil => rfl
      | cons bit bits => simp [cursorWithTrace,arrayRecords,ih]

@[simp] theorem consumeTrace_records (ruler bits : List Bool) : arrayRecords (consumeTrace ruler bits) = 0 := by
  simp [consumeTrace,arrayRecords]

-- Reserve final capacity for the initial region and every permitted copy.
def arrayWithTrace (capacity : ℕ) : List Bool → Array Bool → Array Bool × Trace
  | [], acc => (acc,[.frames 1])
  | bit :: bits, acc =>
      let next := arrayWithTrace capacity bits (acc.push bit)
      (next.1,[.frames 1,.arrayAllocation capacity] ++ under 1 next.2)

theorem arrayWithTrace_result (capacity : ℕ) (bits : List Bool) (acc : Array Bool) :
    (arrayWithTrace capacity bits acc).1 = List.toArrayAux bits acc := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => exact ih (acc.push bit)

theorem arrayWithTrace_cells (capacity : ℕ) (bits : List Bool) (acc : Array Bool) :
    listCells (arrayWithTrace capacity bits acc).2 = 0 := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp [arrayWithTrace, listCells, ih]

theorem arrayWithTrace_slots (capacity : ℕ) (bits : List Bool) (acc : Array Bool) :
    arraySlots (arrayWithTrace capacity bits acc).2 = bits.length * capacity := by
  induction bits generalizing acc with
  | nil => simp [arrayWithTrace, arraySlots]
  | cons bit bits ih => simp [arrayWithTrace, arraySlots, ih, Nat.add_mul, Nat.add_comm]

theorem arrayWithTrace_frames (capacity : ℕ) (bits : List Bool) (acc : Array Bool) :
    framePeak (arrayWithTrace capacity bits acc).2 ≤ bits.length + 1 := by
  induction bits generalizing acc with
  | nil => simp [arrayWithTrace, framePeak]
  | cons bit bits ih =>
      have hu := framePeak_under 1 (arrayWithTrace capacity bits (acc.push bit)).2
      have ht := ih (acc.push bit)
      simp only [arrayWithTrace, framePeak_append, framePeak, List.length_cons]
      omega

def toArrayWithTrace (bits : List Bool) : Array Bool × Trace :=
  let result := arrayWithTrace bits.length bits (Array.mkEmpty bits.length)
  (result.1,[.arrayAllocation bits.length,.frames (bits.length + 1)] ++ result.2)

theorem toArrayWithTrace_result (bits : List Bool) : (toArrayWithTrace bits).1 = bits.toArray := by
  apply Array.toList_inj.mp
  simp [toArrayWithTrace, arrayWithTrace_result, Array.toArrayAux_eq, Array.mkEmpty]

theorem toArrayWithTrace_bounds (bits : List Bool) :
    listCells (toArrayWithTrace bits).2 = 0 ∧
    arraySlots (toArrayWithTrace bits).2 = bits.length * (bits.length + 1) ∧
    framePeak (toArrayWithTrace bits).2 ≤ bits.length + 1 := by
  have hf := arrayWithTrace_frames bits.length bits (Array.mkEmpty bits.length)
  simp only [toArrayWithTrace, listCells_append, arraySlots_append, framePeak_append, listCells, arraySlots,
    framePeak, arrayWithTrace_cells, arrayWithTrace_slots, Nat.add_zero, Nat.max_zero]
  refine ⟨trivial,by ring,max_le le_rfl hf⟩

@[simp] theorem arrayWithTrace_records (capacity : ℕ) (bits : List Bool) (acc : Array Bool) :
    arrayRecords (arrayWithTrace capacity bits acc).2 = bits.length := by
  induction bits generalizing acc with
  | nil => rfl
  | cons bit bits ih => simp [arrayWithTrace,arrayRecords,ih,Nat.add_comm]

@[simp] theorem toArrayWithTrace_records (bits : List Bool) : arrayRecords (toArrayWithTrace bits).2 = bits.length + 1 := by
  simp [toArrayWithTrace,arrayRecords,Nat.add_comm]

-- Logical array versions fit in the reserved final region at every push.
-- This checks the fixed-capacity interpretation, rather than assuming an
-- undocumented native allocator growth policy.
theorem array_prefix_capacity (capacity : ℕ) (bits : List Bool) (acc : Array Bool) (steps : ℕ)
    (h : acc.size + bits.length ≤ capacity) : (List.toArrayAux (bits.take steps) acc).size ≤ capacity := by
  have ht : (bits.take steps).length ≤ bits.length := by simp
  have hs : (List.toArrayAux (bits.take steps) acc).size = acc.size + (bits.take steps).length := by
    rw [← Array.length_toList,Array.toArrayAux_eq,List.length_append,Array.length_toList]
  omega

-- One cons per replicate cell; retain its structural source activations.
def rulerTrace (length : ℕ) : Trace := [.listAllocation length,.frames (length + 1)]

@[simp] theorem rulerTrace_under_cells (depth length : ℕ) : listCells (under depth (rulerTrace length)) = length := by
  simp [rulerTrace,listCells]

@[simp] theorem rulerTrace_under_slots (depth length : ℕ) : arraySlots (under depth (rulerTrace length)) = 0 := by
  simp [rulerTrace,arraySlots]

@[simp] theorem rulerTrace_under_frames (depth length : ℕ) : framePeak (under depth (rulerTrace length)) = depth + length + 1 := by
  simp [under,rulerTrace,shiftEvent,framePeak,Nat.add_assoc]

def readTrace (n K : ℕ) (seed : List Bool) : Trace :=
  let choiceRuler := List.replicate (coinBitBudget n K) false
  let precisionRuler := List.replicate K false
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K)) ++ under 8 (rulerTrace K) ++ [.frames 8]
  let choiceTrace := under 8 (consumeTrace choiceRuler seed)
  match (BinarySeedCursor.consume choiceRuler seed).1 with
  | none => initialTrace ++ choiceTrace
  | some first =>
      let scalarTrace := under 8 (consumeTrace precisionRuler first.2)
      match (BinarySeedCursor.consume precisionRuler first.2).1 with
      | none => initialTrace ++ choiceTrace ++ scalarTrace
      | some second =>
          let outerTrace := under 8 (consumeTrace precisionRuler second.2)
          match (BinarySeedCursor.consume precisionRuler second.2).1 with
          | none => initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace
          | some third =>
              if third.2 = [] then
                initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace ++
                  under 8 (toArrayWithTrace first.1).2 ++
                  under 8 (toArrayWithTrace second.1).2 ++
                  under 8 (toArrayWithTrace third.1).2 ++ [.arrayAllocation 32]
              else initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace

def consumeWithTrace (ruler bits : List Bool) : (Option (List Bool × List Bool) × ℕ) × Trace :=
  let result := cursorWithTrace ruler bits []
  ((result.1,5 * BinarySeedCursor.visits ruler bits),result.2 ++ [.frames (BinarySeedCursor.visits ruler bits)])

@[simp] theorem consumeWithTrace_result (ruler bits : List Bool) :
    (consumeWithTrace ruler bits).1 = BinarySeedCursor.consume ruler bits := by
  simp only [consumeWithTrace,cursorWithTrace_result,BinarySeedCursor.consume]

@[simp] theorem consumeWithTrace_option (ruler bits : List Bool) :
    (consumeWithTrace ruler bits).1.1 = (BinarySeedCursor.consume ruler bits).1 :=
  congrArg Prod.fst (consumeWithTrace_result ruler bits)

@[simp] theorem consumeWithTrace_charge (ruler bits : List Bool) :
    (consumeWithTrace ruler bits).1.2 = (BinarySeedCursor.consume ruler bits).2 :=
  congrArg Prod.snd (consumeWithTrace_result ruler bits)

@[simp] theorem consumeWithTrace_trace (ruler bits : List Bool) :
    (consumeWithTrace ruler bits).2 = consumeTrace ruler bits := rfl

-- The retained views, their reader closures and table fields reserve one
-- source-record region; the cursor lists themselves are shared, with no new
-- tape cells or native projection. Native byte/reference prices are separate.
def packWithTrace (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    BinaryPRGSeedBlocks.Tables n K × Trace :=
  let c := toArrayWithTrace choice
  let s := toArrayWithTrace scalar
  let o := toArrayWithTrace outer
  (⟨⟨c.1,by simpa only [c,toArrayWithTrace_result,List.size_toArray] using hc⟩,
      ⟨s.1,by simpa only [s,toArrayWithTrace_result,List.size_toArray] using hs⟩,
      ⟨o.1,by simpa only [o,toArrayWithTrace_result,List.size_toArray] using ho⟩,
      ⟨scalar,hs⟩,⟨outer,ho⟩,
      BinaryScalarTape.read_eq_array _ _ (by simp [s,toArrayWithTrace_result]),
      BinaryScalarTape.read_eq_array _ _ (by simp [o,toArrayWithTrace_result])⟩,
    under 8 c.2 ++ under 8 s.2 ++ under 8 o.2 ++ [.arrayAllocation 32])

@[simp] theorem packWithTrace_result (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (packWithTrace n K choice scalar outer hc hs ho).1 = BinaryPRGSeedBlocks.pack n K choice scalar outer hc hs ho := by
  simp [packWithTrace,BinaryPRGSeedBlocks.pack,toArrayWithTrace_result]

-- Instrumented producer: the results come from the operational cursor and
-- array builders, rather than computing the original read alongside a trace.
def readWithTrace (n K : ℕ) (seed : List Bool) :
    (Option (BinaryPRGSeedBlocks.Tables n K) × BinaryPRGSeedBlocks.Ledger) × Trace :=
  let choiceRuler := List.replicate (coinBitBudget n K) false
  let precisionRuler := List.replicate K false
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K)) ++ under 8 (rulerTrace K) ++ [.frames 8]
  let rulers := coinBitBudget n K + K
  let choice := consumeWithTrace choiceRuler seed
  let choiceTrace := under 8 choice.2
  match hc : choice.1.1 with
  | none => ((none,⟨rulers,choice.1.2,0⟩),initialTrace ++ choiceTrace)
  | some first =>
      let scalar := consumeWithTrace precisionRuler first.2
      let scalarTrace := under 8 scalar.2
      match hs : scalar.1.1 with
      | none => ((none,⟨rulers,choice.1.2 + scalar.1.2,0⟩),initialTrace ++ choiceTrace ++ scalarTrace)
      | some second =>
          let outer := consumeWithTrace precisionRuler second.2
          let outerTrace := under 8 outer.2
          match ho : outer.1.1 with
          | none => ((none,⟨rulers,choice.1.2 + scalar.1.2 + outer.1.2,0⟩),initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2
                    ((congrArg Prod.fst (consumeWithTrace_result choiceRuler seed)).symm.trans hc)).1
                  simpa only [choiceRuler,List.length_replicate] using h
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2
                    ((congrArg Prod.fst (consumeWithTrace_result precisionRuler first.2)).symm.trans hs)).1
                  simpa only [precisionRuler,List.length_replicate] using h
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2
                    ((congrArg Prod.fst (consumeWithTrace_result precisionRuler second.2)).symm.trans ho)).1
                  simpa only [precisionRuler,List.length_replicate] using h
                let packed := packWithTrace n K first.1 second.1 third.1 hChoice hScalar hOuter
                ((some packed.1,⟨rulers,choice.1.2 + scalar.1.2 + outer.1.2 + 1,
                    BinaryPRGSeedBlocks.arrayCellAllowance first.1.length +
                    BinaryPRGSeedBlocks.arrayCellAllowance second.1.length +
                    BinaryPRGSeedBlocks.arrayCellAllowance third.1.length⟩),
                  initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace ++ packed.2)
              else ((none,⟨rulers,choice.1.2 + scalar.1.2 + outer.1.2 + 1,0⟩),
                initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)

@[simp] theorem readWithTrace_result (n K : ℕ) (seed : List Bool) :
    (readWithTrace n K seed).1 = BinaryPRGSeedBlocks.read n K seed := by
  unfold readWithTrace BinaryPRGSeedBlocks.read
  dsimp only
  repeat' first
    | rfl
    | simp_all [packWithTrace_result]
    | split

  rename_i c hc s hs o ho hEnd c' hc' s' hs' o' ho' hEnd'
  have hC : c = c' := Option.some.inj
    (((consumeWithTrace_option (List.replicate (coinBitBudget n K) false) seed).symm.trans hc).symm.trans hc')
  cases hC
  have hS : s = s' := Option.some.inj
    (((consumeWithTrace_option (List.replicate K false) c.2).symm.trans hs).symm.trans hs')
  cases hS
  have hO : o = o' := Option.some.inj
    (((consumeWithTrace_option (List.replicate K false) s.2).symm.trans ho).symm.trans ho')
  cases hO
  exact ⟨rfl,rfl,rfl⟩

@[simp] theorem readWithTrace_trace (n K : ℕ) (seed : List Bool) :
    (readWithTrace n K seed).2 = readTrace n K seed := by
  unfold readWithTrace readTrace
  dsimp only
  repeat' first
    | rfl
    | simp_all [consumeWithTrace_trace,packWithTrace,List.append_assoc]
    | split

theorem consumeTrace_under_bounds (ruler bits : List Bool) :
    listCells (under 8 (consumeTrace ruler bits)) ≤ 2 * ruler.length ∧
    arraySlots (under 8 (consumeTrace ruler bits)) = 0 ∧
    framePeak (under 8 (consumeTrace ruler bits)) ≤ 2 * ruler.length + 10 := by
  have h := consumeTrace_bounds ruler bits
  have hf := framePeak_under 8 (consumeTrace ruler bits)
  simp only [listCells_under,arraySlots_under]
  exact ⟨h.1,h.2.1,by omega⟩

theorem toArrayWithTrace_under_bounds (bits : List Bool) :
    listCells (under 8 (toArrayWithTrace bits).2) = 0 ∧
    arraySlots (under 8 (toArrayWithTrace bits).2) = bits.length * (bits.length + 1) ∧
    framePeak (under 8 (toArrayWithTrace bits).2) ≤ bits.length + 9 := by
  have h := toArrayWithTrace_bounds bits
  have hf := framePeak_under 8 (toArrayWithTrace bits).2
  simp only [listCells_under,arraySlots_under]
  exact ⟨h.1,h.2.1,by omega⟩

theorem regionAllocation_add (a b : ℕ) :
    a * (a + 1) + b * (b + 1) ≤ (a + b) * (a + b + 1) := by nlinarith

theorem readTrace_bounds (n K : ℕ) (seed : List Bool) :
    listCells (readTrace n K seed) ≤ 3 * sampleBitBudget n K ∧
    arraySlots (readTrace n K seed) ≤ sampleBitBudget n K * (sampleBitBudget n K + 1) + 32 ∧
    framePeak (readTrace n K seed) ≤ 2 * sampleBitBudget n K + 10 := by
  have hN : sampleBitBudget n K = coinBitBudget n K + K + K := by
    unfold sampleBitBudget innerBitBudget
    rfl
  have hC := consumeTrace_under_bounds (List.replicate (coinBitBudget n K) false) seed
  simp only [List.length_replicate] at hC
  unfold readTrace
  try dsimp only
  split
  · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,rulerTrace_under_frames,listCells,arraySlots,framePeak,
      Nat.add_zero,Nat.zero_add,Nat.max_zero]
    exact ⟨by omega,by omega,by omega⟩
  · rename_i first hc
    have hFirst := (BinarySeedCursor.consume_success (List.replicate (coinBitBudget n K) false) seed first.1 first.2 hc).1
    have hS := consumeTrace_under_bounds (List.replicate K false) first.2
    simp only [List.length_replicate] at hFirst hS
    split
    · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,rulerTrace_under_frames,listCells,arraySlots,framePeak,
        Nat.add_zero,Nat.zero_add,Nat.max_zero]
      exact ⟨by omega,by omega,by omega⟩
    · rename_i second hs
      have hSecond := (BinarySeedCursor.consume_success (List.replicate K false) first.2 second.1 second.2 hs).1
      have hO := consumeTrace_under_bounds (List.replicate K false) second.2
      simp only [List.length_replicate] at hSecond hO
      split
      · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,rulerTrace_under_frames,listCells,arraySlots,framePeak,
          Nat.add_zero,Nat.zero_add,Nat.max_zero]
        exact ⟨by omega,by omega,by omega⟩
      · rename_i third ho
        have hThird := (BinarySeedCursor.consume_success (List.replicate K false) second.2 third.1 third.2 ho).1
        simp only [List.length_replicate] at hThird
        split
        · have ha := toArrayWithTrace_under_bounds first.1
          have hb := toArrayWithTrace_under_bounds second.1
          have hd := toArrayWithTrace_under_bounds third.1
          rw [hFirst] at ha
          rw [hSecond] at hb
          rw [hThird] at hd
          have hCapacity : coinBitBudget n K * (coinBitBudget n K + 1) + K * (K + 1) + K * (K + 1) ≤
              sampleBitBudget n K * (sampleBitBudget n K + 1) := by
            rw [hN]
            exact (Nat.add_le_add_right (regionAllocation_add (coinBitBudget n K) K) (K * (K + 1))).trans
              (regionAllocation_add (coinBitBudget n K + K) K)
          simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,rulerTrace_under_frames,listCells,arraySlots,framePeak,
            Nat.add_zero,Nat.zero_add,Nat.max_zero]
          exact ⟨by omega,by omega,by omega⟩
        · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,rulerTrace_under_frames,listCells,arraySlots,framePeak,
            Nat.add_zero,Nat.zero_add,Nat.max_zero]
          exact ⟨by omega,by omega,by omega⟩


theorem readTrace_arrayRecords_bound (n K : ℕ) (seed : List Bool) :
    arrayRecords (readTrace n K seed) ≤ sampleBitBudget n K + 4 := by
  have hN : sampleBitBudget n K = coinBitBudget n K + K + K := by unfold sampleBitBudget innerBitBudget; rfl
  unfold readTrace
  dsimp only
  split
  · simp [rulerTrace,arrayRecords]
  · rename_i first hc
    have hFirst := (BinarySeedCursor.consume_success (List.replicate (coinBitBudget n K) false) seed first.1 first.2 hc).1
    simp only [List.length_replicate] at hFirst
    split
    · simp [rulerTrace,arrayRecords]
    · rename_i second hs
      have hSecond := (BinarySeedCursor.consume_success (List.replicate K false) first.2 second.1 second.2 hs).1
      simp only [List.length_replicate] at hSecond
      split
      · simp [rulerTrace,arrayRecords]
      · rename_i third ho
        have hThird := (BinarySeedCursor.consume_success (List.replicate K false) second.2 third.1 third.2 ho).1
        simp only [List.length_replicate] at hThird
        split
        · simp [rulerTrace,arrayRecords,hFirst,hSecond,hThird,hN]
          omega
        · simp [rulerTrace,arrayRecords]

@[simp] theorem consumeTrace_arrays (ruler bits : List Bool) : arraySlots (consumeTrace ruler bits) = 0 :=
  (consumeTrace_bounds ruler bits).2.1

theorem readTrace_reject_arrays (n K : ℕ) (seed : List Bool)
    (h : (BinaryPRGSeedBlocks.read n K seed).1 = none) : arraySlots (readTrace n K seed) = 0 := by
  unfold BinaryPRGSeedBlocks.read at h
  dsimp only at h
  unfold readTrace
  dsimp only
  split at h
  · rename_i hc
    simp [hc,rulerTrace,arraySlots]
  · rename_i first hc
    simp only [hc]
    split at h
    · rename_i hs
      simp [hs,rulerTrace,arraySlots]
    · rename_i second hs
      simp only [hs]
      split at h
      · rename_i ho
        simp [ho,rulerTrace,arraySlots]
      · rename_i third ho
        simp only [ho]
        split at h
        · cases h
        · rename_i hEnd
          simp [hEnd,rulerTrace,arraySlots]

theorem listCells_take_le (trace : Trace) (steps : ℕ) : listCells (trace.take steps) ≤ listCells trace := by
  have h := listCells_append (trace.take steps) (trace.drop steps)
  rw [List.take_append_drop] at h
  omega

theorem arraySlots_take_le (trace : Trace) (steps : ℕ) : arraySlots (trace.take steps) ≤ arraySlots trace := by
  have h := arraySlots_append (trace.take steps) (trace.drop steps)
  rw [List.take_append_drop] at h
  omega

theorem arrayRecords_take_le (trace : Trace) (steps : ℕ) : arrayRecords (trace.take steps) ≤ arrayRecords trace := by
  have h := arrayRecords_append (trace.take steps) (trace.drop steps)
  rw [List.take_append_drop] at h
  omega

theorem framePeak_take_le (trace : Trace) (steps : ℕ) : framePeak (trace.take steps) ≤ framePeak trace := by
  have h := framePeak_append (trace.take steps) (trace.drop steps)
  rw [List.take_append_drop] at h
  omega

-- Retaining all allocated objects needs no garbage collection guarantee.
-- Released or reused objects can only reduce this allocation-model envelope.
def ownedBound (count : ℕ) : ℕ := 3 * count + count * (count + 1) + 32

def retainedHeap (borrowedSeedCells : ℕ) (trace : Trace) (steps : ℕ) : ℕ :=
  borrowedSeedCells + listCells (trace.take steps) + arraySlots (trace.take steps)

theorem read_all_prefix_heap (n K : ℕ) (seed : List Bool) (steps : ℕ) :
    retainedHeap seed.length (readWithTrace n K seed).2 steps ≤ seed.length + ownedBound (sampleBitBudget n K) := by
  rw [readWithTrace_trace]
  have h := readTrace_bounds n K seed
  have hl := listCells_take_le (readTrace n K seed) steps
  have ha := arraySlots_take_le (readTrace n K seed) steps
  unfold retainedHeap ownedBound
  omega

theorem read_all_prefix_frames (n K : ℕ) (seed : List Bool) (steps : ℕ) :
    framePeak ((readWithTrace n K seed).2.take steps) ≤ 2 * sampleBitBudget n K + 10 := by
  rw [readWithTrace_trace]
  exact (framePeak_take_le _ _).trans (readTrace_bounds n K seed).2.2

theorem read_reject_prefix_heap (n K : ℕ) (seed : List Bool) (steps : ℕ)
    (h : (BinaryPRGSeedBlocks.read n K seed).1 = none) :
    retainedHeap seed.length (readWithTrace n K seed).2 steps ≤ seed.length + 3 * sampleBitBudget n K := by
  rw [readWithTrace_trace]
  have hl := listCells_take_le (readTrace n K seed) steps
  have ha := arraySlots_take_le (readTrace n K seed) steps
  have hb := (readTrace_bounds n K seed).1
  rw [readTrace_reject_arrays n K seed h] at ha
  unfold retainedHeap
  omega

theorem read_success_prefix_heap (n K : ℕ) (seed : List Bool) (steps : ℕ)
    (tables : BinaryPRGSeedBlocks.Tables n K) (h : (BinaryPRGSeedBlocks.read n K seed).1 = some tables) :
    retainedHeap seed.length (readWithTrace n K seed).2 steps ≤ 4 * sampleBitBudget n K +
      sampleBitBudget n K * (sampleBitBudget n K + 1) + 32 := by
  have hb := read_all_prefix_heap n K seed steps
  have hs := BinaryPRGSeedBlocks.read_success_length n K seed tables h
  unfold retainedHeap at hb ⊢
  rw [hs] at hb ⊢
  unfold ownedBound at hb
  omega

-- Explicit representation parameters: a frame unit must cover the chosen
-- source activation's references/control/scalar payload. No native-byte values
-- or bounded-width scalar assumptions are silently supplied here.
structure Representation where
  listCellUnits : ℕ
  arraySlotUnits : ℕ
  arrayHeaderUnits : ℕ
  frameUnits : ℕ
  deriving Repr, DecidableEq

def representedWorkspace (prices : Representation) (trace : Trace) (steps : ℕ) : ℕ :=
  prices.listCellUnits * listCells (trace.take steps) +
  prices.arraySlotUnits * arraySlots (trace.take steps) +
  prices.arrayHeaderUnits * arrayRecords (trace.take steps) +
  prices.frameUnits * framePeak (trace.take steps)

def representationBound (prices : Representation) (count : ℕ) : ℕ :=
  prices.listCellUnits * (3 * count) + prices.arraySlotUnits * (count * (count + 1) + 32) +
    prices.arrayHeaderUnits * (count + 4) + prices.frameUnits * (2 * count + 10)

theorem read_representation_bound (prices : Representation) (n K : ℕ) (seed : List Bool) (steps : ℕ) :
    representedWorkspace prices (readWithTrace n K seed).2 steps ≤ representationBound prices (sampleBitBudget n K) := by
  rw [readWithTrace_trace]
  have h := readTrace_bounds n K seed
  have hl := (listCells_take_le (readTrace n K seed) steps).trans h.1
  have ha := (arraySlots_take_le (readTrace n K seed) steps).trans h.2.1
  have hf := (framePeak_take_le (readTrace n K seed) steps).trans h.2.2
  have hr := (arrayRecords_take_le (readTrace n K seed) steps).trans (readTrace_arrayRecords_bound n K seed)
  unfold representedWorkspace representationBound
  exact Nat.add_le_add (Nat.add_le_add (Nat.add_le_add (Nat.mul_le_mul_left _ hl) (Nat.mul_le_mul_left _ ha))
    (Nat.mul_le_mul_left _ hr)) (Nat.mul_le_mul_left _ hf)

theorem ownedBound_mono {a b : ℕ} (h : a ≤ b) : ownedBound a ≤ ownedBound b := by
  unfold ownedBound
  gcongr

-- Only reached seed preparation is traced. Input parsing and output sampling
-- retain their own contracts; the wrapper contributes two source activations.
def runSeedTrace (frame seed : List Bool) : Trace :=
  match (BinaryPRGAccuracyRulerRequest.read frame).1 with
  | none => []
  | some parsed => if parsed.2 = [] then under 2 (readTrace parsed.1.1 parsed.1.2.request.precision seed) else []

def runWithTrace (rich : Bool) (frame seed : List Bool) :
    (Option (List Bool × BinaryPRGOutputRun.Ledger) × BinaryPRGSeedPreparedRun.Ledger) × Trace :=
  let decoded := BinaryPRGAccuracyRulerRequest.read frame
  match decoded.1 with
  | none => ((none,⟨decoded.2,⟨0,0,0⟩⟩),[])
  | some parsed =>
      if parsed.2 = [] then
        let blocks := readWithTrace parsed.1.1 parsed.1.2.request.precision seed
        ((blocks.1.1.map (BinaryPRGSeedBlockOutput.output parsed.1.2 rich),⟨decoded.2,blocks.1.2⟩),under 2 blocks.2)
      else ((none,⟨decoded.2,⟨0,0,0⟩⟩),[])

@[simp] theorem runWithTrace_result (rich : Bool) (frame seed : List Bool) :
    (runWithTrace rich frame seed).1 = BinaryPRGSeedPreparedRun.run rich frame seed := by
  unfold runWithTrace BinaryPRGSeedPreparedRun.run
  dsimp only
  repeat' first
    | rfl
    | simp_all [readWithTrace_result]
    | split

@[simp] theorem runWithTrace_trace (rich : Bool) (frame seed : List Bool) :
    (runWithTrace rich frame seed).2 = runSeedTrace frame seed := by
  unfold runWithTrace runSeedTrace
  dsimp only
  repeat' first
    | rfl
    | simp_all [readWithTrace_trace]
    | split

theorem runSeedTrace_bounds (frame seed : List Bool) :
    listCells (runSeedTrace frame seed) ≤ 3 * BinaryPRGSeedRequestBound.seedCountBound frame.length ∧
    arraySlots (runSeedTrace frame seed) ≤ BinaryPRGSeedRequestBound.seedCountBound frame.length *
      (BinaryPRGSeedRequestBound.seedCountBound frame.length + 1) + 32 ∧
    framePeak (runSeedTrace frame seed) ≤ 2 * BinaryPRGSeedRequestBound.seedCountBound frame.length + 12 := by
  unfold runSeedTrace
  split
  · simp [listCells,arraySlots,framePeak]
  · rename_i parsed hd
    have hCount := BinaryPRGSeedRequestBound.read_seedCount_bound frame parsed hd
    split
    · have h := readTrace_bounds parsed.1.1 parsed.1.2.request.precision seed
      have hf := framePeak_under 2 (readTrace parsed.1.1 parsed.1.2.request.precision seed)
      simp only [listCells_under,arraySlots_under]
      refine ⟨by omega,?_,by omega⟩
      exact h.2.1.trans (Nat.add_le_add_right (Nat.mul_le_mul hCount (Nat.add_le_add_right hCount 1)) 32)
    · simp [listCells,arraySlots,framePeak]

theorem run_all_prefix_seed_heap (rich : Bool) (frame seed : List Bool) (steps : ℕ) :
    retainedHeap seed.length (runWithTrace rich frame seed).2 steps ≤ seed.length +
      ownedBound (8 * frame.length + 3025) := by
  rw [runWithTrace_trace]
  have h := runSeedTrace_bounds frame seed
  have hl := listCells_take_le (runSeedTrace frame seed) steps
  have ha := arraySlots_take_le (runSeedTrace frame seed) steps
  unfold retainedHeap ownedBound BinaryPRGSeedRequestBound.seedCountBound at *
  omega

theorem run_all_prefix_seed_frames (rich : Bool) (frame seed : List Bool) (steps : ℕ) :
    framePeak ((runWithTrace rich frame seed).2.take steps) ≤ 16 * frame.length + 6062 := by
  rw [runWithTrace_trace]
  have h := (framePeak_take_le (runSeedTrace frame seed) steps).trans (runSeedTrace_bounds frame seed).2.2
  calc
    _ ≤ 2 * (8 * frame.length + 3025) + 12 := h
    _ = _ := by ring

end Blotto.BinarySeedPreparationSpace
