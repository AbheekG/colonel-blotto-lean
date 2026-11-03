import Blotto.BinarySeedPreparationSpace
import Blotto.BinaryPRGHeapTraceUsage

/-! Validated cursor blocks are retained as tapes. The operational producer
never packs native arrays or compatibility-reader closures. Erasure to the
old tables is a specification used only in proofs and source envelopes. -/
namespace Blotto.BinaryPRGTapeSeedBlocks
open RationalLottoResourceSystem BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 2000000

structure Blocks (n K : ℕ) where
  choice : BinaryScalarTape (coinBitBudget n K)
  scalar : BinaryScalarTape K
  outer : BinaryScalarTape K

def pack (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) : Blocks n K :=
  ⟨⟨choice,hc⟩,⟨scalar,hs⟩,⟨outer,ho⟩⟩

def Blocks.erase {n K : ℕ} (blocks : Blocks n K) : BinaryPRGSeedBlocks.Tables n K :=
  BinaryPRGSeedBlocks.pack n K blocks.choice.bits blocks.scalar.bits blocks.outer.bits
    blocks.choice.size blocks.scalar.size blocks.outer.size

@[simp] theorem pack_erase (n K : ℕ) (choice scalar outer : List Bool)
    (hc : choice.length = coinBitBudget n K) (hs : scalar.length = K) (ho : outer.length = K) :
    (pack n K choice scalar outer hc hs ho).erase = BinaryPRGSeedBlocks.pack n K choice scalar outer hc hs ho := rfl

@[simp] theorem Blocks.erase_choice {n K : ℕ} (blocks : Blocks n K) :
    blocks.erase.choice.data.toList = blocks.choice.bits := by simp [Blocks.erase,BinaryPRGSeedBlocks.pack]

@[simp] theorem Blocks.erase_scalar {n K : ℕ} (blocks : Blocks n K) : blocks.erase.scalarView = blocks.scalar := rfl
@[simp] theorem Blocks.erase_outer {n K : ℕ} (blocks : Blocks n K) : blocks.erase.outerView = blocks.outer := rfl

def Blocks.flatList {n K : ℕ} (blocks : Blocks n K) : List Bool :=
  blocks.choice.bits ++ blocks.scalar.bits ++ blocks.outer.bits

theorem Blocks.erase_flatList {n K : ℕ} (blocks : Blocks n K) : blocks.erase.flatList = blocks.flatList := by
  exact BinaryPRGSeedBlocks.pack_flatList n K _ _ _ _ _ _

def readWithTrace (n K : ℕ) (seed : List Bool) : Option (Blocks n K) × Trace :=
  let choiceRuler := List.replicate (coinBitBudget n K) false
  let precisionRuler := List.replicate K false
  let initialTrace := under 8 (rulerTrace (coinBitBudget n K)) ++ under 8 (rulerTrace K) ++ [.frames 8]
  let choice := consumeWithTrace choiceRuler seed
  let choiceTrace := under 8 choice.2
  match hc : choice.1.1 with
  | none => (none,initialTrace ++ choiceTrace)
  | some first =>
      let scalar := consumeWithTrace precisionRuler first.2
      let scalarTrace := under 8 scalar.2
      match hs : scalar.1.1 with
      | none => (none,initialTrace ++ choiceTrace ++ scalarTrace)
      | some second =>
          let outer := consumeWithTrace precisionRuler second.2
          let outerTrace := under 8 outer.2
          match ho : outer.1.1 with
          | none => (none,initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)
          | some third =>
              if hEnd : third.2 = [] then
                have hChoice : first.1.length = coinBitBudget n K := by
                  have h := (BinarySeedCursor.consume_success choiceRuler seed first.1 first.2
                    ((consumeWithTrace_option choiceRuler seed).symm.trans hc)).1
                  simpa only [choiceRuler,List.length_replicate] using h
                have hScalar : second.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler first.2 second.1 second.2
                    ((consumeWithTrace_option precisionRuler first.2).symm.trans hs)).1
                  simpa only [precisionRuler,List.length_replicate] using h
                have hOuter : third.1.length = K := by
                  have h := (BinarySeedCursor.consume_success precisionRuler second.2 third.1 third.2
                    ((consumeWithTrace_option precisionRuler second.2).symm.trans ho)).1
                  simpa only [precisionRuler,List.length_replicate] using h
                (some (pack n K first.1 second.1 third.1 hChoice hScalar hOuter),
                  initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace ++ [.arrayAllocation 32])
              else (none,initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace)

theorem read_state (n K : ℕ) (seed : List Bool) :
    (readWithTrace n K seed).1.map Blocks.erase = (BinaryPRGSeedBlocks.read n K seed).1 := by
  unfold readWithTrace BinaryPRGSeedBlocks.read
  dsimp only
  repeat' first
    | rfl
    | simp_all [pack_erase]
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
  rfl

theorem read_success_flatList (n K : ℕ) (seed : List Bool) (blocks : Blocks n K)
    (h : (readWithTrace n K seed).1 = some blocks) : blocks.flatList = seed := by
  have hState := read_state n K seed
  rw [h,Option.map_some] at hState
  rw [← blocks.erase_flatList]
  exact BinaryPRGSeedBlocks.read_success_flatList n K seed blocks.erase hState.symm

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
              if third.2 = [] then initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace ++ [.arrayAllocation 32]
              else initialTrace ++ choiceTrace ++ scalarTrace ++ outerTrace

@[simp] theorem read_trace (n K : ℕ) (seed : List Bool) : (readWithTrace n K seed).2 = readTrace n K seed := by
  unfold readWithTrace readTrace
  dsimp only
  repeat' first
    | rfl
    | simp_all [consumeWithTrace_trace,consumeWithTrace_option,List.append_assoc]
    | split

theorem trace_bounds (n K : ℕ) (seed : List Bool) :
    listCells (readTrace n K seed) ≤ 3*sampleBitBudget n K ∧
    arraySlots (readTrace n K seed) ≤ 32 ∧
    framePeak (readTrace n K seed) ≤ 2*sampleBitBudget n K+10 := by
  have hN : sampleBitBudget n K = coinBitBudget n K+K+K := by unfold sampleBitBudget innerBitBudget; rfl
  have hC := consumeTrace_under_bounds (List.replicate (coinBitBudget n K) false) seed
  simp only [List.length_replicate] at hC
  unfold readTrace
  dsimp only
  split
  · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,
      rulerTrace_under_frames,listCells,arraySlots,framePeak,Nat.add_zero,Nat.zero_add,Nat.max_zero]
    exact ⟨by omega,by omega,by omega⟩
  · rename_i first hc
    have hS := consumeTrace_under_bounds (List.replicate K false) first.2
    simp only [List.length_replicate] at hS
    split
    · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,
        rulerTrace_under_frames,listCells,arraySlots,framePeak,Nat.add_zero,Nat.zero_add,Nat.max_zero]
      exact ⟨by omega,by omega,by omega⟩
    · rename_i second hs
      have hO := consumeTrace_under_bounds (List.replicate K false) second.2
      simp only [List.length_replicate] at hO
      split
      · simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,
          rulerTrace_under_frames,listCells,arraySlots,framePeak,Nat.add_zero,Nat.zero_add,Nat.max_zero]
        exact ⟨by omega,by omega,by omega⟩
      · split <;>
          simp only [listCells_append,arraySlots_append,framePeak_append,rulerTrace_under_cells,rulerTrace_under_slots,
            rulerTrace_under_frames,listCells,arraySlots,framePeak,Nat.add_zero,Nat.zero_add,Nat.max_zero] <;>
          exact ⟨by omega,by omega,by omega⟩

theorem trace_slots_le (n K : ℕ) (seed : List Bool) :
    arraySlots (readTrace n K seed) ≤ arraySlots (BinarySeedPreparationSpace.readTrace n K seed) := by
  unfold readTrace BinarySeedPreparationSpace.readTrace
  dsimp only
  repeat' first
    | exact Nat.le_refl _
    | split
    | simp_all [arraySlots_append,rulerTrace,arraySlots]
  omega

theorem reject_arrays (n K : ℕ) (seed : List Bool)
    (h : (BinaryPRGSeedBlocks.read n K seed).1 = none) : arraySlots (readWithTrace n K seed).2 = 0 := by
  rw [read_trace]
  have hl := trace_slots_le n K seed
  rw [BinarySeedPreparationSpace.readTrace_reject_arrays n K seed h] at hl
  omega

theorem read_usage (n K : ℕ) (seed : List Bool) :
    usage (readWithTrace n K seed).2 ≤ ownedBound (sampleBitBudget n K)+2*sampleBitBudget n K+10 := by
  rw [read_trace]
  have h := trace_bounds n K seed
  unfold usage BinaryPRGHeapPrimitiveLifetime.cells ownedBound
  omega

end Blotto.BinaryPRGTapeSeedBlocks
