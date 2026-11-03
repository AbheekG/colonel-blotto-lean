import Blotto.BinaryRegisterCounterDecoder

/-! Generic word prices follow actual instruction operands and actual returned
register states. These observers are not called by the executable producer.
The complete decoder profile is instantiated below; native calibration stays separate. -/
namespace Blotto.BinaryRegisterDecoderLayer
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryRegisterMetadataPlan
set_option autoImplicit false
set_option maxHeartbeats 2000000
attribute [local irreducible] BinaryRegisterTreePlan.lookupAt BinaryRegisterTreePlan.writeAt BinaryRegisterTreePlan.initialAt BinaryNormalizationPlan.applyAt BinaryRegisterMetadataPlan.cursorAt BinaryRegisterStoragePlan.executeAt BinaryRegisterStoragePlan.runAt BinaryRegisterStoragePlan.pairAt BinaryRegisterStoragePlan.outputsAt

variable (price : SignedWord → ℕ) (factor : ℕ)
variable (hPrice : ∀ word, price word ≤ factor*(payload word).2)

include hPrice in
theorem read_bound (word : SignedWord) : price word ≤ factor*readCharge word :=
  (hPrice word).trans (Nat.mul_le_mul_left factor (read_pays word))

include hPrice in
theorem write_bound (word : SignedWord) : price word ≤ factor*writeCharge word :=
  (hPrice word).trans (Nat.mul_le_mul_left factor (write_pays word))

def copiedPrice : {height : ℕ} → Tree height → ℕ
  | _,.leaf word => price word
  | _,.branch left right => copiedPrice left+copiedPrice right

include hPrice in
theorem copied_bound {height : ℕ} (tree : Tree height) :
    copiedPrice price tree ≤ factor*(copied tree).2 := by
  induction tree with
  | leaf word =>
      have h := hPrice word
      simp only [copiedPrice,copied,Nat.mul_add,Nat.mul_one]
      omega
  | branch left right hl hr =>
      simp only [copiedPrice,copied,Nat.mul_add,Nat.mul_one]
      omega

include hPrice in
theorem initial_bound (tree : Tree 4) : copiedPrice price tree ≤ factor*initialCharge tree :=
  (copied_bound price factor hPrice tree).trans (Nat.mul_le_mul_left factor (initial_pays tree))

def sourcePrice (source : BinaryRationalPairProgram.Source) : ℕ :=
  price source.lengthI+price source.lengthJ+price source.resourceI+price source.resourceJ

include hPrice in
theorem source_bound (source : BinaryRationalPairProgram.Source) :
    sourcePrice price source ≤ factor*sourceCharge source := by
  have ha := hPrice source.lengthI
  have hb := hPrice source.lengthJ
  have hc := hPrice source.resourceI
  have hd := hPrice source.resourceJ
  have h := Nat.mul_le_mul_left factor (source_pays source)
  simp only [Nat.mul_add] at h
  unfold sourcePrice
  omega

def execute (instruction : Instruction) (registers : Registers) (depth : ℕ) : ℕ :=
  let left := BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)
  let right := BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)
  let word := BinaryNormalizationPlan.applyAt instruction.op left.1.1 right.1.1 (depth+2)
  price left.1.1+price right.1.1+price word.1.1

include hPrice in
theorem execute_bound (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    execute price instruction registers depth ≤ factor*(BinaryRegisterStoragePlan.executeAt instruction registers depth).1.2.1 := by
  have hl := read_bound price factor hPrice (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
  have hr := read_bound price factor hPrice (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1
  have hw := write_bound price factor hPrice (BinaryNormalizationPlan.applyAt instruction.op
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.left (depth+2)).1.1
    (BinaryRegisterTreePlan.lookupAt registers.tree instruction.right (depth+2)).1.1 (depth+2)).1.1
  simp only [execute,BinaryRegisterStoragePlan.executeAt]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_zero] at *
  omega

def run : List Instruction → Registers → ℕ → ℕ
  | [],_,_ => 0
  | instruction::rest,registers,depth =>
      let next := BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)
      execute price instruction registers (depth+2)+run rest next.1.1.1 (depth+1)

include hPrice in
theorem run_bound (program : List Instruction) (registers : Registers) (depth : ℕ) :
    run price program registers depth ≤ factor*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 := by
  induction program generalizing registers depth with
  | nil => simp only [run,BinaryRegisterStoragePlan.runAt]; omega
  | cons instruction rest ih =>
      have he := execute_bound price factor hPrice instruction registers (depth+2)
      have hr := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1)
      simp only [run,BinaryRegisterStoragePlan.runAt]
      simp only [Nat.mul_add,Nat.mul_one,Nat.mul_zero] at *
      omega

theorem prefix_le (program : List Instruction) (registers : Registers) (depth used : ℕ) :
    run price (program.take used) registers depth ≤ run price program registers depth := by
  induction program generalizing registers depth used with
  | nil => simp only [List.take_nil,run]; omega
  | cons instruction rest ih => cases used with
    | zero => simp only [List.take_zero,run]; omega
    | succ used =>
        have h := ih (BinaryRegisterStoragePlan.executeAt instruction registers (depth+2)).1.1.1 (depth+1) used
        simpa only [List.take_succ_cons,run] using Nat.add_le_add_left h (execute price instruction registers (depth+2))

include hPrice in
theorem every_prefix (program : List Instruction) (registers : Registers) (depth used : ℕ) :
    run price (program.take used) registers depth ≤ factor*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 :=
  (prefix_le price program registers depth used).trans (run_bound price factor hPrice program registers depth)

def pair (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ :=
  let init := BinaryRegisterTreePlan.initialAt source (depth+2)
  copiedPrice price init.1.1.tree+run price code init.1.1 (depth+2)

include hPrice in
theorem pair_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    pair price source depth ≤ factor*(BinaryRegisterStoragePlan.pairAt source depth).1.2.1 := by
  have hi := initial_bound price factor hPrice (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1.tree
  have hr := run_bound price factor hPrice code (BinaryRegisterTreePlan.initialAt source (depth+2)).1.1 (depth+2)
  simp only [pair,BinaryRegisterStoragePlan.pairAt]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_zero] at *
  omega

def outputs (source : BinaryRationalPairProgram.Source) (depth : ℕ) : ℕ :=
  let registers := BinaryRegisterStoragePlan.pairAt source (depth+2)
  let lower := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a7 (depth+2)
  let upper := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a8 (depth+2)
  let probability := BinaryRegisterTreePlan.lookupAt registers.1.1.1.tree a11 (depth+2)
  pair price source (depth+2)+price lower.1.1+price upper.1.1+price probability.1.1

include hPrice in
theorem outputs_bound (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    outputs price source depth ≤ factor*(BinaryRegisterStoragePlan.outputsAt source depth).1.2.1 := by
  have hp := pair_bound price factor hPrice source (depth+2)
  have hl := read_bound price factor hPrice (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a7 (depth+2)).1.1
  have hu := read_bound price factor hPrice (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a8 (depth+2)).1.1
  have hb := read_bound price factor hPrice (BinaryRegisterTreePlan.lookupAt
    (BinaryRegisterStoragePlan.pairAt source (depth+2)).1.1.1.tree a11 (depth+2)).1.1
  simp only [outputs,BinaryRegisterStoragePlan.outputsAt]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_zero] at *
  omega

include hPrice in
theorem emitted_bound (source : BinaryRationalPairProgram.Source) :
    outputs price source 0 ≤ factor*(BinaryRegisterStoragePlan.outputsWithEmission source).1.1.2 := by
  simpa only [BinaryRegisterStoragePlan.outputsWithEmission,BinaryNormalizationPlan.finishMeasured,
    BinaryNumericalReadbackPlan.finish] using outputs_bound price factor hPrice source 0

open BinaryPRGWordControllerWordStore (Store lookup)
open BinaryPRGWordControllerBooleanResourceUpdate (Address)
open BinaryPRGHeapStoredTree (Stored)
open BinaryPRGHeapResourceLoop (Finished)

variable {capacity : Store} {n : ℕ} {hCount : n = capacity.cap.value}
variable {hC : ∀ address : Address capacity.width capacity.cap,
  CanonicalWord (lookup capacity.tree address.word)}

def packed (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) : ℕ :=
  let input := (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1
  sourcePrice price input.1.1+outputs price input.1.1 0

include hPrice in
theorem packed_bound (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    packed price (hC := hC) limits state first second tail he ≤
      factor*(BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1.1.2 := by
  have hs := source_bound price factor hPrice (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  have ho := emitted_bound price factor hPrice (BinaryPackedPairPlan.source (hC := hC) limits state first second tail he).1.1.1
  simp only [packed,BinaryPackedPairPlan.pairMeasured]
  simp only [Nat.mul_add,Nat.mul_one,Nat.mul_zero] at *
  omega


-- The fixed complete profile needs no caller width, state or price certificate.
theorem complete_execute (instruction : Instruction) (registers : Registers) (depth : ℕ) :
    execute BinaryRegisterCounterDecoder.wordPrice instruction registers depth ≤
      40000*(BinaryRegisterStoragePlan.executeAt instruction registers depth).1.2.1 :=
  execute_bound _ 40000 BinaryRegisterCounterDecoder.word_payload instruction registers depth

theorem complete_run (program : List Instruction) (registers : Registers) (depth : ℕ) :
    run BinaryRegisterCounterDecoder.wordPrice program registers depth ≤
      40000*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 :=
  run_bound _ 40000 BinaryRegisterCounterDecoder.word_payload program registers depth

theorem complete_every_prefix (program : List Instruction) (registers : Registers) (depth used : ℕ) :
    run BinaryRegisterCounterDecoder.wordPrice (program.take used) registers depth ≤
      40000*(BinaryRegisterStoragePlan.runAt program registers depth).1.2.1 :=
  every_prefix _ 40000 BinaryRegisterCounterDecoder.word_payload program registers depth used

theorem complete_pair (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    pair BinaryRegisterCounterDecoder.wordPrice source depth ≤
      40000*(BinaryRegisterStoragePlan.pairAt source depth).1.2.1 :=
  pair_bound _ 40000 BinaryRegisterCounterDecoder.word_payload source depth

theorem complete_outputs (source : BinaryRationalPairProgram.Source) (depth : ℕ) :
    outputs BinaryRegisterCounterDecoder.wordPrice source depth ≤
      40000*(BinaryRegisterStoragePlan.outputsAt source depth).1.2.1 :=
  outputs_bound _ 40000 BinaryRegisterCounterDecoder.word_payload source depth

theorem complete_emitted (source : BinaryRationalPairProgram.Source) :
    outputs BinaryRegisterCounterDecoder.wordPrice source 0 ≤
      40000*(BinaryRegisterStoragePlan.outputsWithEmission source).1.1.2 :=
  emitted_bound _ 40000 BinaryRegisterCounterDecoder.word_payload source

theorem complete_packed (limits : Stored capacity.tree) (state : Finished capacity n hCount)
    (first second : Address capacity.width capacity.cap) (tail : List (Address capacity.width capacity.cap))
    (he : state.active = first::second::tail) :
    packed BinaryRegisterCounterDecoder.wordPrice (hC := hC) limits state first second tail he ≤
      40000*(BinaryPackedPairPlan.pairMeasured (hC := hC) limits state first second tail he).1.1.2 :=
  packed_bound _ 40000 BinaryRegisterCounterDecoder.word_payload limits state first second tail he

end Blotto.BinaryRegisterDecoderLayer
