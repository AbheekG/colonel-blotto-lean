import Blotto.BinaryQuadraticLifetime
import Blotto.BinaryWordStoreLifetime
import Blotto.BinaryPRGWordControllerGeneralChoice
import Blotto.BinaryGeneralResourceLattice

/-! Actual Boolean-address Tree4 pair construction/update and field extraction
have allocation lifetimes joined to the quadratic arithmetic backend. Tree
leaves retain word references; input payload is borrowed, and arithmetic traces
cover newly produced words. No native register array is produced. Every old
node/cursor/record reservation stays live. Native SSA exists only as the checked
proof view deriving reached word widths from the source fields or lattice.
This endpoint is reached pair preparation, not the complete resource loop or
its selected native resource-array update. Pointer encodings and host layout
are separate from the Boolean/list/reference-cell model. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticResourcePairLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerPairRegisters
open BinaryResourcePair BinaryGeneralResourceLattice

def buildWithTrace (fallback : SignedWord) : (ruler : List Bool) → List SignedWord → (Tree ruler.length×List SignedWord)×Trace
  | [],[] => ((.leaf fallback,[]),[.frames 1,.arrayAllocation 8])
  | [],bit::rest => ((.leaf bit,rest),[.frames 1,.arrayAllocation 8])
  | _::ruler,seed =>
      let left := buildWithTrace fallback ruler seed
      let right := buildWithTrace fallback ruler left.1.2
      ((.branch left.1.1 right.1.1,right.1.2),[.frames 1,.arrayAllocation 8] ++ under 1 left.2 ++ under 1 right.2)

@[simp] theorem buildWithTrace_erases (fallback : SignedWord) (ruler : List Bool) (seed : List SignedWord) :
    (buildWithTrace fallback ruler seed).1=BinaryPRGWordControllerWordStore.build fallback ruler seed := by
  induction ruler generalizing seed with
  | nil => cases seed <;> rfl
  | cons cell ruler ih => simp only [buildWithTrace,BinaryPRGWordControllerWordStore.build,ih]

theorem buildWithTrace_bounds (fallback : SignedWord) (ruler : List Bool) (items : List SignedWord) :
    listCells (buildWithTrace fallback ruler items).2+arraySlots (buildWithTrace fallback ruler items).2=
      8*buildVisits fallback ruler items ∧ framePeak (buildWithTrace fallback ruler items).2≤ruler.length+1 := by
  induction ruler generalizing items with
  | nil => cases items <;> simp [buildWithTrace,buildVisits,listCells,arraySlots,framePeak]
  | cons cell ruler ih =>
      have hl := ih items
      have hr := ih (buildWithTrace fallback ruler items).1.2
      have hlf := framePeak_under 1 (buildWithTrace fallback ruler items).2
      have hrf := framePeak_under 1 (buildWithTrace fallback ruler (buildWithTrace fallback ruler items).1.2).2
      simp only [buildWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
        listCells_under,arraySlots_under,buildVisits,List.length_cons]
      rw [buildWithTrace_erases] at hr hrf ⊢
      exact ⟨by omega,by omega⟩

def scanTreeWithTrace : {depth : ℕ} → Tree depth → List Bool → SignedWord×Trace
  | _,.leaf bit,_ => (bit,[.frames 1,.arrayAllocation 4])
  | _,.branch left _,[] =>
      let later := scanTreeWithTrace left []
      (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)
  | _,.branch left right,bit::rest =>
      let later := if bit then scanTreeWithTrace right rest else scanTreeWithTrace left rest
      (later.1,[.frames 1,.arrayAllocation 4] ++ under 1 later.2)

@[simp] theorem scanTreeWithTrace_erases {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    (scanTreeWithTrace tree address).1=scan tree address := by
  induction tree generalizing address with
  | leaf bit => rfl
  | branch left right hl hr => cases address with
    | nil => exact hl []
    | cons bit rest => cases bit <;> simp [scanTreeWithTrace,scan,hl,hr]

theorem scanTreeWithTrace_bounds {depth : ℕ} (tree : Tree depth) (address : List Bool) :
    listCells (scanTreeWithTrace tree address).2+arraySlots (scanTreeWithTrace tree address).2=4*(depth+1) ∧
    framePeak (scanTreeWithTrace tree address).2≤depth+1 := by
  induction tree generalizing address with
  | leaf bit => simp [scanTreeWithTrace,listCells,arraySlots,framePeak]
  | @branch depth left right hl hr =>
      cases address with
      | nil =>
          have hf := framePeak_under 1 (scanTreeWithTrace left []).2
          have h := hl []
          simp only [scanTreeWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under]
          exact ⟨by omega,by omega⟩
      | cons bit rest =>
          cases bit <;> simp only [scanTreeWithTrace,Bool.false_eq_true,ite_false,ite_true]
          · have hf := framePeak_under 1 (scanTreeWithTrace left rest).2
            have h := hl rest
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩
          · have hf := framePeak_under 1 (scanTreeWithTrace right rest).2
            have h := hr rest
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩

def lookupWithTrace  {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) : SignedWord×Trace :=
  let reversed := reverseWithTrace address.bits []
  let reached := scanTreeWithTrace tree reversed.1
  (reached.1,[.frames 2,.arrayAllocation 8] ++ under 2 reversed.2 ++ under 2 reached.2)

@[simp] theorem lookupWithTrace_erases  {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) :
    (lookupWithTrace tree address).1=lookup tree address := by
  simp only [lookupWithTrace,scanTreeWithTrace_erases,reverseWithTrace_result]
  rfl

theorem lookupWithTrace_bounds  {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) :
    listCells (lookupWithTrace tree address).2+arraySlots (lookupWithTrace tree address).2≤5*depth+12 ∧
    framePeak (lookupWithTrace tree address).2≤depth+3 := by
  have hr := reverseWithTrace_cells address.bits []
  have hra := reverseWithTrace_arrays address.bits []
  have hrf := reverseWithTrace_frames address.bits []
  rw [address.size] at hr hrf
  have hs := scanTreeWithTrace_bounds tree (reverseWithTrace address.bits []).1
  have hR := framePeak_under 2 (reverseWithTrace address.bits []).2
  have hS := framePeak_under 2 (scanTreeWithTrace tree (reverseWithTrace address.bits []).1).2
  simp only [lookupWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def writeScanWithTrace : {depth : ℕ} → Tree depth → List Bool → SignedWord → Tree depth×Trace
  | _,.leaf _,_,word => (.leaf word,[.frames 1,.arrayAllocation 8])
  | _,.branch left right,[],word =>
      let later := writeScanWithTrace left [] word
      (.branch later.1 right,[.frames 1,.arrayAllocation 8] ++ under 1 later.2)
  | _,.branch left right,bit::rest,word =>
      if bit then
        let later := writeScanWithTrace right rest word
        (.branch left later.1,[.frames 1,.arrayAllocation 8] ++ under 1 later.2)
      else
        let later := writeScanWithTrace left rest word
        (.branch later.1 right,[.frames 1,.arrayAllocation 8] ++ under 1 later.2)

@[simp] theorem writeScanWithTrace_erases {depth : ℕ} (tree : Tree depth) (address : List Bool) (word : SignedWord) :
    (writeScanWithTrace tree address word).1=writeScan tree address word := by
  induction tree generalizing address with
  | leaf old => rfl
  | branch left right hl hr =>
      cases address with
      | nil => simp only [writeScanWithTrace,writeScan,hl]
      | cons bit rest => cases bit <;> simp [writeScanWithTrace,writeScan,hl,hr]

theorem writeScanWithTrace_bounds {depth : ℕ} (tree : Tree depth) (address : List Bool) (word : SignedWord) :
    listCells (writeScanWithTrace tree address word).2+arraySlots (writeScanWithTrace tree address word).2=8*(depth+1) ∧
    framePeak (writeScanWithTrace tree address word).2≤depth+1 := by
  induction tree generalizing address with
  | leaf old => simp [writeScanWithTrace,listCells,arraySlots,framePeak]
  | @branch depth left right hl hr =>
      cases address with
      | nil =>
          have h := hl []
          have hf := framePeak_under 1 (writeScanWithTrace left [] word).2
          simp only [writeScanWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
            listCells_under,arraySlots_under]
          exact ⟨by omega,by omega⟩
      | cons bit rest =>
          cases bit <;> simp only [writeScanWithTrace,Bool.false_eq_true,ite_false,ite_true]
          · have h := hl rest
            have hf := framePeak_under 1 (writeScanWithTrace left rest word).2
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
              listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩
          · have h := hr rest
            have hf := framePeak_under 1 (writeScanWithTrace right rest word).2
            simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
              listCells_under,arraySlots_under]
            exact ⟨by omega,by omega⟩

def writeWithTrace {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) (word : SignedWord) : Tree depth×Trace :=
  let reversed := reverseWithTrace address.bits []
  let written := writeScanWithTrace tree reversed.1 word
  (written.1,[.frames 2,.arrayAllocation 8] ++ under 2 reversed.2 ++ under 2 written.2)

@[simp] theorem writeWithTrace_erases {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    (writeWithTrace tree address word).1=write tree address word := by
  simp only [writeWithTrace,writeScanWithTrace_erases,reverseWithTrace_result]
  rfl

theorem writeWithTrace_bounds {depth : ℕ} (tree : Tree depth) (address : FixedBinaryWord depth) (word : SignedWord) :
    listCells (writeWithTrace tree address word).2+arraySlots (writeWithTrace tree address word).2≤9*depth+16 ∧
    framePeak (writeWithTrace tree address word).2≤depth+3 := by
  have hr := reverseWithTrace_cells address.bits []
  have hra := reverseWithTrace_arrays address.bits []
  have hrf := reverseWithTrace_frames address.bits []
  rw [address.size] at hr hrf
  have hs := writeScanWithTrace_bounds tree (reverseWithTrace address.bits []).1 word
  have hR := framePeak_under 2 (reverseWithTrace address.bits []).2
  have hS := framePeak_under 2 (writeScanWithTrace tree (reverseWithTrace address.bits []).1 word).2
  simp only [writeWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def executeWithTrace (instruction : Instruction) (registers : Registers) : Registers×Trace :=
  let left := lookupWithTrace registers.tree instruction.left
  let right := lookupWithTrace registers.tree instruction.right
  let word := BinaryQuadraticLifetime.applyWithTrace instruction.op left.1 right.1
  let written := writeWithTrace registers.tree registers.cursor word.1
  let advanced := BinaryWordStoreLifetime.incrementWithTrace registers.cursor
  (⟨written.1,advanced.1.1⟩,[.frames 2,.arrayAllocation 16] ++ under 2 left.2 ++ under 2 right.2 ++
    under 2 word.2 ++ under 2 written.2 ++ under 2 advanced.2)

@[simp] theorem executeWithTrace_erases (instruction : Instruction) (registers : Registers) :
    (executeWithTrace instruction registers).1=execute instruction registers := by
  simp only [executeWithTrace,lookupWithTrace_erases,BinaryQuadraticLifetime.applyWithTrace_erases,
    writeWithTrace_erases,BinaryWordStoreLifetime.incrementWithTrace_erases,execute]

def instructionBound (W : ℕ) : ℕ := BinaryQuadraticLifetime.opcodeBound W+200
def instructionFrames (W : ℕ) : ℕ := BinaryQuadraticLifetime.opcodeFrames W+20

theorem executeWithTrace_bounds (instruction : Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (W : ℕ) (hWords : BinaryRationalRegisterProgram.WordBounds reference W) :
    listCells (executeWithTrace instruction registers).2+arraySlots (executeWithTrace instruction registers).2≤ instructionBound W ∧
    framePeak (executeWithTrace instruction registers).2≤ instructionFrames W := by
  have hLeft := lookupWithTrace_bounds registers.tree instruction.left
  have hRight := lookupWithTrace_bounds registers.tree instruction.right
  have hOp := BinaryQuadraticLifetime.applyWithTrace_bounds instruction.op
    (lookupWithTrace registers.tree instruction.left).1 (lookupWithTrace registers.tree instruction.right).1 W
    (by rw [lookupWithTrace_erases,h.2]; exact hWords _)
    (by rw [lookupWithTrace_erases,h.2]; exact hWords _)
  have hWrite := writeWithTrace_bounds registers.tree registers.cursor
    (BinaryQuadraticLifetime.applyWithTrace instruction.op
      (lookupWithTrace registers.tree instruction.left).1 (lookupWithTrace registers.tree instruction.right).1).1
  have hAdvanced := BinaryWordStoreLifetime.incrementWithTrace_bounds registers.cursor
  have hLF := framePeak_under 2 (lookupWithTrace registers.tree instruction.left).2
  have hRF := framePeak_under 2 (lookupWithTrace registers.tree instruction.right).2
  have hOF := framePeak_under 2 (BinaryQuadraticLifetime.applyWithTrace instruction.op
    (lookupWithTrace registers.tree instruction.left).1 (lookupWithTrace registers.tree instruction.right).1).2
  have hWF := framePeak_under 2 (writeWithTrace registers.tree registers.cursor
    (BinaryQuadraticLifetime.applyWithTrace instruction.op
      (lookupWithTrace registers.tree instruction.left).1 (lookupWithTrace registers.tree instruction.right).1).1).2
  have hAF := framePeak_under 2 (BinaryWordStoreLifetime.incrementWithTrace registers.cursor).2
  unfold executeWithTrace instructionBound instructionFrames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def runWithTrace : List Instruction → Registers → Registers×Trace
  | [],registers => (registers,[.frames 1,.arrayAllocation 8])
  | instruction::rest,registers =>
      let next := executeWithTrace instruction registers
      let later := runWithTrace rest next.1
      (later.1,[.frames 2,.arrayAllocation 8] ++ under 2 next.2 ++ under 1 later.2)

@[simp] theorem runWithTrace_erases (program : List Instruction) (registers : Registers) :
    (runWithTrace program registers).1=run program registers := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih => simp only [runWithTrace,run,executeWithTrace_erases,ih]

theorem runWithTrace_bounds (program : List Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (hValid : BinaryRationalRegisterProgram.ValidRegisters reference)
    (hRoom : reference.size+program.length<16) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds (program.map Instruction.reference) reference W) :
    listCells (runWithTrace program registers).2+arraySlots (runWithTrace program registers).2≤
      program.length*(instructionBound W+8)+8 ∧
    framePeak (runWithTrace program registers).2≤program.length+instructionFrames W+4 := by
  induction program generalizing registers reference with
  | nil => simp [runWithTrace,listCells,arraySlots,framePeak,instructionFrames]
  | cons instruction rest ih =>
      have hNext := execute_refines instruction registers reference h hValid (by simp only [List.length_cons] at hRoom; omega)
      have hBefore := trace_start _ _ W hTrace
      have hTraceNext : BinaryRationalRegisterProgram.TraceWordBounds (rest.map Instruction.reference)
          (BinaryRationalRegisterProgram.execute instruction.reference reference) W := hTrace.2
      have hInstruction := executeWithTrace_bounds instruction registers reference h W hBefore
      have hRest := ih (execute instruction registers) (BinaryRationalRegisterProgram.execute instruction.reference reference)
        hNext (BinaryRationalRegisterProgram.execute_valid _ _ hValid) (by
          rw [BinaryRationalRegisterProgram.execute_size]
          simp only [List.length_cons] at hRoom
          omega) hTraceNext
      have hIF := framePeak_under 2 (executeWithTrace instruction registers).2
      have hRF := framePeak_under 1 (runWithTrace rest (execute instruction registers)).2
      simp only [runWithTrace,executeWithTrace_erases,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,
        framePeak,listCells_under,arraySlots_under,List.length_cons]
      exact ⟨by nlinarith only [hInstruction.1,hRest.1],by omega⟩

def initialWithTrace (source : BinaryRationalPairProgram.Source) : Registers×Trace :=
  let built := buildWithTrace BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
  (⟨built.1.1,a5⟩,[.frames 2,.listAllocation 13,.arrayAllocation 16] ++ under 2 built.2)

@[simp] theorem initialWithTrace_erases (source : BinaryRationalPairProgram.Source) :
    (initialWithTrace source).1=BinaryPRGWordControllerPairRegisters.initial source := by
  simp only [initialWithTrace,buildWithTrace_erases,BinaryPRGWordControllerPairRegisters.initial]

theorem initialWithTrace_bounds (source : BinaryRationalPairProgram.Source) :
    listCells (initialWithTrace source).2+arraySlots (initialWithTrace source).2≤300 ∧
    framePeak (initialWithTrace source).2≤7 := by
  have h := buildWithTrace_bounds BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
  have hv := buildVisits_exact BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
  have hf := framePeak_under 2 (buildWithTrace BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)).2
  norm_num only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reducePow] at h hv
  simp only [initialWithTrace,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def preparedPairWithTrace (source : BinaryRationalPairProgram.Source) : Registers×Trace :=
  let init := initialWithTrace source
  let completed := runWithTrace code init.1
  (completed.1,[.frames 2,.arrayAllocation 8] ++ under 2 init.2 ++ under 2 completed.2)

@[simp] theorem preparedPairWithTrace_erases (source : BinaryRationalPairProgram.Source) :
    (preparedPairWithTrace source).1=pair source := by
  simp only [preparedPairWithTrace,runWithTrace_erases,initialWithTrace_erases,pair]

def pairBound (W : ℕ) : ℕ := 316+7*(instructionBound W+8)
def pairFrames (W : ℕ) : ℕ := instructionFrames W+16

theorem preparedPairWithTrace_bounds (source : BinaryRationalPairProgram.Source) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code source.inputs W) :
    listCells (preparedPairWithTrace source).2+arraySlots (preparedPairWithTrace source).2≤pairBound W ∧
    framePeak (preparedPairWithTrace source).2≤pairFrames W := by
  have hi := initialWithTrace_bounds source
  have ht := hTrace
  rw [← code_reference] at ht
  have hp := runWithTrace_bounds code (BinaryPRGWordControllerPairRegisters.initial source) source.inputs (initial_refines source) source.inputs_valid
    (by simp [BinaryRationalPairProgram.Source.inputs,code]) W ht
  have hIF := framePeak_under 2 (initialWithTrace source).2
  have hPF := framePeak_under 2 (runWithTrace code (BinaryPRGWordControllerPairRegisters.initial source)).2
  have hLength : code.length=7 := rfl
  rw [hLength] at hp
  unfold preparedPairWithTrace pairBound pairFrames
  simp only [initialWithTrace_erases,listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,
    listCells_under,arraySlots_under]
  have hFramePositive : 1≤ instructionFrames W := by unfold instructionFrames; omega
  exact ⟨by omega,by omega⟩

def outputsWithTrace (source : BinaryRationalPairProgram.Source) : BinaryPRGWordControllerPairOutputs.Outputs×Trace :=
  let registers := preparedPairWithTrace source
  let lower := lookupWithTrace registers.1.tree a7
  let upper := lookupWithTrace registers.1.tree a8
  let probability := lookupWithTrace registers.1.tree a11
  (⟨lower.1,upper.1,probability.1⟩,[.frames 2,.arrayAllocation 16] ++ under 2 registers.2 ++
    under 2 lower.2 ++ under 2 upper.2 ++ under 2 probability.2)

@[simp] theorem outputsWithTrace_erases (source : BinaryRationalPairProgram.Source) :
    (outputsWithTrace source).1=BinaryPRGWordControllerPairOutputs.prepare source := by
  simp only [outputsWithTrace,preparedPairWithTrace_erases,lookupWithTrace_erases,BinaryPRGWordControllerPairOutputs.prepare]

def outputsBound (W : ℕ) : ℕ := pairBound W+112
def outputsFrames (W : ℕ) : ℕ := pairFrames W+4

theorem outputsWithTrace_bounds (source : BinaryRationalPairProgram.Source) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds RealPairProgram.code source.inputs W) :
    listCells (outputsWithTrace source).2+arraySlots (outputsWithTrace source).2≤outputsBound W ∧
    framePeak (outputsWithTrace source).2≤outputsFrames W := by
  have hp := preparedPairWithTrace_bounds source W hTrace
  have hl := lookupWithTrace_bounds (preparedPairWithTrace source).1.tree a7
  have hu := lookupWithTrace_bounds (preparedPairWithTrace source).1.tree a8
  have hb := lookupWithTrace_bounds (preparedPairWithTrace source).1.tree a11
  have hPF := framePeak_under 2 (preparedPairWithTrace source).2
  have hLF := framePeak_under 2 (lookupWithTrace (preparedPairWithTrace source).1.tree a7).2
  have hUF := framePeak_under 2 (lookupWithTrace (preparedPairWithTrace source).1.tree a8).2
  have hBF := framePeak_under 2 (lookupWithTrace (preparedPairWithTrace source).1.tree a11).2
  have hFramePositive : 9≤pairFrames W := by unfold pairFrames instructionFrames; omega
  unfold outputsWithTrace outputsBound outputsFrames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

def sourceCells (source : BinaryRationalPairProgram.Source) : ℕ := 16+
  BinaryRationalOpcodeAllocation.payload source.lengthI+BinaryRationalOpcodeAllocation.payload source.lengthJ+
  BinaryRationalOpcodeAllocation.payload source.resourceI+BinaryRationalOpcodeAllocation.payload source.resourceJ

theorem outputs_source_all_prefix (source : BinaryRationalPairProgram.Source) (s : ℕ)
    (hs : 2≤s) (hHeight : source.pair.FieldsHeight s) (borrowedOtherCells originalSeedCells steps : ℕ) :
    retainedHeap (sourceCells source+borrowedOtherCells+originalSeedCells) (outputsWithTrace source).2 steps≤
      sourceCells source+borrowedOtherCells+originalSeedCells+outputsBound (32*s+31) :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _
    (outputsWithTrace_bounds source _ (source.trace_wordBounds hHeight hs)).1

theorem outputs_source_all_prefix_frames (source : BinaryRationalPairProgram.Source) (s : ℕ)
    (hs : 2≤s) (hHeight : source.pair.FieldsHeight s) (steps : ℕ) :
    framePeak ((outputsWithTrace source).2.take steps)≤outputsFrames (32*s+31) :=
  (framePeak_take_le _ _).trans (outputsWithTrace_bounds source _ (source.trace_wordBounds hHeight hs)).2

/-- The actual resource pair caller consumes the traced three outputs. No
native SSA register array or alternative pair producer executes here. -/
def choiceWithTrace {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) :
    BinaryPRGWordControllerGeneralChoice.Choice capacity hC×Trace :=
  let outputs := outputsWithTrace (pairSource hC state a b tail he)
  (⟨state,a,b,tail,he,outputs.1,outputsWithTrace_erases _⟩,
    [.frames 2,.arrayAllocation 24] ++ under 2 outputs.2)

@[simp] theorem choiceWithTrace_erases {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail) :
    (choiceWithTrace hC state a b tail he).1=BinaryPRGWordControllerGeneralChoice.Choice.prepare hC state a b tail he := by
  simp only [choiceWithTrace,outputsWithTrace_erases,BinaryPRGWordControllerGeneralChoice.Choice.prepare]

def choiceBound (W : ℕ) : ℕ := outputsBound W+24
def choiceFrames (W : ℕ) : ℕ := outputsFrames W+4

theorem choiceWithTrace_lattice_bounds {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) :
    listCells (choiceWithTrace hC state a b tail he).2+arraySlots (choiceWithTrace hC state a b tail he).2≤
      choiceBound (3+2*binaryWordWidth D) ∧
    framePeak (choiceWithTrace hC state a b tail he).2≤choiceFrames (3+2*binaryWordWidth D) := by
  have hp := outputsWithTrace_bounds (pairSource hC state a b tail he) _
    (pair_trace_wordBounds hC state a b tail he D hD hLattice hUnit hs)
  have hf := framePeak_under 2 (outputsWithTrace (pairSource hC state a b tail he)).2
  have hPositive : 1≤outputsFrames (3+2*binaryWordWidth D) := by unfold outputsFrames pairFrames instructionFrames; omega
  unfold choiceWithTrace choiceBound choiceFrames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by omega,by omega⟩

open scoped BigOperators

def callerCells {n : ℕ} (capacity : FixedArrayTable n SignedWord) (state : Certified capacity) : ℕ :=
  16+2*n+state.state.active.length+
    (∑ j,BinaryRationalOpcodeAllocation.payload (capacity.read j))+
    (∑ j,BinaryRationalOpcodeAllocation.payload (state.state.resource.read j))

theorem choice_lattice_all_prefix {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state)
    (borrowedOtherCells originalSeedCells steps : ℕ) :
    retainedHeap (callerCells capacity state+borrowedOtherCells+originalSeedCells) (choiceWithTrace hC state a b tail he).2 steps≤
      callerCells capacity state+borrowedOtherCells+originalSeedCells+choiceBound (3+2*binaryWordWidth D) :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _
    (choiceWithTrace_lattice_bounds hC state a b tail he D hD hLattice hUnit hs).1

theorem choice_lattice_all_prefix_frames {n : ℕ} {capacity : FixedArrayTable n SignedWord}
    (hC : ∀ j,CanonicalWord (capacity.read j)) (state : Certified capacity)
    (a b : Fin n) (tail : List (Fin n)) (he : state.state.active=a::b::tail)
    (D : ℕ) (hD : 0<D) (hLattice : ∀ j,OnRationalLattice D (value (capacity.read j)))
    (hUnit : ∀ j,value (capacity.read j)≤1) (hs : StateInvariant capacity D state) (steps : ℕ) :
    framePeak ((choiceWithTrace hC state a b tail he).2.take steps)≤choiceFrames (3+2*binaryWordWidth D) :=
  (framePeak_take_le _ _).trans (choiceWithTrace_lattice_bounds hC state a b tail he D hD hLattice hUnit hs).2

end Blotto.BinaryQuadraticResourcePairLifetime
