import Blotto.BinaryPRGWordControllerWordStoreView
import Blotto.BinaryRationalPairProgram
import Blotto.BinaryQuadraticData

/-! The resource pair's fixed seven-opcode program now has a concrete
Boolean-address register interpreter.  Operand addresses are stored four-bit
literals; the append cursor advances by Boolean carry.  The data interpreter
uses quadratic Boolean opcodes and no native array read/push or numeric address
decoder.  Exact native pair words follow from per-step register refinement.
This backend is not assigned to unchanged old pair callers, and heap pointer
encoding remains a separate whole-machine join. -/

namespace Blotto.BinaryPRGWordControllerPairRegisters
open BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGWordControllerWordStore BinaryPRGWordControllerWordStoreView

def a0 : FixedBinaryWord 4 := ⟨[false,false,false,false],rfl⟩
def a1 : FixedBinaryWord 4 := ⟨[true,false,false,false],rfl⟩
def a2 : FixedBinaryWord 4 := ⟨[false,true,false,false],rfl⟩
def a3 : FixedBinaryWord 4 := ⟨[true,true,false,false],rfl⟩
def a5 : FixedBinaryWord 4 := ⟨[true,false,true,false],rfl⟩
def a6 : FixedBinaryWord 4 := ⟨[false,true,true,false],rfl⟩
def a7 : FixedBinaryWord 4 := ⟨[true,true,true,false],rfl⟩
def a8 : FixedBinaryWord 4 := ⟨[false,false,false,true],rfl⟩
def a9 : FixedBinaryWord 4 := ⟨[true,false,false,true],rfl⟩
def a10 : FixedBinaryWord 4 := ⟨[false,true,false,true],rfl⟩
def a11 : FixedBinaryWord 4 := ⟨[true,true,false,true],rfl⟩

structure Instruction where
  op : RealArithmeticOp
  left : FixedBinaryWord 4
  right : FixedBinaryWord 4

def code : List Instruction :=
  [⟨.add,a2,a3⟩,⟨.sub,a5,a1⟩,⟨.maximum,⟨[false,false,true,false],rfl⟩,a6⟩,
    ⟨.minimum,a0,a5⟩,⟨.sub,a2,a7⟩,⟨.sub,a8,a7⟩,⟨.div,a9,a10⟩]

noncomputable def Instruction.reference (instruction : Instruction) : RealArithmeticInstruction :=
  ⟨instruction.op,instruction.left.value,instruction.right.value⟩

theorem code_reference : code.map Instruction.reference = RealPairProgram.code := by rfl

structure Registers where
  tree : Tree 4
  cursor : FixedBinaryWord 4

def initialWords (source : BinaryRationalPairProgram.Source) : List SignedWord :=
  [source.lengthI,source.lengthJ,source.resourceI,source.resourceJ,BinaryRationalOpcode.zero]

def initial (source : BinaryRationalPairProgram.Source) : Registers :=
  ⟨(build BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)).1,a5⟩

def execute (instruction : Instruction) (registers : Registers) : Registers :=
  let left := lookup registers.tree instruction.left
  let right := lookup registers.tree instruction.right
  let word := BinaryQuadraticData.apply instruction.op left right
  ⟨write registers.tree registers.cursor word,(BinaryIndexWord.increment registers.cursor).1⟩

def run : List Instruction → Registers → Registers
  | [], registers => registers
  | instruction :: rest, registers => run rest (execute instruction registers)

def Refines (registers : Registers) (reference : Array SignedWord) : Prop :=
  registers.cursor.value = reference.size ∧
    ∀ address : FixedBinaryWord 4, lookup registers.tree address =
      BinaryRationalRegisterProgram.read reference address.value

theorem initial_refines (source : BinaryRationalPairProgram.Source) : Refines (initial source) source.inputs := by
  refine ⟨rfl,?_⟩
  intro address
  change lookup (build BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)).1 address = _
  rw [build_lookup]
  have hAddress := BinaryBigEndian.value_bounds address.bits.reverse
  rw [BinaryBigEndian.value_reverse, List.length_reverse, address.size] at hAddress
  norm_num at hAddress
  change address.value < 16 at hAddress
  interval_cases h : address.value <;> simp [initialWords,BinaryRationalPairProgram.Source.inputs,
    BinaryRationalRegisterProgram.read,List.getD_eq_getElem?_getD]

theorem read_push (registers : Array SignedWord) (word : SignedWord) (index : ℕ) :
    BinaryRationalRegisterProgram.read (registers.push word) index =
      if index = registers.size then word else BinaryRationalRegisterProgram.read registers index := by
  by_cases hAt : index = registers.size
  · subst index
    simp [BinaryRationalRegisterProgram.read,Array.getD]
  · by_cases hOld : index < registers.size
    · rw [BinaryRationalRegisterProgram.read_push_old _ _ _ hOld, ite_eq_right hAt]
    · have hPast : ¬index < registers.size + 1 := by omega
      simp [BinaryRationalRegisterProgram.read,Array.getD,hPast,hOld,hAt]

theorem execute_refines (instruction : Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (hValid : BinaryRationalRegisterProgram.ValidRegisters reference)
    (hRoom : reference.size + 1 < 16) :
    Refines (execute instruction registers) (BinaryRationalRegisterProgram.execute instruction.reference reference) := by
  have hIncrement := (BinaryIndexWord.increment_value registers.cursor (by rw [h.1]; exact hRoom)).1
  refine ⟨?_,?_⟩
  · simp only [execute,BinaryRationalRegisterProgram.execute,Array.size_push]
    exact hIncrement.trans (congrArg (· + 1) h.1)
  · intro address
    simp only [execute]
    rw [lookup_write,h.1,h.2 instruction.left,h.2 instruction.right,h.2 address]
    rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state instruction.op _ _
      (hValid instruction.left.value) (hValid instruction.right.value)]
    exact (read_push reference _ address.value).symm

theorem run_refines (program : List Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (hValid : BinaryRationalRegisterProgram.ValidRegisters reference)
    (hRoom : reference.size + program.length < 16) :
    Refines (run program registers) (BinaryRationalRegisterProgram.run (program.map Instruction.reference) reference) := by
  induction program generalizing registers reference with
  | nil => exact h
  | cons instruction rest ih =>
      have hNext := execute_refines instruction registers reference h hValid (by simp only [List.length_cons] at hRoom; omega)
      have hValidNext := BinaryRationalRegisterProgram.execute_valid instruction.reference reference hValid
      exact ih _ _ hNext hValidNext (by
        rw [BinaryRationalRegisterProgram.execute_size]
        simp only [List.length_cons] at hRoom
        omega)

def pair (source : BinaryRationalPairProgram.Source) : Registers := run code (initial source)

theorem pair_refines (source : BinaryRationalPairProgram.Source) : Refines (pair source) source.run := by
  have h := run_refines code (initial source) source.inputs (initial_refines source) source.inputs_valid
    (by simp [BinaryRationalPairProgram.Source.inputs,code] : source.inputs.size + code.length < 16)
  simpa only [pair,code_reference,BinaryRationalPairProgram.Source.run] using h

theorem pair_lower (source : BinaryRationalPairProgram.Source) :
    lookup (pair source).tree a7 = BinaryRationalRegisterProgram.read source.run 7 := by
  exact (pair_refines source).2 a7

theorem pair_upper (source : BinaryRationalPairProgram.Source) :
    lookup (pair source).tree a8 = BinaryRationalRegisterProgram.read source.run 8 := by
  exact (pair_refines source).2 a8

theorem pair_probability (source : BinaryRationalPairProgram.Source) :
    lookup (pair source).tree a11 = BinaryRationalRegisterProgram.read source.run 11 := by
  exact (pair_refines source).2 a11

def executeWithWork (instruction : Instruction) (registers : Registers) : Registers × ℕ :=
  let left := lookup registers.tree instruction.left
  let right := lookup registers.tree instruction.right
  let word := BinaryQuadraticOpcode.applyWithWork instruction.op left right
  let advanced := BinaryIndexWord.incrementWithWork registers.cursor
  (⟨write registers.tree registers.cursor word.1,advanced.1.1⟩,
    lookupCells registers.tree instruction.left + lookupCells registers.tree instruction.right + word.2 +
      updateCells ⟨4,⟨[false,false,true,true],rfl⟩,registers.tree⟩ registers.cursor word.1 + advanced.2 + 8)

theorem executeWithWork_erasure (instruction : Instruction) (registers : Registers) :
    (executeWithWork instruction registers).1 = execute instruction registers := by
  unfold executeWithWork execute
  dsimp only
  rw [BinaryQuadraticData.apply_erasure,BinaryIndexWord.incrementWithWork_state]

def instructionBound (W : ℕ) : ℕ := 11000 * (W + 1)^2 + 200 * (W + 1)

theorem executeWithWork_bound (instruction : Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (hValid : BinaryRationalRegisterProgram.ValidRegisters reference)
    (W : ℕ) (hBefore : BinaryRationalRegisterProgram.WordBounds reference W)
    (hAfter : BinaryRationalRegisterProgram.WordBounds (BinaryRationalRegisterProgram.execute instruction.reference reference) W) :
    (executeWithWork instruction registers).2 ≤ instructionBound W := by
  let left := lookup registers.tree instruction.left
  let right := lookup registers.tree instruction.right
  have hLeft : width left ≤ W := by dsimp only [left]; rw [h.2]; exact hBefore _
  have hRight : width right ≤ W := by dsimp only [right]; rw [h.2]; exact hBefore _
  have hLeftValid : BinaryRationalOpcode.Valid left := by dsimp only [left]; rw [h.2]; exact hValid _
  have hRightValid : BinaryRationalOpcode.Valid right := by dsimp only [right]; rw [h.2]; exact hValid _
  have hOutput : width (BinaryQuadraticOpcode.applyWithWork instruction.op left right).1 ≤ W := by
    rw [BinaryQuadraticOpcode.applyWithWork_state instruction.op left right hLeftValid hRightValid]
    have hNew := hAfter reference.size
    simpa only [BinaryRationalRegisterProgram.execute,read_push,ite_true,Instruction.reference,← h.2 instruction.left,
      ← h.2 instruction.right] using hNew
  have hOp := (BinaryQuadraticOpcode.applyWithWork_bound instruction.op left right).trans
    (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left
      (Nat.add_le_add_right (max_le hLeft hRight) 1) 2))
  have hLeftPayload := BinaryRationalExpression.payloadWords_bound left W hLeft
  have hRightPayload := BinaryRationalExpression.payloadWords_bound right W hRight
  have hOutputPayload := BinaryRationalExpression.payloadWords_bound _ W hOutput
  have hIncrement := BinaryIndexWord.incrementWithWork_bound registers.cursor
  unfold executeWithWork instructionBound
  dsimp only
  rw [lookupCells_exact,lookupCells_exact,updateCells_exact]
  change 46 + BinaryRationalExpression.payloadWords left +
    (46 + BinaryRationalExpression.payloadWords right) +
      (BinaryQuadraticOpcode.applyWithWork instruction.op left right).2 +
        (56 + BinaryRationalExpression.payloadWords (BinaryQuadraticOpcode.applyWithWork instruction.op left right).1) +
          (BinaryIndexWord.incrementWithWork registers.cursor).2 + 8 ≤ _
  omega

def runWithWork : List Instruction → Registers → Registers × ℕ
  | [], registers => (registers,1)
  | instruction :: rest, registers =>
      let next := executeWithWork instruction registers
      let later := runWithWork rest next.1
      (later.1,next.2 + later.2 + 2)

theorem runWithWork_erasure (program : List Instruction) (registers : Registers) :
    (runWithWork program registers).1 = run program registers := by
  induction program generalizing registers with
  | nil => rfl
  | cons instruction rest ih =>
      simp only [runWithWork,run,executeWithWork_erasure,ih]

theorem trace_start (program : List RealArithmeticInstruction) (reference : Array SignedWord) (W : ℕ)
    (h : BinaryRationalRegisterProgram.TraceWordBounds program reference W) :
    BinaryRationalRegisterProgram.WordBounds reference W := by
  cases program with
  | nil => exact h
  | cons instruction rest => exact h.1

theorem runWithWork_bound (program : List Instruction) (registers : Registers) (reference : Array SignedWord)
    (h : Refines registers reference) (hValid : BinaryRationalRegisterProgram.ValidRegisters reference)
    (hRoom : reference.size + program.length < 16) (W : ℕ)
    (hTrace : BinaryRationalRegisterProgram.TraceWordBounds (program.map Instruction.reference) reference W) :
    (runWithWork program registers).2 ≤ program.length * (instructionBound W + 2) + 1 := by
  induction program generalizing registers reference with
  | nil => simp [runWithWork]
  | cons instruction rest ih =>
      have hNext := execute_refines instruction registers reference h hValid (by simp only [List.length_cons] at hRoom; omega)
      have hBefore := trace_start _ _ W hTrace
      have hTraceNext : BinaryRationalRegisterProgram.TraceWordBounds (rest.map Instruction.reference)
          (BinaryRationalRegisterProgram.execute instruction.reference reference) W := hTrace.2
      have hAfter := trace_start _ _ W hTraceNext
      have hInstruction := executeWithWork_bound instruction registers reference h hValid W hBefore hAfter
      have hRest := ih (execute instruction registers) (BinaryRationalRegisterProgram.execute instruction.reference reference)
        hNext (BinaryRationalRegisterProgram.execute_valid _ _ hValid) (by
          rw [BinaryRationalRegisterProgram.execute_size]
          simp only [List.length_cons] at hRoom
          omega) hTraceNext
      simp only [runWithWork,executeWithWork_erasure,List.length_cons]
      nlinarith

def pairWithWork (source : BinaryRationalPairProgram.Source) : Registers × ℕ := runWithWork code (initial source)

theorem pairWithWork_erasure (source : BinaryRationalPairProgram.Source) :
    (pairWithWork source).1 = pair source := runWithWork_erasure _ _

theorem pairWithWork_bound (source : BinaryRationalPairProgram.Source) (s : ℕ)
    (hs : 2 ≤ s) (h : source.pair.FieldsHeight s) :
    (pairWithWork source).2 ≤ 7 * (instructionBound (32 * s + 31) + 2) + 1 := by
  have hTrace := source.trace_wordBounds h hs
  rw [← code_reference] at hTrace
  exact runWithWork_bound code (initial source) source.inputs (initial_refines source) source.inputs_valid
    (by simp [BinaryRationalPairProgram.Source.inputs,code]) _ hTrace

def initialWithWork (source : BinaryRationalPairProgram.Source) : Registers × ℕ :=
  (initial source,6 * buildVisits BinaryRationalOpcode.zero [false,false,false,false] (initialWords source) +
    copiedPayload (initial source).tree + 32)

theorem initialWithWork_erasure (source : BinaryRationalPairProgram.Source) :
    (initialWithWork source).1 = initial source := rfl

theorem initialWithWork_bound (source : BinaryRationalPairProgram.Source) (W : ℕ)
    (hBefore : BinaryRationalRegisterProgram.WordBounds source.inputs W) :
    (initialWithWork source).2 ≤ 218 + 16 * (1 + 2 * W) := by
  have h0 : width source.lengthI ≤ W := by
    simpa [BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 0
  have h1 : width source.lengthJ ≤ W := by
    simpa [BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 1
  have h2 : width source.resourceI ≤ W := by
    simpa [BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 2
  have h3 : width source.resourceJ ≤ W := by
    simpa [BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 3
  have hz : width BinaryRationalOpcode.zero ≤ W := by
    simpa [BinaryRationalPairProgram.Source.inputs,BinaryRationalRegisterProgram.read,Array.getD] using hBefore 4
  have hFallback := BinaryRationalExpression.payloadWords_bound BinaryRationalOpcode.zero W hz
  have hItems : ∀ word ∈ initialWords source, BinaryRationalExpression.payloadWords word ≤ 1 + 2 * W := by
    intro word hw
    simp [initialWords] at hw
    rcases hw with rfl | rfl | rfl | rfl | rfl
    · exact BinaryRationalExpression.payloadWords_bound _ W h0
    · exact BinaryRationalExpression.payloadWords_bound _ W h1
    · exact BinaryRationalExpression.payloadWords_bound _ W h2
    · exact BinaryRationalExpression.payloadWords_bound _ W h3
    · exact hFallback
  have hMax := build_maxPayload_bound BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
    (1 + 2 * W) (getD_payload_bound _ _ _ hFallback hItems)
  have hCopied := copiedPayload_bound (initial source).tree
  have hCopy : copiedPayload (initial source).tree ≤ 16 * (1 + 2 * W) := by
    exact hCopied.trans (Nat.mul_le_mul_left 16 hMax)
  have hVisits := buildVisits_exact BinaryRationalOpcode.zero [false,false,false,false] (initialWords source)
  norm_num only [List.length_cons,List.length_nil,Nat.reduceAdd,Nat.reducePow] at hVisits
  unfold initialWithWork
  dsimp only
  omega

def preparedPairWithWork (source : BinaryRationalPairProgram.Source) : Registers × ℕ :=
  let init := initialWithWork source
  let completed := runWithWork code init.1
  (completed.1,init.2 + completed.2)

theorem preparedPairWithWork_erasure (source : BinaryRationalPairProgram.Source) :
    (preparedPairWithWork source).1 = pair source := by
  unfold preparedPairWithWork pair
  dsimp only
  rw [runWithWork_erasure]
  rfl

theorem preparedPairWithWork_bound (source : BinaryRationalPairProgram.Source) (s : ℕ)
    (hs : 2 ≤ s) (h : source.pair.FieldsHeight s) :
    (preparedPairWithWork source).2 ≤ 218 + 16 * (1 + 2 * (32 * s + 31)) +
      7 * (instructionBound (32 * s + 31) + 2) + 1 := by
  have hTrace := source.trace_wordBounds h hs
  have hInitial := initialWithWork_bound source (32 * s + 31) (trace_start _ _ _ hTrace)
  have hProgram := pairWithWork_bound source s hs h
  unfold preparedPairWithWork
  dsimp only
  change (initialWithWork source).2 + (pairWithWork source).2 ≤ _
  omega

end Blotto.BinaryPRGWordControllerPairRegisters
