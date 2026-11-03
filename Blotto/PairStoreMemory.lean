import Blotto.Rounding

/-! A typed read/write RAM for one resource buffer and four scratch registers.
Its resource and register addresses are disjoint by construction. Instructions
never allocate or resize either region. Native array evaluation is a value
implementation; unit RAM writes do not assert Lean reference-count uniqueness. -/

namespace Blotto

structure PairStoreBuffer (n : ℕ) (α : Type*) where
  data : Array α
  size : data.size = n

namespace PairStoreBuffer

def read {n : ℕ} {α : Type*} (b : PairStoreBuffer n α) (i : Fin n) : α :=
  b.data[i.val]'(by rw [b.size]; exact i.isLt)

def write {n : ℕ} {α : Type*} (b : PairStoreBuffer n α) (i : Fin n) (value : α) : PairStoreBuffer n α :=
  ⟨b.data.set i.val value (by rw [b.size]; exact i.isLt), by simp [b.size]⟩

def ofFn {n : ℕ} {α : Type*} (f : Fin n → α) : PairStoreBuffer n α :=
  ⟨Array.ofFn f, Array.size_ofFn⟩

theorem read_write {n : ℕ} {α : Type*} (b : PairStoreBuffer n α) (i j : Fin n) (value : α) :
    (b.write i value).read j = if j = i then value else b.read j := by
  simp [read, write, Array.getElem_set, Fin.ext_iff, eq_comm]

theorem read_ofFn {n : ℕ} {α : Type*} (f : Fin n → α) (i : Fin n) : (ofFn f).read i = f i := by
  simp [read, ofFn]

end PairStoreBuffer

abbrev PairStoreAddress (n : ℕ) := Fin n ⊕ Fin 4

theorem pairStoreRegions_disjoint {n : ℕ} (i : Fin n) (r : Fin 4) :
    (Sum.inl i : PairStoreAddress n) ≠ Sum.inr r := by intro h; cases h

structure PairStoreState (n : ℕ) (α : Type*) where
  cells : PairStoreBuffer n α
  registers : PairStoreBuffer 4 α

inductive PairStoreInstruction (n : ℕ) where
  | load (cell : Fin n) (destination : Fin 4)
  | add (destination left right : Fin 4)
  | sub (destination left right : Fin 4)
  | store (cell : Fin n) (source : Fin 4)

namespace PairStoreInstruction

def execute {n : ℕ} {α : Type*} [Add α] [Sub α] :
    PairStoreInstruction n → PairStoreState n α → PairStoreState n α
  | .load cell destination, s => { s with registers := s.registers.write destination (s.cells.read cell) }
  | .add destination left right, s =>
    { s with registers := s.registers.write destination (s.registers.read left + s.registers.read right) }
  | .sub destination left right, s =>
    { s with registers := s.registers.write destination (s.registers.read left - s.registers.read right) }
  | .store cell source, s => { s with cells := s.cells.write cell (s.registers.read source) }

def resourceReads {n : ℕ} : PairStoreInstruction n → ℕ
  | .load _ _ => 1
  | _ => 0

def resourceWrites {n : ℕ} : PairStoreInstruction n → ℕ
  | .store _ _ => 1
  | _ => 0

def registerReads {n : ℕ} : PairStoreInstruction n → ℕ
  | .add _ _ _ | .sub _ _ _ => 2
  | .store _ _ => 1
  | .load _ _ => 0

def registerWrites {n : ℕ} : PairStoreInstruction n → ℕ
  | .store _ _ => 0
  | _ => 1

def arithmeticCalls {n : ℕ} : PairStoreInstruction n → ℕ
  | .add _ _ _ | .sub _ _ _ => 1
  | _ => 0

end PairStoreInstruction
namespace PairStoreProgram

def run {n : ℕ} {α : Type*} [Add α] [Sub α] : List (PairStoreInstruction n) → PairStoreState n α → PairStoreState n α
  | [], s => s
  | instruction :: rest, s => run rest (instruction.execute s)

def code {n : ℕ} (i j : Fin n) : List (PairStoreInstruction n) :=
  [.load i 1, .load j 2, .add 3 1 2, .sub 3 3 0, .store i 0, .store j 3]

def initial {n : ℕ} {α : Type*} [Zero α] (cells : PairStoreBuffer n α) (z : α) : PairStoreState n α :=
  ⟨cells, PairStoreBuffer.ofFn ![z, 0, 0, 0]⟩

def update {n : ℕ} {α : Type*} [Zero α] [Add α] [Sub α]
    (cells : PairStoreBuffer n α) (i j : Fin n) (z : α) : PairStoreBuffer n α :=
  (run (code i j) (initial cells z)).cells

theorem update_eq {n : ℕ} {α : Type*} [Zero α] [Add α] [Sub α]
    (cells : PairStoreBuffer n α) (i j : Fin n) (z : α) :
    update cells i j z = (cells.write i z).write j (cells.read i + cells.read j - z) := by
  simp [update, run, code, initial, PairStoreInstruction.execute,
    PairStoreBuffer.read_write, PairStoreBuffer.read_ofFn]

theorem reads_before_stores {n : ℕ} {α : Type*} [Zero α] [Add α] [Sub α]
    (cells : PairStoreBuffer n α) (i j : Fin n) (z : α) :
    (run ((code i j).take 4) (initial cells z)).cells = cells := rfl

theorem update_untouched {n : ℕ} {α : Type*} [Zero α] [Add α] [Sub α]
    (cells : PairStoreBuffer n α) (i j r : Fin n) (z : α) (hri : r ≠ i) (hrj : r ≠ j) :
    (update cells i j z).read r = cells.read r := by
  rw [update_eq]
  simp only [PairStoreBuffer.read_write, ite_eq_right hrj, ite_eq_right hri]

theorem region_sizes {n : ℕ} {α : Type*} [Add α] [Sub α]
    (program : List (PairStoreInstruction n)) (s : PairStoreState n α) :
    (run program s).cells.data.size = n ∧ (run program s).registers.data.size = 4 :=
  ⟨(run program s).cells.size, (run program s).registers.size⟩

theorem address_count (n : ℕ) : Fintype.card (PairStoreAddress n) = n + 4 := by simp [PairStoreAddress]

theorem resourceReads {n : ℕ} (i j : Fin n) : ((code i j).map PairStoreInstruction.resourceReads).sum = 2 := rfl
theorem resourceWrites {n : ℕ} (i j : Fin n) : ((code i j).map PairStoreInstruction.resourceWrites).sum = 2 := rfl
theorem registerReads {n : ℕ} (i j : Fin n) : ((code i j).map PairStoreInstruction.registerReads).sum = 6 := rfl
theorem registerWrites {n : ℕ} (i j : Fin n) : ((code i j).map PairStoreInstruction.registerWrites).sum = 4 := rfl
theorem arithmeticCalls {n : ℕ} (i j : Fin n) : ((code i j).map PairStoreInstruction.arithmeticCalls).sum = 2 := rfl

-- Four initial scratch writes plus the priced reads, writes and operations.
def ramWork {n : ℕ} (i j : Fin n) : ℕ :=
  4 + ((code i j).map PairStoreInstruction.resourceReads).sum +
    ((code i j).map PairStoreInstruction.resourceWrites).sum +
    ((code i j).map PairStoreInstruction.registerReads).sum +
    ((code i j).map PairStoreInstruction.registerWrites).sum +
    ((code i j).map PairStoreInstruction.arithmeticCalls).sum

theorem ramWork_eq {n : ℕ} (i j : Fin n) : ramWork i j = 20 := rfl

-- Scratch writes may copy their four cells. Resource writes stay RAM stores.
def scratchCopyWork {n : ℕ} (i j : Fin n) : ℕ :=
  ramWork i j + 3 * ((code i j).map PairStoreInstruction.registerWrites).sum

theorem scratchCopyWork_eq {n : ℕ} (i j : Fin n) : scratchCopyWork i j = 32 := rfl

-- A separate allowance permits both native persistent resource writes to copy.
def nativeCopyWork {n : ℕ} (i j : Fin n) : ℕ := scratchCopyWork i j + 2 * (n - 1)

theorem nativeCopyWork_eq {n : ℕ} (i j : Fin n) : nativeCopyWork i j = 2 * n + 30 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  rw [nativeCopyWork, scratchCopyWork_eq]
  omega

end PairStoreProgram
end Blotto
