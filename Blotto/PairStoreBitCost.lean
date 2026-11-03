import Blotto.PairStoreRationalHeight
import Blotto.RationalCostModel
import Blotto.RationalExpressionBitCost

/-! Operand-sized prices for the typed pair-store program. Four-cell scratch
writes allow full copying. Resource writes have separate logical-RAM and
full-native-copy prices; the latter does not certify linear PRG execution. -/

namespace Blotto.PairStoreState

def WordBounds {n : ℕ} (state : PairStoreState n ℚ) (W : ℕ) : Prop :=
  (∀ j, rationalWordWidth (state.cells.read j) ≤ W) ∧
    ∀ r, rationalWordWidth (state.registers.read r) ≤ W

end Blotto.PairStoreState
namespace Blotto.PairStoreBuffer
open scoped BigOperators

def copyBitCost {n : ℕ} (buffer : PairStoreBuffer n ℚ) : ℕ :=
  ∑ j : Fin n, rationalWordWidth (buffer.read j)

theorem copyBitCost_bound {n : ℕ} (model : RationalCostModel) (buffer : PairStoreBuffer n ℚ) (W : ℕ)
    (h : ∀ j, rationalWordWidth (buffer.read j) ≤ W) : buffer.copyBitCost ≤ n * model.rat W := by
  have hSum := Finset.sum_le_sum (s := (Finset.univ : Finset (Fin n)))
    (f := fun j => rationalWordWidth (buffer.read j)) (g := fun _ => model.rat W)
    (fun j _ => (h j).trans (model.word_le W))
  have hConst : (∑ _j : Fin n, model.rat W) = n * model.rat W := by simp
  exact hSum.trans_eq hConst

end Blotto.PairStoreBuffer
namespace Blotto.PairStoreInstruction

def bitUnits {n : ℕ} (copyResources : Bool) (instruction : PairStoreInstruction n) : ℕ :=
  instruction.resourceReads + instruction.resourceWrites + instruction.registerReads +
    instruction.registerWrites + instruction.arithmeticCalls + 3 * instruction.registerWrites +
    if copyResources then (n - 1) * instruction.resourceWrites else 0

def bitCost {n : ℕ} (model : RationalCostModel) (copyResources : Bool)
    (instruction : PairStoreInstruction n) (state : PairStoreState n ℚ) : ℕ :=
  match instruction with
  | .load cell _ => rationalWordWidth (state.cells.read cell) + (instruction.execute state).registers.copyBitCost
  | .add _ left right | .sub _ left right =>
    rationalWordWidth (state.registers.read left) + rationalWordWidth (state.registers.read right) +
      model.rat (RationalExpression.pairWidth (state.registers.read left) (state.registers.read right)) +
      (instruction.execute state).registers.copyBitCost
  | .store _ source => rationalWordWidth (state.registers.read source) +
      if copyResources then (instruction.execute state).cells.copyBitCost else rationalWordWidth (state.registers.read source)

theorem bitCost_bound {n : ℕ} (model : RationalCostModel) (copyResources : Bool)
    (instruction : PairStoreInstruction n) (state : PairStoreState n ℚ) (W : ℕ)
    (hBefore : state.WordBounds W) (hAfter : (instruction.execute state).WordBounds W) :
    instruction.bitCost model copyResources state ≤ instruction.bitUnits copyResources * model.rat W := by
  have hRegisters := PairStoreBuffer.copyBitCost_bound model (instruction.execute state).registers W hAfter.2
  have hCells := PairStoreBuffer.copyBitCost_bound model (instruction.execute state).cells W hAfter.1
  cases instruction with
  | load cell destination =>
    have hRead := (hBefore.1 cell).trans (model.word_le W)
    cases copyResources <;> simp only [bitCost, bitUnits, resourceReads, resourceWrites, registerReads,
      registerWrites, arithmeticCalls, Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero, Nat.add_zero] <;> omega
  | add destination left right | sub destination left right =>
    have hLeft := (hBefore.2 left).trans (model.word_le W)
    have hRight := (hBefore.2 right).trans (model.word_le W)
    have hCall := model.monotone (show
      RationalExpression.pairWidth (state.registers.read left) (state.registers.read right) ≤ W
        from max_le (hBefore.2 left) (hBefore.2 right))
    cases copyResources <;> simp only [bitCost, bitUnits, resourceReads, resourceWrites, registerReads,
      registerWrites, arithmeticCalls, Bool.false_eq_true, ite_false, ite_true, Nat.mul_zero, Nat.add_zero] <;> omega
  | store cell source =>
    have hRead := (hBefore.2 source).trans (model.word_le W)
    have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) cell.isLt
    cases copyResources <;> simp only [bitCost, bitUnits, resourceReads, resourceWrites, registerReads,
      registerWrites, arithmeticCalls, Bool.false_eq_true, ite_false, ite_true, Nat.mul_one, Nat.mul_zero, Nat.add_zero]
    · omega
    · have hUnits : 2 + (n - 1) = n + 1 := by omega
      nlinarith

end Blotto.PairStoreInstruction
namespace Blotto.PairStoreProgram

theorem run_append {n : ℕ} (first second : List (PairStoreInstruction n)) (state : PairStoreState n ℚ) :
    run (first ++ second) state = run second (run first state) := by
  induction first generalizing state with
  | nil => rfl
  | cons instruction rest ih => exact ih (instruction.execute state)

def bitCost {n : ℕ} (model : RationalCostModel) (copyResources : Bool) :
    List (PairStoreInstruction n) → PairStoreState n ℚ → ℕ
  | [], _ => 0
  | instruction :: rest, state => instruction.bitCost model copyResources state +
      bitCost model copyResources rest (instruction.execute state)

theorem bitCost_bound {n : ℕ} (model : RationalCostModel) (copyResources : Bool)
    (program : List (PairStoreInstruction n)) (state : PairStoreState n ℚ) (W : ℕ)
    (hPrefixes : ∀ k, (run (program.take k) state).WordBounds W) :
    bitCost model copyResources program state ≤ (program.map (PairStoreInstruction.bitUnits copyResources)).sum * model.rat W := by
  induction program generalizing state with
  | nil => simp [bitCost]
  | cons instruction rest ih =>
    have hBefore : state.WordBounds W := hPrefixes 0
    have hAfter : (instruction.execute state).WordBounds W := hPrefixes 1
    have hRest : ∀ k, (run (rest.take k) (instruction.execute state)).WordBounds W := by
      intro k
      exact hPrefixes (k + 1)
    have hInstruction := instruction.bitCost_bound model copyResources state W hBefore hAfter
    have hTail := ih (instruction.execute state) hRest
    simp only [bitCost, List.map_cons, List.sum_cons]
    nlinarith

def updateBitCost {n : ℕ} (model : RationalCostModel) (copyResources : Bool)
    (cells : PairStoreBuffer n ℚ) (i j : Fin n) (z : ℚ) : ℕ :=
  (initial cells z).registers.copyBitCost + bitCost model copyResources (code i j) (initial cells z)

theorem bitUnits_code {n : ℕ} (copyResources : Bool) (i j : Fin n) :
    4 + ((code i j).map (PairStoreInstruction.bitUnits copyResources)).sum =
      if copyResources then 2 * n + 30 else 32 := by
  have hn : 0 < n := Nat.lt_of_le_of_lt (Nat.zero_le _) i.isLt
  cases copyResources with
  | false => rfl
  | true =>
    simp [code, PairStoreInstruction.bitUnits, PairStoreInstruction.resourceReads,
      PairStoreInstruction.resourceWrites, PairStoreInstruction.registerReads, PairStoreInstruction.registerWrites,
      PairStoreInstruction.arithmeticCalls]
    omega

theorem updateBitCost_bound {n : ℕ} (model : RationalCostModel) (copyResources : Bool)
    (cells : PairStoreBuffer n ℚ) (i j : Fin n) (z : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hCells : ∀ r, RationalHeight (cells.read r) s) (hZ : RationalHeight z s) :
    updateBitCost model copyResources cells i j z ≤
      (if copyResources then 2 * n + 30 else 32) * model.rat (8 * s + 7) := by
  have hPrefixes : ∀ k, (run ((code i j).take k) (initial cells z)).WordBounds (8 * s + 7) :=
    fun k => prefixes_wordWidth cells i j z s hs hCells hZ k
  have hInitial : (initial cells z).WordBounds (8 * s + 7) := hPrefixes 0
  have hCopy := PairStoreBuffer.copyBitCost_bound model (initial cells z).registers (8 * s + 7) hInitial.2
  have hRun := bitCost_bound model copyResources (code i j) (initial cells z) (8 * s + 7) hPrefixes
  have hUnits := bitUnits_code copyResources i j
  unfold updateBitCost
  nlinarith

end Blotto.PairStoreProgram
