import Blotto.PureBoundaryEquilibria
import Blotto.BinaryStoredRowFrameWork
import Blotto.BinaryPRGOutputLifetime
import Blotto.BinaryBooleanPrimitiveLifetime

/-! The one-field boundary returns the player's original stored budget word.
There is no rational re-encoding, sampler arithmetic, or random-bit request.
Actual coordinate framing preserves suffixes, and its bit-cell visits and
every-prefix allocation trace have source-payload-derived bounds. The input
game parser/validity checks and physical record/compiler layout remain the
general caller's obligations. The visit observer and data-only framing trace
are separate source components: constructing the numeric visit observer is
not included in the data-only allocation trace. -/

namespace Blotto.BinaryOneFieldBoundary
open BinaryRationalNormalization BinaryRationalEncoding BinaryPRGOutputLifetime
open BinarySeedPreparationSpace PureBoundaryEquilibria
open scoped BigOperators

def selected (rich : Bool) (budgetA budgetB : SignedWord) : SignedWord :=
  if rich then budgetA else budgetB

def row (budget : SignedWord) : FixedArrayTable 1 SignedWord :=
  FixedArrayTable.ofFn fun _ => budget

def header : List Bool := [false, true, true]

theorem header_value : header = BinaryNatFrame.encode 1 := by decide

def output (rich : Bool) (budgetA budgetB : SignedWord) : List Bool :=
  header ++ BinaryStoredRowFrame.words [selected rich budgetA budgetB]

theorem output_row (rich : Bool) (budgetA budgetB : SignedWord) :
    output rich budgetA budgetB = BinaryStoredRowFrame.row (row (selected rich budgetA budgetB)) := by
  simp [output, BinaryStoredRowFrame.row, row, FixedArrayTable.read_ofFn,
    header_value, List.ofFn_succ]

theorem output_read (rich : Bool) (budgetA budgetB : SignedWord)
    (hA : BinaryRationalOpcode.Valid budgetA) (hB : BinaryRationalOpcode.Valid budgetB)
    (suffix : List Bool) :
    BinaryRatListFrame.readRow (output rich budgetA budgetB ++ suffix) =
      some (1, [value (selected rich budgetA budgetB)], suffix) := by
  rw [output_row]
  have h := BinaryStoredRowFrame.row_read (row (selected rich budgetA budgetB))
    (by intro j; simp only [row, FixedArrayTable.read_ofFn, selected]
        cases rich
        · exact hB
        · exact hA) suffix
  simpa [row, FixedArrayTable.read_ofFn, List.ofFn_succ] using h

def payloadSize (budget : SignedWord) : ℕ := budget.numerator.length + budget.denominator.length

def outputWithWork (rich : Bool) (budgetA budgetB : SignedWord) : List Bool × ℕ :=
  let budget := selected rich budgetA budgetB
  (output rich budgetA budgetB, BinaryStoredRowFrameWork.wordsVisits [budget] + header.length + 8)

theorem outputWithWork_bound (rich : Bool) (budgetA budgetB : SignedWord) :
    (outputWithWork rich budgetA budgetB).2 ≤
      8 * payloadSize (selected rich budgetA budgetB) + 21 := by
  have h := BinaryStoredRowFrameWork.wordsVisits_bound [selected rich budgetA budgetB]
  simp only [BinaryStoredRowFrameWork.storedSpines, List.length_cons, List.length_nil] at h
  unfold outputWithWork payloadSize header
  simp only [List.length_cons, List.length_nil]
  omega

def outputWithTrace (rich : Bool) (budgetA budgetB : SignedWord) : List Bool × Trace :=
  let framed := frameWithTrace header [selected rich budgetA budgetB]
  (framed.1, [.frames 2, .listAllocation 4, .arrayAllocation 4] ++ under 2 framed.2)

theorem outputWithTrace_erasure (rich : Bool) (budgetA budgetB : SignedWord) :
    (outputWithTrace rich budgetA budgetB).1 = output rich budgetA budgetB :=
  frameWithTrace_state _ _

theorem outputWithTrace_bounds (rich : Bool) (budgetA budgetB : SignedWord) :
    listCells (outputWithTrace rich budgetA budgetB).2 +
      arraySlots (outputWithTrace rich budgetA budgetB).2 ≤
        6 * payloadSize (selected rich budgetA budgetB) + 20 := by
  have h := frameWithTrace_cells header [selected rich budgetA budgetB]
  have hArray := frameWithTrace_arrays header [selected rich budgetA budgetB]
  unfold outputWithTrace payloadSize
  simp only [listCells_append, arraySlots_append, listCells, arraySlots,
    listCells_under, arraySlots_under]
  simp only [BinaryStoredRowFrame.words, List.length_append,
    BinaryStoredRowFrameWork.word_length, List.length_nil] at h
  simp only [header, List.length_cons, List.length_nil] at *
  omega

theorem output_all_prefix_heap (rich : Bool) (budgetA budgetB : SignedWord)
    (borrowedInputCells steps : ℕ) :
    retainedHeap borrowedInputCells (outputWithTrace rich budgetA budgetB).2 steps ≤
      borrowedInputCells + 6 * payloadSize (selected rich budgetA budgetB) + 20 :=
  BinaryBooleanPrimitiveLifetime.prefix_heap _ _ _ _ (outputWithTrace_bounds rich budgetA budgetB)

theorem outputWithTrace_frames (rich : Bool) (budgetA budgetB : SignedWord) :
    framePeak (outputWithTrace rich budgetA budgetB).2 ≤
      2 * payloadSize (selected rich budgetA budgetB) + 18 := by
  have h := frameWithTrace_frames header [selected rich budgetA budgetB]
  have hu := framePeak_under 2 (frameWithTrace header [selected rich budgetA budgetB]).2
  unfold outputWithTrace payloadSize
  simp only [framePeak_append, framePeak]
  simp only [BinaryStoredRowFrame.words, List.length_append,
    BinaryStoredRowFrameWork.word_length, List.length_nil, List.length_cons,
    header] at *
  omega

theorem output_all_prefix_frames (rich : Bool) (budgetA budgetB : SignedWord) (steps : ℕ) :
    framePeak ((outputWithTrace rich budgetA budgetB).2.take steps) ≤
      2 * payloadSize (selected rich budgetA budgetB) + 18 :=
  (framePeak_take_le _ _).trans (outputWithTrace_frames rich budgetA budgetB)

noncomputable def law (budget : SignedWord) : Mixed 1 :=
  pointLaw (oneFieldRow (value budget : ℝ))

theorem row_fullBudget (budget : SignedWord) (hBudget : 0 ≤ value budget) :
    FullBudget (value budget : ℝ) (fun j => (value ((row budget).read j) : ℝ)) := by
  have hRow : (fun j => (value ((row budget).read j) : ℝ)) =
      oneFieldRow (value budget : ℝ) := by
    funext j
    simp only [row, FixedArrayTable.read_ofFn]
    rfl
  rw [hRow]
  exact oneFieldRow_fullBudget (value budget : ℝ) (by exact_mod_cast hBudget)

theorem pair_equilibrium (values : Values 1) (budgetA budgetB : SignedWord)
    (hA : 0 ≤ value budgetA) (hB : 0 ≤ value budgetB) :
    Supported (value budgetA : ℝ) (law budgetA) ∧
      Supported (value budgetB : ℝ) (law budgetB) ∧
      regret values (value budgetA : ℝ) (law budgetA) (law budgetB) = 0 ∧
      regret values (value budgetB : ℝ) (law budgetB) (law budgetA) = 0 :=
  oneField_equilibrium values _ _ (by exact_mod_cast hA) (by exact_mod_cast hB)

end Blotto.BinaryOneFieldBoundary
