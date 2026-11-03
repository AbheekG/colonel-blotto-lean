import Blotto.GeneralPaperNativeSortedRows

/-! Model-specific stored-row sorting with derived local array/control
words. Rational height assumptions are erased price proofs; sorting reads
the actual stored values and constructs its own fuel. -/
namespace Blotto.GeneralPaperNativeSortedModels
open GeneralPaperSourceRowsExecution GeneralPaperSummaryArrayExecution
open GeneralPaperDecodeBucketExecution (primitive)
set_option autoImplicit false
set_option maxHeartbeats 1600000

def one {R : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) : FixedArrayTable R ℚ × ℕ :=
  GeneralPaperNativeSortedRows.one (primitive bits model) (index bits) (address bits W R) values

theorem one_data {R : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) :
    (one bits model W values).1=FixedArrayTable.ofFn (fun a => values.read ((GeneralPaperRowSort.order values).read a)) :=
  GeneralPaperNativeSortedRows.one_data _ _ _ _

theorem one_models {R : ℕ} (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) :
    (one true model W values).1=(one false model 1 values).1 := by rw [one_data,one_data]

theorem one_real {R : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ) (values : FixedArrayTable R ℚ) (a : Fin R) :
    ((one bits model W values).1.read a:ℝ)=GeneralPaperCircleSortedComparison.sorted (fun j => (values.read j:ℝ)) a :=
  GeneralPaperNativeSortedRows.one_real _ _ _ _ a

theorem one_bit_work {R : ℕ} (model : RationalCostModel) (W H : ℕ) (values : FixedArrayTable R ℚ)
    (h : ∀ j,rationalWordWidth (values.read j)≤H) :
    (one true model W values).2≤GeneralPaperNativeSortedRows.oneProfile R (arrayWord W R) (model.rat H) :=
  GeneralPaperNativeSortedRows.one_work model.rat (fun w => w) model.monotone _ H
    (GeneralPaperSummaryArrayControls.array_word_positive W R) values h (GeneralPaperSummaryArrayControls.array_index W R)

theorem one_arithmetic_work {R : ℕ} (model : RationalCostModel) (values : FixedArrayTable R ℚ) :
    (one false model 1 values).2≤GeneralPaperNativeSortedRows.oneProfile R 1 1 := by
  let H := ∑ j,rationalWordWidth (values.read j)
  have h : ∀ j,rationalWordWidth (values.read j)≤H := fun j =>
    Finset.single_le_sum (f:=fun j => rationalWordWidth (values.read j)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  exact GeneralPaperNativeSortedRows.one_work (fun _ => 1) (fun _ => 1) (fun _ _ _ => le_rfl) 1 H (by decide)
    values h (fun _ _ => le_rfl)

def matrix {T R : ℕ} (bits : Bool) (model : RationalCostModel) (W : ℕ)
    (rows : FixedArrayTable T (FixedArrayTable R ℚ)) : FixedArrayTable T (FixedArrayTable R ℚ) × ℕ :=
  GeneralPaperNativeSortedRows.matrix (primitive bits model) (index bits) (address bits W T) (address bits W R) rows

theorem matrix_models {T R : ℕ} (model : RationalCostModel) (W : ℕ) (rows : FixedArrayTable T (FixedArrayTable R ℚ)) :
    (matrix true model W rows).1=(matrix false model 1 rows).1 := by
  unfold matrix
  rw [GeneralPaperNativeSortedRows.matrix_data,GeneralPaperNativeSortedRows.matrix_data]
  congr 1
  funext r
  rw [GeneralPaperNativeSortedRows.one_data,GeneralPaperNativeSortedRows.one_data]

theorem matrix_bit_work {T R : ℕ} (model : RationalCostModel) (W H : ℕ)
    (rows : FixedArrayTable T (FixedArrayTable R ℚ)) (h : ∀ r j,rationalWordWidth ((rows.read r).read j)≤H) :
    (matrix true model W rows).2≤
      T*(GeneralPaperNativeSortedRows.oneProfile R (arrayWord W R) (model.rat H)+64*arrayWord W T)+44*(T+1)*arrayWord W T :=
  GeneralPaperNativeSortedRows.matrix_work model.rat (fun w => w) model.monotone _ _ H
    (GeneralPaperSummaryArrayControls.array_word_positive W T) (GeneralPaperSummaryArrayControls.array_word_positive W R)
    rows h (GeneralPaperSummaryArrayControls.array_index W T) (GeneralPaperSummaryArrayControls.array_index W R)

end Blotto.GeneralPaperNativeSortedModels
