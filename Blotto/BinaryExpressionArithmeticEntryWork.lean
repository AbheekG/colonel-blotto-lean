import Blotto.BinaryPreparationArithmeticEntryWork
import Blotto.BinaryQuadraticExpressionMeasured
import Blotto.BinaryGroupEmissionMeasured

/-! Proof-only raw/comparison entry charges for the actual quadratic expression
source, chosen conditionals and array callbacks. Route emission consumes the
actual prepared uniform row and returned pivot operand. Native costs are separate. -/
namespace Blotto.BinaryExpressionArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
open BinaryRationalExpression
set_option autoImplicit false
set_option maxHeartbeats 5000000

theorem quadratic_bound (op : RealArithmeticOp) (a b : SignedWord) :
    BinaryArithmeticEntryWork.raw op a b ≤ 2*listCells (BinaryQuadraticMeasured.apply op a b).1.2 := by
  have h := BinaryArithmeticEntryWork.raw_bound op a b
  simp only [BinaryQuadraticMeasured.apply,BinaryQuadraticMeasured.applyMeasured,
    BinaryRationalRawMeasured.traced,BinaryRationalRawStorageMeasured.traced,
    listCells_append,listCells_under,listCells]
  omega

theorem comparison_bound (a b : SignedWord) :
    BinaryArithmeticEntryWork.comparison a b ≤
      2*listCells (BinaryQuadraticExpressionMeasured.compare a b).1.2 := by
  simpa only [BinaryQuadraticExpressionMeasured.compare,listCells,Nat.add_zero] using
    BinaryArithmeticEntryWork.comparison_bound a b

def expression {k : ℕ} (env : FixedArrayTable k SignedWord) : BinaryRationalExpression k → ℕ
  | .input _ => 0
  | .literal _ => 0
  | .add a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .add
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .sub a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .sub
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .mul a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .mul
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .div a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .div
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .minimum a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .minimum
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .maximum a b => expression env a+expression env b+BinaryArithmeticEntryWork.raw .maximum
      (BinaryQuadraticExpressionMeasured.evaluate env a).1.1 (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
  | .ifLe a b yes no =>
      let x := BinaryQuadraticExpressionMeasured.evaluate env a
      let y := BinaryQuadraticExpressionMeasured.evaluate env b
      expression env a+expression env b+BinaryArithmeticEntryWork.comparison x.1.1 y.1.1+
        if (BinaryQuadraticExpressionMeasured.compare x.1.1 y.1.1).1.1 then expression env yes else expression env no

theorem expression_bound {k : ℕ} (env : FixedArrayTable k SignedWord) (e : BinaryRationalExpression k) :
    expression env e ≤ 2*listCells (BinaryQuadraticExpressionMeasured.evaluate env e).1.2 := by
  induction e with
  | input _ | literal _ => simp only [expression,BinaryQuadraticExpressionMeasured.evaluate_record,listCells]; omega
  | add a b ha hb =>
    have h := quadratic_bound .add (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | sub a b ha hb =>
    have h := quadratic_bound .sub (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | mul a b ha hb =>
    have h := quadratic_bound .mul (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | div a b ha hb =>
    have h := quadratic_bound .div (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | minimum a b ha hb =>
    have h := quadratic_bound .minimum (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | maximum a b ha hb =>
    have h := quadratic_bound .maximum (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
      (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
    rw [BinaryQuadraticExpressionMeasured.evaluate_record]
    simp only [BinaryPlannedQuadratic.apply_previous,expression,BinaryQuadraticExpressionMeasured.combine_record,
      listCells_append,listCells_under,listCells]
    omega
  | ifLe a b yes no ha hb hy hn =>
      have h := comparison_bound (BinaryQuadraticExpressionMeasured.evaluate env a).1.1
        (BinaryQuadraticExpressionMeasured.evaluate env b).1.1
      rw [BinaryQuadraticExpressionMeasured.evaluate_record]
      simp only [expression]
      split <;> simp only [listCells_append,listCells_under,listCells] <;> omega

def tableCost : (n : ℕ) → (Fin n → ℕ) → ℕ
  | 0,_ => 0
  | n+1,cost => cost 0+tableCost n (fun j => cost j.succ)

theorem enumerate_bound {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) (cost : Fin n → ℕ)
    (h : ∀ j,cost j ≤ 2*listCells (produce j).1.2) :
    tableCost n cost ≤ 2*BinaryPreparationArithmeticEntryWork.entryCells (BinaryLifetimeArrayMeasured.enumerate n produce).1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
      have hf := h 0
      have ht := ih (fun j => produce j.succ) (fun j => cost j.succ) (fun j => h j.succ)
      simp only [tableCost,BinaryLifetimeArrayMeasured.enumerate,BinaryPreparationArithmeticEntryWork.entryCells]
      omega

theorem build_bound {α : Type*} (n : ℕ) (produce : Fin n → (α × Trace) × ℕ) (cost : Fin n → ℕ)
    (h : ∀ j,cost j ≤ 2*listCells (produce j).1.2) :
    tableCost n cost ≤ 2*listCells (BinaryLifetimeArrayMeasured.build n produce).1.2 := by
  have he := enumerate_bound n produce cost h
  rw [BinaryPreparationArithmeticEntryWork.entryCells_flatten] at he
  simp only [BinaryLifetimeArrayMeasured.build,BinaryLifetimeFlattenList.flattenDirect_result,
    listCells_append,listCells_under,listCells]
  omega

def cell {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) : ℕ :=
  match (routes.read j).1 with
  | none => 0
  | some g => BinaryArithmeticEntryWork.raw .mul (routes.read j).2 (row.read g)

theorem cell_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) (j : Fin n) :
    cell routes row j ≤ 2*listCells (BinaryGroupEmissionMeasured.cell routes row j).1.2 := by
  simp only [BinaryGroupEmissionMeasured.cell_record,BinaryPlannedQuadratic.apply_previous]
  split
  · rename_i hNone
    simp only [cell,hNone]
    omega
  · rename_i g hSome
    simpa only [cell,hSome] using quadratic_bound .mul (routes.read j).2 (row.read g)

def emit {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) : ℕ := tableCost n (cell routes row)

theorem emit_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m))
    (row : FixedArrayTable m SignedWord) :
    emit routes row ≤ 2*listCells (BinaryGroupEmissionMeasured.emit routes row).1.2 := by
  rw [BinaryGroupEmissionMeasured.emit_record]
  exact build_bound n (BinaryGroupEmissionMeasured.cell routes row) (cell routes row) (cell_bound routes row)

def mixed {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) : ℕ :=
  let uniform := BinaryGroupEmissionMeasured.subrow row
  let emitted := BinaryGroupEmissionMeasured.emit routes uniform.1.1
  emit routes uniform.1.1+BinaryArithmeticEntryWork.raw .add (emitted.1.1.read pivot) (row.read (Fin.last m))

theorem mixed_bound {n m : ℕ} (routes : FixedArrayTable n (BinaryGroupRoutes.Route m)) (pivot : Fin n)
    (row : FixedArrayTable (m+1) SignedWord) :
    mixed routes pivot row ≤ 2*listCells (BinaryGroupEmissionMeasured.emitMixed routes pivot row).1.2 := by
  have he := emit_bound routes (BinaryGroupEmissionMeasured.subrow row).1.1
  have ha := quadratic_bound .add
    ((BinaryGroupEmissionMeasured.emit routes (BinaryGroupEmissionMeasured.subrow row).1.1).1.1.read pivot)
    (row.read (Fin.last m))
  simp only [BinaryPlannedQuadratic.apply_previous,mixed,BinaryGroupEmissionMeasured.emitMixed_record,wrap,combine,listCells_append,listCells_under,listCells]
  omega

end Blotto.BinaryExpressionArithmeticEntryWork
