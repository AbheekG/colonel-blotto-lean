import Blotto.BinaryPrimitiveTracePlan
import Blotto.BinaryCubicOpcodeMeasured
import Blotto.BinaryNormalizationPlan

/-! Ghost unit-case accounting for the actual arithmetic entry counters.
These observers are proofs/specifications, never selected runtime producers.
The count relation follows countFrom's two actual recursive arms. Charges use
actual returned operands, including every selected sign/opcode branch. Retained
cell reservations cover entry scans separately from old source/emission work.
Native scalar/reference/allocator and whole-model joins remain separate. -/
namespace Blotto.BinaryArithmeticEntryWork
open BinaryRationalNormalization BinaryRationalArithmetic BinarySeedPreparationSpace
open BinaryTracePlanMeasured
set_option autoImplicit false
set_option maxHeartbeats 4000000

inductive CountRun : List Bool → ℕ → ℕ → ℕ → Prop where
  | nil (count : ℕ) : CountRun [] count count 1
  | cons (bit : Bool) (rest : List Bool) (count result work : ℕ)
      (later : CountRun rest (count+1) result work) : CountRun (bit::rest) count result (work+1)

theorem count_run (bits : List Bool) (count : ℕ) :
    CountRun bits count (BinaryBorrowDropMetadata.countFrom bits count) (bits.length+1) := by
  induction bits generalizing count with
  | nil => exact .nil count
  | cons bit rest ih => exact .cons bit rest count _ _ (ih (count+1))

theorem count_run_cost {bits : List Bool} {count result work : ℕ}
    (run : CountRun bits count result work) : work=bits.length+1 := by
  induction run with
  | nil => rfl
  | cons bit rest count result work later ih => simp only [List.length_cons]; omega

def unsigned (a b : List Bool) : ℕ := a.length+b.length+2

def signed (a b : BinarySignedMagnitude.Word) : ℕ := unsigned a.bits b.bits

theorem unsigned_add_entries (a b : List Bool) :
    unsigned a b = (BinaryAddMultiplyMetadata.addProduced a b).2.1+
      (BinaryAddMultiplyMetadata.addProduced a b).2.2+2 := by
  rw [BinaryAddMultiplyMetadata.addProduced_lengths]; rfl

theorem unsigned_multiply_entries (a b : List Bool) :
    unsigned a b = (BinaryAddMultiplyMetadata.multiplyProduced a b).2.1+
      (BinaryAddMultiplyMetadata.multiplyProduced a b).2.2+2 := by
  rw [BinaryAddMultiplyMetadata.multiplyProduced_lengths]; rfl

theorem difference_entries (a b : List Bool) :
    unsigned a b = (BinaryCompareSignedMeasured.differenceProduced a b).2.1+
      (BinaryCompareSignedMeasured.differenceProduced a b).2.2+2 := by
  rw [BinaryCompareSignedMeasured.differenceProduced_lengths]; rfl

theorem signed_add_entries (a b : BinarySignedMagnitude.Word) :
    signed a b = (BinaryCompareSignedMeasured.addProduced a b).2.1+
      (BinaryCompareSignedMeasured.addProduced a b).2.2+2 := by
  rw [BinaryCompareSignedMeasured.addProduced_lengths]; rfl

theorem signed_subtract_entries (a b : BinarySignedMagnitude.Word) :
    signed a b = (BinaryCompareSignedMeasured.subtractProduced a b).2.1+
      (BinaryCompareSignedMeasured.subtractProduced a b).2.2+2 := by
  rw [BinaryCompareSignedMeasured.subtractProduced_lengths]; rfl

theorem signed_multiply_entries (a b : BinarySignedMagnitude.Word) :
    signed a b = (BinaryCompareSignedMeasured.multiplyProduced a b).2.1+
      (BinaryCompareSignedMeasured.multiplyProduced a b).2.2+2 := by
  rw [BinaryCompareSignedMeasured.multiplyProduced_lengths]; rfl

def comparison (a b : SignedWord) : ℕ :=
  let left := BinaryCompareSignedMeasured.multiply (numeratorWord a) (denominatorWord b)
  let right := BinaryCompareSignedMeasured.multiply (numeratorWord b) (denominatorWord a)
  signed (numeratorWord a) (denominatorWord b)+signed (numeratorWord b) (denominatorWord a)+
    signed left.data right.data

def addition (a b : SignedWord) : ℕ :=
  let left := BinaryCompareSignedMeasured.multiply (numeratorWord a) (denominatorWord b)
  let right := BinaryCompareSignedMeasured.multiply (numeratorWord b) (denominatorWord a)
  signed (numeratorWord a) (denominatorWord b)+signed (numeratorWord b) (denominatorWord a)+
    signed left.data right.data+unsigned a.denominator b.denominator

def multiplication (a b : SignedWord) : ℕ :=
  signed (numeratorWord a) (numeratorWord b)+unsigned a.denominator b.denominator

def division (a b : SignedWord) : ℕ :=
  unsigned a.numerator b.denominator+unsigned a.denominator b.numerator

theorem zero_division_entries (a b : SignedWord) :
    division a b = (BinaryRationalRawStorageMeasured.wordWidths a).1+
      (BinaryRationalRawStorageMeasured.wordWidths a).2+
      (BinaryRationalRawStorageMeasured.wordWidths b).1+
      (BinaryRationalRawStorageMeasured.wordWidths b).2+4 := by
  simp only [division,unsigned,BinaryRationalRawStorageMeasured.wordWidths_exact]
  omega

def raw : RealArithmeticOp → SignedWord → SignedWord → ℕ
  | .add,a,b => addition a b
  | .sub,a,b => addition a (BinaryRationalArithmetic.negate b)
  | .mul,a,b => multiplication a b
  | .div,a,b => division a b
  | .minimum,a,b => comparison a b
  | .maximum,a,b => comparison a b

theorem comparison_bound (a b : SignedWord) :
    comparison a b ≤ 2*(BinaryRationalComparisonMeasured.compare a b).storage := by
  simp only [comparison,signed,unsigned,BinaryRationalComparisonMeasured.compare_previous_record,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]
  omega

theorem addition_bound (a b : SignedWord) :
    addition a b ≤ 2*(BinaryRationalRawStorageMeasured.add a b).storage := by
  simp only [addition,signed,unsigned,BinaryRationalRawStorageMeasured.add_cached_record,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]
  omega

theorem multiplication_bound (a b : SignedWord) :
    multiplication a b ≤ 2*(BinaryRationalRawStorageMeasured.multiply a b).storage := by
  simp only [multiplication,signed,unsigned,BinaryRationalRawStorageMeasured.multiply_cached_record,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]
  omega

theorem division_bound (a b : SignedWord) :
    division a b ≤ 2*(BinaryRationalRawStorageMeasured.divide a b).storage := by
  simp only [division,unsigned,BinaryRationalRawStorageMeasured.divide_cached_record,
    BinaryRationalOpcodeAllocation.payload]
  omega

theorem raw_bound (op : RealArithmeticOp) (a b : SignedWord) :
    raw op a b ≤ 2*(BinaryRationalRawStorageMeasured.apply op a b).storage := by
  cases op
  · exact addition_bound a b
  · have h := addition_bound a (BinaryRationalArithmetic.negate b)
    simp only [raw,BinaryRationalRawStorageMeasured.apply_previous_record]
    omega
  · exact multiplication_bound a b
  · have h := division_bound a b
    simp only [raw,BinaryRationalRawStorageMeasured.apply_previous_record]
    split
    · dsimp only; omega
    · simp only [division,unsigned,BinaryRationalOpcodeAllocation.payload]
      omega
  · have h := comparison_bound a b
    simp only [raw,BinaryRationalRawStorageMeasured.apply_previous_record]
    omega
  · have h := comparison_bound a b
    simp only [raw,BinaryRationalRawStorageMeasured.apply_previous_record]
    omega

theorem raw_with_work (op : RealArithmeticOp) (a b : SignedWord) :
    raw op a b+(BinaryRationalRawStorageMeasured.apply op a b).work ≤
      2*((BinaryRationalRawStorageMeasured.apply op a b).storage+
        (BinaryRationalRawStorageMeasured.apply op a b).work) := by
  have h := raw_bound op a b
  omega

theorem raw_plan (op : RealArithmeticOp) (a b : SignedWord) (depth : ℕ) :
    raw op a b ≤ 2*listCells (denote (BinaryPrimitiveTracePlan.rawAt op a b depth).1.2) := by
  have h := raw_bound op a b
  simpa only [BinaryPrimitiveTracePlan.rawAt,denote,listCells,Nat.add_zero] using h

theorem cubic_bound (op : RealArithmeticOp) (a b : SignedWord) :
    raw op a b ≤ 2*(BinaryCubicOpcodeMeasured.apply op a b).storage := by
  have h := raw_bound op a b
  simp only [BinaryCubicOpcodeMeasured.apply]
  omega

theorem normalized_plan (op : RealArithmeticOp) (a b : SignedWord) (depth : ℕ) :
    raw op a b ≤ 2*listCells (denote (BinaryNormalizationPlan.applyAt op a b depth).1.2) := by
  have h := raw_plan op a b (depth+2)
  simp only [BinaryNormalizationPlan.applyAt,denote,listCells_append,listCells]
  omega

end Blotto.BinaryArithmeticEntryWork
