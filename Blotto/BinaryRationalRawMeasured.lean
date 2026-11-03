import Blotto.BinarySignedMeasured
import Blotto.BinaryQuadraticLifetime
import Blotto.BinaryRationalRawStorageMeasured

/-! The older value/allocation/work interfaces remain checked references.
The actual traced entry now consumes the storage-fused raw producer, so it
does not replay rawStorage. Source reservations retain their preceding exact
contracts; native observer arithmetic and physical costs remain open. -/

namespace Blotto.BinaryRationalRawMeasured
open BinaryRationalNormalization BinaryRationalArithmetic BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def add (first second : SignedWord) : (SignedWord × ℕ) × ℕ :=
  let left := BinarySignedMeasured.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMeasured.multiply (numeratorWord second) (denominatorWord first)
  let numerator := BinarySignedMeasured.add left.1.1 right.1.1
  let denominator := BinaryArithmeticMeasured.multiply first.denominator second.denominator
  ((⟨numerator.1.1.negative,numerator.1.1.bits,denominator.1.1⟩,
    left.1.2+right.1.2+numerator.1.2+denominator.1.2+4),left.2+right.2+numerator.2+denominator.2+4)

theorem add_erases (first second : SignedWord) :
    (add first second).1 = BinaryRationalOpcodeAllocation.rawAddWithAllocation first second := by
  simp only [add,BinaryRationalOpcodeAllocation.rawAddWithAllocation,BinarySignedMeasured.multiply_erases,
    BinarySignedMeasured.add_erases,BinaryArithmeticMeasured.multiply_erases]

theorem add_work (first second : SignedWord) : (add first second).2 = rawAddWork first second := by
  simp only [add,rawAddWork,BinarySignedMeasured.multiply_work,BinarySignedMeasured.multiply_data,
    BinarySignedMeasured.add_work,BinaryArithmeticMeasured.multiply_work]

def multiply (first second : SignedWord) : (SignedWord × ℕ) × ℕ :=
  let numerator := BinarySignedMeasured.multiply (numeratorWord first) (numeratorWord second)
  let denominator := BinaryArithmeticMeasured.multiply first.denominator second.denominator
  ((⟨numerator.1.1.negative,numerator.1.1.bits,denominator.1.1⟩,numerator.1.2+denominator.1.2+3),
    numerator.2+denominator.2+3)

theorem multiply_erases (first second : SignedWord) :
    (multiply first second).1 = BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation first second := by
  simp only [multiply,BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation,
    BinarySignedMeasured.multiply_erases,BinaryArithmeticMeasured.multiply_erases]

theorem multiply_work (first second : SignedWord) : (multiply first second).2 = rawMultiplyWork first second := by
  simp only [multiply,rawMultiplyWork,BinarySignedMeasured.multiply_work,BinaryArithmeticMeasured.multiply_work]

def divide (first second : SignedWord) : (SignedWord × ℕ) × ℕ :=
  let numerator := BinaryArithmeticMeasured.multiply first.numerator second.denominator
  let denominator := BinaryArithmeticMeasured.multiply first.denominator second.numerator
  ((⟨Bool.xor first.negative second.negative,numerator.1.1,denominator.1.1⟩,
    numerator.1.2+denominator.1.2+4),numerator.2+denominator.2+4)

theorem divide_erases (first second : SignedWord) :
    (divide first second).1 = BinaryRationalOpcodeAllocation.rawDivideWithAllocation first second := by
  simp only [divide,BinaryRationalOpcodeAllocation.rawDivideWithAllocation,BinaryArithmeticMeasured.multiply_erases]

theorem divide_work (first second : SignedWord) : (divide first second).2 = rawDivideWork first second := by
  simp only [divide,rawDivideWork,BinaryArithmeticMeasured.multiply_work]

def lessEqual (first second : SignedWord) : (Bool × ℕ) × ℕ :=
  let left := BinarySignedMeasured.multiply (numeratorWord first) (denominatorWord second)
  let right := BinarySignedMeasured.multiply (numeratorWord second) (denominatorWord first)
  let difference := BinarySignedMeasured.subtract left.1.1 right.1.1
  let scan := BinaryNormalizationAllocation.scanWithFrames difference.1.1.bits
  ((difference.1.1.negative || !scan.1,left.1.2+right.1.2+difference.1.2+scan.2+5),
    left.2+right.2+difference.2+3*(difference.1.1.bits.length+1)+5)

theorem lessEqual_erases (first second : SignedWord) :
    (lessEqual first second).1 = BinaryRationalOpcodeAllocation.lessEqualWithAllocation first second := by
  simp only [lessEqual,BinaryRationalOpcodeAllocation.lessEqualWithAllocation,BinarySignedMeasured.multiply_erases,
    BinarySignedMeasured.subtract_erases]

theorem lessEqual_work (first second : SignedWord) : (lessEqual first second).2 = lessEqualWork first second := by
  simp only [lessEqual,lessEqualWork,BinarySignedMeasured.multiply_work,BinarySignedMeasured.multiply_data,
    BinarySignedMeasured.subtract_work,BinarySignedMeasured.subtract_data]

def apply : RealArithmeticOp → SignedWord → SignedWord → (SignedWord × ℕ) × ℕ
  | .add,first,second => add first second
  | .sub,first,second =>
      let result := add first (BinaryRationalArithmetic.negate second)
      ((result.1.1,result.1.2+1),1+result.2)
  | .mul,first,second => multiply first second
  | .div,first,second =>
      let scan := BinaryNormalizationAllocation.scanWithFrames second.numerator
      if scan.1 then
        let result := divide first second
        ((result.1.1,result.1.2+scan.2+2),3*(second.numerator.length+1)+2+result.2)
      else ((BinaryRationalOpcode.zero,scan.2+3),3*(second.numerator.length+1)+2+2)
  | .minimum,first,second =>
      let compared := lessEqual first second
      ((if compared.1.1 then first else second,compared.1.2+2),compared.2+2)
  | .maximum,first,second =>
      let compared := lessEqual first second
      ((if compared.1.1 then second else first,compared.1.2+2),compared.2+2)

theorem apply_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1 = BinaryRationalOpcodeAllocation.rawApplyWithAllocation op first second := by
  cases op <;> simp only [apply,BinaryRationalOpcodeAllocation.rawApplyWithAllocation,
    add_erases,multiply_erases,divide_erases,lessEqual_erases]
  split <;> rename_i hScan <;> simp only [hScan,Bool.false_eq_true,ite_true,ite_false]

theorem apply_data (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1.1 = BinaryRationalOpcode.rawApply op first second := by
  rw [apply_erases,BinaryRationalOpcodeAllocation.rawApplyWithAllocation_state]

theorem apply_work (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).2 = BinaryRationalOpcode.rawApplyWork op first second := by
  cases op <;> simp only [apply,BinaryRationalOpcode.rawApplyWork,add_work,multiply_work,divide_work,
    lessEqual_work,BinaryNormalizationAllocation.scanWithFrames_state]
  by_cases hScan : BinaryEuclideanGCD.nonzero second.numerator = true <;>
    simp only [hScan,Bool.false_eq_true,ite_true,ite_false]

def traced (op : RealArithmeticOp) (first second : SignedWord) : (SignedWord × Trace) × ℕ :=
  BinaryRationalRawStorageMeasured.traced op first second

theorem traced_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).1 = BinaryQuadraticLifetime.rawWithTrace op first second :=
  BinaryRationalRawStorageMeasured.traced_erases _ _ _

theorem traced_data (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).1.1 = BinaryRationalOpcode.rawApply op first second :=
  BinaryRationalRawStorageMeasured.traced_data _ _ _

theorem traced_work (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).2 = BinaryRationalOpcode.rawApplyWork op first second :=
  BinaryRationalRawStorageMeasured.traced_work _ _ _

end Blotto.BinaryRationalRawMeasured
