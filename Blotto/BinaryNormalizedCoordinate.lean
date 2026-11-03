import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryPhysicalInterpolationWork

/-! The actual affine-coordinate producer retains each planned opcode's
division/emission extras while sharing its returned word, trace and source
charge. Counter evaluation and full native/physical models remain separate. -/
namespace Blotto.BinaryNormalizedCoordinate
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option autoImplicit false

def opcode (op : RealArithmeticOp) (first second : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryNormalizationPlan.apply op first second
  (produced.1.1,produced.1.2+produced.2)

theorem opcode_record (op : RealArithmeticOp) (first second : SignedWord) :
    (opcode op first second).1 = BinaryPlannedQuadratic.apply op first second := rfl

theorem opcode_extra (op : RealArithmeticOp) (first second : SignedWord) :
    (opcode op first second).2 = BinaryPlannedQuadratic.extra op first second := rfl

def coordinate (first second scalar : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let complement := opcode .sub BinaryPRGRecognition.one scalar
  let left := opcode .mul complement.1.1.1 first
  let right := opcode .mul scalar second
  let joined := opcode .add left.1.1.1 right.1.1.1
  (((joined.1.1.1,wrap 64 2 [complement.1.1.2,left.1.1.2,right.1.1.2,joined.1.1.2]),
    complement.1.2+left.1.2+right.1.2+joined.1.2+16),
    complement.2+left.2+right.2+joined.2)

theorem coordinate_record (first second scalar : SignedWord) :
    (coordinate first second scalar).1 =
      let complement := BinaryPlannedQuadratic.apply .sub BinaryPRGRecognition.one scalar
      let left := BinaryPlannedQuadratic.apply .mul complement.1.1 first
      let right := BinaryPlannedQuadratic.apply .mul scalar second
      let joined := BinaryPlannedQuadratic.apply .add left.1.1 right.1.1
      ((joined.1.1,wrap 64 2 [complement.1.2,left.1.2,right.1.2,joined.1.2]),
        complement.2+left.2+right.2+joined.2+16) := by
  simp only [coordinate,opcode_record]

def canonicalize (word : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let produced := BinaryNormalizationPlan.canonicalize word
  (produced.1.1,produced.1.2+produced.2)

theorem canonicalize_record (word : SignedWord) :
    (canonicalize word).1 = BinaryQuadraticMeasured.canonicalize word := by
  simp only [canonicalize,BinaryNormalizationPlan.canonicalize_compat,BinaryQuadraticMeasured.canonicalize]

end Blotto.BinaryNormalizedCoordinate
