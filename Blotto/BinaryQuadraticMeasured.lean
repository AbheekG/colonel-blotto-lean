import Blotto.BinaryRationalRawMeasured
import Blotto.BinarySteinGCDMeasured
import Blotto.BinaryDivisionStorageMeasured

/-! Actual raw arithmetic, Stein GCD, two restoring divisions, sign scan and
canonical trims produce the same word/trace and the same quadratic source-work
charge together. All trace/allocation/work fields are ghost instruments; these
equalities do not price their native evaluation or physical allocator behavior. -/

namespace Blotto.BinaryQuadraticMeasured
open BinaryRationalNormalization BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000

def normalizeMeasured (word : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let common := BinarySteinGCDMeasured.gcd word.numerator word.denominator
  let numerator := BinaryDivisionStorageMeasured.tracedMeasured word.numerator common.1.1
  let denominator := BinaryDivisionStorageMeasured.tracedMeasured word.denominator common.1.1
  let sign := BooleanFreshSeedMeasured.scan numerator.1.1.1.1
  (((⟨word.negative && sign.1.1,numerator.1.1.1.1,denominator.1.1.1.1⟩,
    [.frames 2,.arrayAllocation 16]++under 2 common.1.2++under 2 numerator.1.1.2++
      under 2 denominator.1.1.2++under 2 sign.1.2),
    common.2+numerator.1.2+denominator.1.2+3*(word.numerator.length+1)+2),numerator.2+denominator.2)

def normalize (word : SignedWord) : (SignedWord × Trace) × ℕ := (normalizeMeasured word).1

theorem normalizeMeasured_compat (word : SignedWord) : (normalizeMeasured word).1 = normalize word := rfl

theorem normalize_erases (word : SignedWord) :
    (normalize word).1 = BinaryQuadraticLifetime.normalizeWithTrace word := by
  simp only [normalize,normalizeMeasured,BinaryDivisionStorageMeasured.tracedMeasured_compat,
    BinaryQuadraticLifetime.normalizeWithTrace,BinarySteinGCDMeasured.gcd_erases,
    BinaryDivisionStorageMeasured.traced_erases,BooleanFreshSeedMeasured.scan_erases]

theorem normalize_data (word : SignedWord) :
    (normalize word).1.1 = (BinaryQuadraticNormalization.normalizeWithWork word).1 := by
  rw [normalize_erases,BinaryQuadraticLifetime.normalizeWithTrace_erases,← BinaryQuadraticData.normalize_erasure]

theorem normalize_work (word : SignedWord) :
    (normalize word).2 = (BinaryQuadraticNormalization.normalizeWithWork word).2 := by
  simp only [normalize,normalizeMeasured,BinaryDivisionStorageMeasured.tracedMeasured_compat,
    BinaryQuadraticNormalization.normalizeWithWork,BinarySteinGCDMeasured.gcd_work,
    BinarySteinGCDMeasured.gcd_data,BinaryDivisionStorageMeasured.traced_work]

theorem normalizeMeasured_division_work_bound (word : SignedWord) :
    (normalizeMeasured word).2 ≤ 4*(normalize word).2 := by
  have hn := BinaryDivisionStorageMeasured.tracedMeasured_work_bound word.numerator
    (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1
  have hd := BinaryDivisionStorageMeasured.tracedMeasured_work_bound word.denominator
    (BinarySteinGCDMeasured.gcd word.numerator word.denominator).1.1
  simp only [BinaryDivisionStorageMeasured.traced] at hn hd
  simp only [normalize,normalizeMeasured]
  omega

def canonicalizeMeasured (word : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let normalized := normalizeMeasured word
  let numerator := BinaryCanonicalTrimMeasured.traced normalized.1.1.1.numerator
  let denominator := BinaryCanonicalTrimMeasured.traced normalized.1.1.1.denominator
  (((⟨normalized.1.1.1.negative,numerator.1.1,denominator.1.1⟩,
    [.frames 2,.arrayAllocation 16]++under 2 normalized.1.1.2++under 2 numerator.1.2++under 2 denominator.1.2),
    normalized.1.2+numerator.2+denominator.2),normalized.2)

def canonicalize (word : SignedWord) : (SignedWord × Trace) × ℕ := (canonicalizeMeasured word).1

theorem canonicalizeMeasured_compat (word : SignedWord) : (canonicalizeMeasured word).1 = canonicalize word := rfl

theorem canonicalize_erases (word : SignedWord) :
    (canonicalize word).1 = BinaryQuadraticLifetime.canonicalizeWithTrace word := by
  simp only [canonicalize,canonicalizeMeasured,normalizeMeasured_compat,
    BinaryQuadraticLifetime.canonicalizeWithTrace,normalize_erases,
    BinaryCanonicalTrimMeasured.traced_erases]

theorem canonicalize_data (word : SignedWord) :
    (canonicalize word).1.1 = (BinaryQuadraticNormalization.canonicalizeWithWork word).1 := by
  rw [canonicalize_erases,BinaryQuadraticLifetime.canonicalizeWithTrace_erases,
    ← BinaryQuadraticData.canonicalize_erasure]

theorem canonicalize_work (word : SignedWord) :
    (canonicalize word).2 = (BinaryQuadraticNormalization.canonicalizeWithWork word).2 := by
  simp only [canonicalize,canonicalizeMeasured,normalizeMeasured_compat,
    BinaryQuadraticNormalization.canonicalizeWithWork,normalize_data,
    normalize_work,BinaryCanonicalTrimMeasured.traced_work]

theorem canonicalizeMeasured_division_work_bound (word : SignedWord) :
    (canonicalizeMeasured word).2 ≤ 4*(canonicalize word).2 := by
  have h := normalizeMeasured_division_work_bound word
  simp only [normalize] at h
  simp only [canonicalize,canonicalizeMeasured]
  omega

def applyMeasured (op : RealArithmeticOp) (first second : SignedWord) : ((SignedWord × Trace) × ℕ) × ℕ :=
  let raw := BinaryRationalRawMeasured.traced op first second
  let canonical := canonicalizeMeasured raw.1.1
  (((canonical.1.1.1,[.frames 2,.arrayAllocation 16]++under 2 raw.1.2++under 2 canonical.1.1.2),
    raw.2+canonical.1.2),canonical.2)

def apply (op : RealArithmeticOp) (first second : SignedWord) : (SignedWord × Trace) × ℕ :=
  (applyMeasured op first second).1

theorem applyMeasured_compat (op : RealArithmeticOp) (first second : SignedWord) :
    (applyMeasured op first second).1 = apply op first second := rfl

theorem apply_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1 = BinaryQuadraticLifetime.applyWithTrace op first second := by
  simp only [apply,applyMeasured,canonicalizeMeasured_compat,
    BinaryQuadraticLifetime.applyWithTrace,BinaryRationalRawMeasured.traced_erases,canonicalize_erases]

theorem apply_data (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).1.1 = (BinaryQuadraticOpcode.applyWithWork op first second).1 := by
  rw [apply_erases,BinaryQuadraticLifetime.applyWithTrace_erases,← BinaryQuadraticData.apply_erasure]

theorem apply_work (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).2 = (BinaryQuadraticOpcode.applyWithWork op first second).2 := by
  simp only [apply,applyMeasured,canonicalizeMeasured_compat,
    BinaryQuadraticOpcode.applyWithWork,BinaryRationalRawMeasured.traced_data,
    BinaryRationalRawMeasured.traced_work,canonicalize_work]

theorem applyMeasured_division_work_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (applyMeasured op first second).2 ≤ 4*(apply op first second).2 := by
  have h := canonicalizeMeasured_division_work_bound
    (BinaryRationalRawMeasured.traced op first second).1.1
  simp only [canonicalize] at h
  simp only [apply,applyMeasured]
  omega

theorem apply_with_division_work_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).2+(applyMeasured op first second).2 ≤ 5*(apply op first second).2 := by
  have h := applyMeasured_division_work_bound op first second
  omega

theorem apply_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).2 ≤ 11000*(BinaryRationalArithmetic.pairWidth first second+1)^2 := by
  rw [apply_work]
  exact BinaryQuadraticOpcode.applyWithWork_bound op first second

theorem apply_contract (op : RealArithmeticOp) (first second : SignedWord)
    (hA : BinaryRationalOpcode.Valid first) (hB : BinaryRationalOpcode.Valid second) :
    value (apply op first second).1.1 = op.applyRat (value first) (value second) ∧
      BinaryRationalEncoding.CanonicalWord (apply op first second).1.1 ∧
      (apply op first second).2 ≤ 44000*RationalCostModel.schoolbook.rat
        (BinaryRationalArithmetic.pairWidth first second) := by
  rw [apply_data,apply_work]
  exact (BinaryQuadraticOpcode.applyWithWork_contract op first second hA hB).2

theorem apply_all_prefix (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first ≤ W) (hB : width second ≤ W) (borrowed steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+borrowed)
        (apply op first second).1.2 steps ≤
      BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+borrowed+
        BinaryQuadraticLifetime.opcodeBound W ∧
      framePeak ((apply op first second).1.2.take steps) ≤ BinaryQuadraticLifetime.opcodeFrames W := by
  rw [apply_erases]
  exact ⟨BinaryQuadraticLifetime.apply_all_prefix op first second W hA hB borrowed steps,
    BinaryQuadraticLifetime.apply_all_prefix_frames op first second W hA hB steps⟩

end Blotto.BinaryQuadraticMeasured
