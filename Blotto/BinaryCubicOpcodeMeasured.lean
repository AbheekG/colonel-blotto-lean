import Blotto.BinaryEuclideanStorageMeasured
import Blotto.BinaryCanonicalTrimMeasured
import Blotto.BinaryRationalRawStorageMeasured
import Blotto.BinaryPrimitiveTracePlan

/-! The cubic opcode now shares actual raw arithmetic, Euclidean normalization
and canonical trimming between data/allocation/storage/source/work fields.
No old opcode/allocation/storage/work producer is replayed for instrumentation.
The old cubic interface remains exact, including invalid Boolean inputs. Native
observer arithmetic and physical ownership/allocator/GC costs are separate. -/
namespace Blotto.BinaryCubicOpcodeMeasured
open BinaryRationalNormalization
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Result where
  data : SignedWord
  allocated : ℕ
  storage : ℕ
  source : ℕ
  work : ℕ

def canonicalize (word : SignedWord) : Result :=
  let normalized := BinaryEuclideanStorageMeasured.normalize word
  let numerator := BinaryPrimitiveTracePlan.trimStored normalized.data.numerator
  let denominator := BinaryPrimitiveTracePlan.trimStored normalized.data.denominator
  let output : SignedWord := ⟨normalized.data.negative,numerator.1.1.1,denominator.1.1.1⟩
  ⟨output,normalized.allocated+numerator.1.1.2+denominator.1.1.2+3,
    BinaryRationalOpcodeAllocation.payload word+BinaryRationalOpcodeAllocation.payload normalized.data+
      BinaryRationalOpcodeAllocation.payload output+4+normalized.storage+numerator.2+denominator.2,
    normalized.source+numerator.1.2+denominator.1.2+2,
    normalized.work+numerator.1.2+denominator.1.2+2⟩

theorem canonicalize_previous_record (word : SignedWord) :
    canonicalize word = (
      let normalized := BinaryEuclideanStorageMeasured.normalize word
      let numerator := BinaryCanonicalTrimMeasured.stored normalized.data.numerator
      let denominator := BinaryCanonicalTrimMeasured.stored normalized.data.denominator
      let output : SignedWord := ⟨normalized.data.negative,numerator.1.1.1,denominator.1.1.1⟩
      ⟨output,normalized.allocated+numerator.1.1.2+denominator.1.1.2+3,
        BinaryRationalOpcodeAllocation.payload word+BinaryRationalOpcodeAllocation.payload normalized.data+
          BinaryRationalOpcodeAllocation.payload output+4+normalized.storage+numerator.2+denominator.2,
        normalized.source+numerator.1.2+denominator.1.2+2,
        normalized.work+numerator.1.2+denominator.1.2+2⟩) := by
  simp only [canonicalize,BinaryPrimitiveTracePlan.trimStored_exact]

theorem canonicalize_erases (word : SignedWord) :
    ((canonicalize word).data,(canonicalize word).allocated) =
      BinaryRationalOpcodeAllocation.canonicalizeWithAllocation word := by
  simp only [canonicalize,BinaryRationalOpcodeAllocation.canonicalizeWithAllocation,
    ← BinaryEuclideanStorageMeasured.normalize_erases,BinaryPrimitiveTracePlan.trimStored_exact,BinaryCanonicalTrimMeasured.stored_erases,
    BinaryCanonicalTrimMeasured.trim_erases]

theorem canonicalize_data (word : SignedWord) :
    (canonicalize word).data = BinaryRationalOpcode.canonicalize word :=
  (congrArg Prod.fst (canonicalize_erases word)).trans
    (BinaryRationalOpcodeAllocation.canonicalizeWithAllocation_state word)

theorem canonicalize_allocated (word : SignedWord) :
    (canonicalize word).allocated = (BinaryRationalOpcodeAllocation.canonicalizeWithAllocation word).2 :=
  congrArg Prod.snd (canonicalize_erases word)

theorem canonicalize_storage (word : SignedWord) :
    (canonicalize word).storage = BinaryRationalOpcodeAllocation.canonicalizeStorage word := by
  unfold canonicalize
  dsimp only
  rw [show (⟨(BinaryEuclideanStorageMeasured.normalize word).data.negative,
      (BinaryPrimitiveTracePlan.trimStored (BinaryEuclideanStorageMeasured.normalize word).data.numerator).1.1.1,
      (BinaryPrimitiveTracePlan.trimStored (BinaryEuclideanStorageMeasured.normalize word).data.denominator).1.1.1⟩ : SignedWord) =
      BinaryRationalOpcode.canonicalize word from canonicalize_data word]
  simp only [BinaryRationalOpcodeAllocation.canonicalizeStorage,
    BinaryEuclideanStorageMeasured.normalize_storage,BinaryEuclideanStorageMeasured.normalize_data,
    BinaryPrimitiveTracePlan.trimStored_exact,BinaryCanonicalTrimMeasured.stored_storage]

theorem canonicalize_source (word : SignedWord) :
    (canonicalize word).source = (BinaryRationalOpcode.canonicalizeWithWork word).2 := by
  simp only [canonicalize,BinaryRationalOpcode.canonicalizeWithWork,
    BinaryEuclideanStorageMeasured.normalize_source,BinaryEuclideanStorageMeasured.normalize_data,
    BinaryPrimitiveTracePlan.trimStored_exact,BinaryCanonicalTrimMeasured.stored_erases,BinaryCanonicalTrimMeasured.trim_work]
  rfl

theorem canonicalize_work_bound (word : SignedWord) :
    (canonicalize word).work ≤ 4*(canonicalize word).source := by
  have h := BinaryEuclideanStorageMeasured.normalize_work_bound word
  simp only [canonicalize]
  omega

theorem canonicalize_storage_bound (word : SignedWord) :
    (canonicalize word).storage ≤ 5000*(width word+2)^4 := by
  rw [canonicalize_storage]
  exact BinaryRationalOpcodeAllocation.canonicalizeStorage_bound word

def apply (op : RealArithmeticOp) (first second : SignedWord) : Result :=
  let raw := BinaryRationalRawStorageMeasured.apply op first second
  let canonical := canonicalize raw.data
  ⟨canonical.data,raw.allocated+canonical.allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      BinaryRationalOpcodeAllocation.payload raw.data+BinaryRationalOpcodeAllocation.payload canonical.data+
      5+raw.storage+canonical.storage,
    raw.work+canonical.source,raw.work+canonical.work⟩

theorem apply_erases (op : RealArithmeticOp) (first second : SignedWord) :
    ((apply op first second).data,(apply op first second).allocated) =
      BinaryRationalOpcodeAllocation.applyWithAllocation op first second := by
  simp only [apply,BinaryRationalOpcodeAllocation.applyWithAllocation,
    ← BinaryRationalRawStorageMeasured.apply_erases,← canonicalize_erases]

theorem apply_data (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).data = BinaryRationalOpcode.apply op first second :=
  (congrArg Prod.fst (apply_erases op first second)).trans
    (BinaryRationalOpcodeAllocation.applyWithAllocation_state op first second)

theorem apply_allocated (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).allocated = (BinaryRationalOpcodeAllocation.applyWithAllocation op first second).2 :=
  congrArg Prod.snd (apply_erases op first second)

theorem apply_storage (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).storage = BinaryRationalOpcodeAllocation.opcodeStorage op first second := by
  simp only [apply,BinaryRationalOpcodeAllocation.opcodeStorage,
    BinaryRationalRawStorageMeasured.apply_storage,BinaryRationalRawStorageMeasured.apply_data,
    canonicalize_storage,canonicalize_data,BinaryRationalOpcode.apply]

theorem apply_source (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).source = (BinaryRationalOpcode.applyWithWork op first second).2 := by
  simp only [apply,BinaryRationalOpcode.applyWithWork,BinaryRationalRawStorageMeasured.apply_data,
    BinaryRationalRawStorageMeasured.apply_work,canonicalize_source]

theorem apply_work_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).work ≤ 4*(apply op first second).source := by
  have h := canonicalize_work_bound (BinaryRationalRawStorageMeasured.apply op first second).data
  simp only [apply]
  omega

theorem apply_work_cubic (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).work ≤ 48000*(BinaryRationalArithmetic.pairWidth first second+1)^3 := by
  have h := apply_work_bound op first second
  rw [apply_source] at h
  have hs := BinaryRationalOpcode.applyWithWork_bound op first second
  omega

theorem apply_storage_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).storage ≤ 2000000*(BinaryRationalArithmetic.pairWidth first second+2)^4 := by
  rw [apply_storage]
  exact BinaryRationalOpcodeAllocation.opcodeStorage_bound op first second

end Blotto.BinaryCubicOpcodeMeasured
