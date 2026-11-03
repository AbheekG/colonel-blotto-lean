import Blotto.BinaryCompareSignedMeasured
import Blotto.BinaryQuadraticResourceStateLifetime

/-! One rational comparison returns the actual cross-product/sign/scan result
with the exact preceding allocation, retained storage and work reservations.
Its traced wrapper consumes those returned observers; it does not rerun the
old lessEqualStorage/lessEqualWork programs. Native observer arithmetic and
reference/allocator/GC realisation remain outside this source contract. -/
namespace Blotto.BinaryRationalComparisonMeasured
open BinaryRationalNormalization BinaryRationalArithmetic BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 2500000

structure Result where
  data : Bool
  allocated : ℕ
  storage : ℕ
  work : ℕ

def compareProduced (first second : SignedWord) : Result × (ℕ × ℕ) :=
  let leftProduced := BinaryCompareSignedMeasured.multiplyProduced (numeratorWord first) (denominatorWord second)
  let left := leftProduced.1.1
  let rightProduced := BinaryCompareSignedMeasured.multiplyProduced (numeratorWord second) (denominatorWord first)
  let right := rightProduced.1.1
  let differenceProduced := BinaryCompareSignedMeasured.subtractProduced left.data right.data
  let difference := differenceProduced.1.1
  let scanned := BinaryNormalizationAllocation.scanWithFrames difference.data.bits
  let allocated := left.allocated+right.allocated+difference.allocated+scanned.2+5
  (⟨difference.data.negative || !scanned.1,allocated,
    (1+leftProduced.2.1+rightProduced.2.2)+(1+rightProduced.2.1+leftProduced.2.2)+
      leftProduced.1.2+rightProduced.1.2+differenceProduced.1.2+8+
      left.storage+right.storage+difference.storage+scanned.2+allocated,
    left.work+right.work+difference.work+3*(differenceProduced.1.2+1)+5⟩,
    (1+leftProduced.2.1+rightProduced.2.2,1+rightProduced.2.1+leftProduced.2.2))

theorem compareProduced_payloads (first second : SignedWord) :
    (compareProduced first second).2 =
      (BinaryRationalOpcodeAllocation.payload first,BinaryRationalOpcodeAllocation.payload second) := by
  simp only [compareProduced,BinaryCompareSignedMeasured.multiplyProduced_lengths,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]

def compare (first second : SignedWord) : Result := (compareProduced first second).1

attribute [irreducible] compareProduced

theorem compareProduced_public (first second : SignedWord) :
    (compareProduced first second).1 = compare first second := rfl

theorem compare_previous_record (first second : SignedWord) :
    compare first second = (
  let left := BinaryCompareSignedMeasured.multiply (numeratorWord first) (denominatorWord second)
  let right := BinaryCompareSignedMeasured.multiply (numeratorWord second) (denominatorWord first)
  let difference := BinaryCompareSignedMeasured.subtract left.data right.data
  let scanned := BinaryNormalizationAllocation.scanWithFrames difference.data.bits
  let allocated := left.allocated+right.allocated+difference.allocated+scanned.2+5
  ⟨difference.data.negative || !scanned.1,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      left.data.bits.length+right.data.bits.length+difference.data.bits.length+8+
      left.storage+right.storage+difference.storage+scanned.2+allocated,
    left.work+right.work+difference.work+3*(difference.data.bits.length+1)+5⟩) := by
  simp only [compare,compareProduced,
    BinaryCompareSignedMeasured.multiplyProduced_lengths,BinaryCompareSignedMeasured.multiplyProduced_width,
    BinaryCompareSignedMeasured.multiplyProduced_public,BinaryCompareSignedMeasured.addProduced_width,
    BinaryCompareSignedMeasured.addProduced_public,BinaryCompareSignedMeasured.subtractProduced_width,
    BinaryCompareSignedMeasured.subtractProduced_public,BinaryAddMultiplyMetadata.multiplyProduced_lengths,
    BinaryAddMultiplyMetadata.multiplyProduced_width,BinaryAddMultiplyMetadata.multiply,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]

theorem compare_erases (first second : SignedWord) :
    ((compare first second).data,(compare first second).allocated) =
      BinaryRationalOpcodeAllocation.lessEqualWithAllocation first second := by
  simp only [compare_previous_record,BinaryRationalOpcodeAllocation.lessEqualWithAllocation,
    ← BinaryCompareSignedMeasured.multiply_erases,← BinaryCompareSignedMeasured.subtract_erases]

theorem compare_data (first second : SignedWord) :
    (compare first second).data = BinaryRationalArithmetic.lessEqual first second := by
  exact (congrArg Prod.fst (compare_erases first second)).trans
    (BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state first second)

theorem compare_allocated (first second : SignedWord) :
    (compare first second).allocated = (BinaryRationalOpcodeAllocation.lessEqualWithAllocation first second).2 :=
  congrArg Prod.snd (compare_erases first second)

theorem compare_storage (first second : SignedWord) :
    (compare first second).storage = BinaryRationalOpcodeAllocation.lessEqualStorage first second := by
  have hAlloc := compare_allocated first second
  simp only [compare_previous_record] at hAlloc ⊢
  rw [hAlloc]
  simp only [BinaryRationalOpcodeAllocation.lessEqualStorage,
    BinaryCompareSignedMeasured.multiply_storage,BinaryCompareSignedMeasured.multiply_data,
    BinaryCompareSignedMeasured.subtract_storage,BinaryCompareSignedMeasured.subtract_data]

theorem compare_work (first second : SignedWord) :
    (compare first second).work = BinaryRationalArithmetic.lessEqualWork first second := by
  simp only [compare_previous_record,BinaryRationalArithmetic.lessEqualWork,
    BinaryCompareSignedMeasured.multiply_work,BinaryCompareSignedMeasured.multiply_data,
    BinaryCompareSignedMeasured.subtract_work,BinaryCompareSignedMeasured.subtract_data]

def traced (first second : SignedWord) : (Bool × Trace) × ℕ :=
  let result := compare first second
  ((result.data,[.frames (200*(pairWidth first second+1)^2+8),
    .arrayAllocation 16,.listAllocation result.storage]),result.work)

theorem traced_erases (first second : SignedWord) :
    (traced first second).1 = BinaryQuadraticResourceStateLifetime.compareWithTrace first second := by
  simp only [traced,BinaryQuadraticResourceStateLifetime.compareWithTrace,
    compare_storage,compare_data,BinaryRationalOpcodeAllocation.lessEqualWithAllocation_state]

theorem traced_work (first second : SignedWord) :
    (traced first second).2 = BinaryRationalArithmetic.lessEqualWork first second := compare_work _ _

theorem traced_bound (first second : SignedWord) :
    (traced first second).2 ≤ 500*(pairWidth first second+1)^2 := by
  rw [traced_work]
  exact lessEqualWork_bound first second


end Blotto.BinaryRationalComparisonMeasured
