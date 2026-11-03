import Blotto.BinaryQuadraticLifetime
import Blotto.BinarySegmentPoint
import Blotto.BinaryPRGHeapTraceUsage
import Blotto.BinaryPRGPreparationWork

/-! The four actual affine-coordinate opcodes replace a native three-slot
environment and repeated syntax compilation. Their returned data are handed
forward once. Exact bytes agree even before semantic validity assumptions. -/
namespace Blotto.BinaryPhysicalInterpolation
open BinaryRationalNormalization BinarySeedPreparationSpace BinaryPRGHeapTraceUsage
set_option maxHeartbeats 3000000

def coordinateWithTrace (first second scalar : SignedWord) : SignedWord × Trace :=
  let complement := BinaryQuadraticLifetime.applyWithTrace .sub BinaryPRGRecognition.one scalar
  let left := BinaryQuadraticLifetime.applyWithTrace .mul complement.1 first
  let right := BinaryQuadraticLifetime.applyWithTrace .mul scalar second
  let joined := BinaryQuadraticLifetime.applyWithTrace .add left.1 right.1
  (joined.1,wrap 64 2 [complement.2,left.2,right.2,joined.2])

def coordinateWithWork (first second scalar : SignedWord) : SignedWord × ℕ :=
  let complement := BinaryQuadraticOpcode.applyWithWork .sub BinaryPRGRecognition.one scalar
  let left := BinaryQuadraticOpcode.applyWithWork .mul complement.1 first
  let right := BinaryQuadraticOpcode.applyWithWork .mul scalar second
  let joined := BinaryQuadraticOpcode.applyWithWork .add left.1 right.1
  (joined.1,complement.2+left.2+right.2+joined.2+16)

theorem coordinate_state (first second scalar : SignedWord) :
    (coordinateWithTrace first second scalar).1 = BinaryQuadraticData.expression
      (BinarySegmentPoint.environment first second scalar) BinarySegmentPoint.program.compile := by
  simp [coordinateWithTrace,BinaryQuadraticLifetime.applyWithTrace_erases,BinaryQuadraticData.expression,
    BinarySegmentPoint.program,BinaryExpressionCompiler.Syntax.compile,BinarySegmentPoint.environment,
    FixedArrayTable.read_ofFn,BinaryPRGRecognition.one]

theorem coordinate_work_state (first second scalar : SignedWord) :
    (coordinateWithWork first second scalar).1 = (coordinateWithTrace first second scalar).1 := by
  simp only [coordinateWithWork,coordinateWithTrace,BinaryQuadraticData.apply_erasure,
    BinaryQuadraticLifetime.applyWithTrace_erases]

theorem apply_valid (op : RealArithmeticOp) (a b : SignedWord)
    (ha : BinaryRationalOpcode.Valid a) (hb : BinaryRationalOpcode.Valid b) :
    BinaryRationalOpcode.Valid (BinaryQuadraticData.apply op a b) := by
  rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state op a b ha hb]
  exact BinaryRationalOpcode.apply_valid op a b ha hb

theorem apply_width (op : RealArithmeticOp) (a b : SignedWord)
    (ha : BinaryRationalOpcode.Valid a) (hb : BinaryRationalOpcode.Valid b) :
    width (BinaryQuadraticData.apply op a b) ≤ 3*max (width a) (width b)+1 := by
  rw [← BinaryQuadraticData.apply_erasure,BinaryQuadraticOpcode.applyWithWork_state op a b ha hb]
  exact BinaryPRGPreparationWork.apply_stored_width op a b

theorem operand_widths (first second scalar : SignedWord)
    (hP : BinaryRationalOpcode.Valid first) (hQ : BinaryRationalOpcode.Valid second) (hT : BinaryRationalOpcode.Valid scalar)
    (W : ℕ) (hW : 1 ≤ W) (hp : width first ≤ W) (hq : width second ≤ W) (ht : width scalar ≤ W) :
    width (BinaryQuadraticData.apply .sub BinaryPRGRecognition.one scalar) ≤ 3*W+1 ∧
      width (BinaryQuadraticData.apply .mul (BinaryQuadraticData.apply .sub BinaryPRGRecognition.one scalar) first) ≤ 9*W+4 ∧
      width (BinaryQuadraticData.apply .mul scalar second) ≤ 3*W+1 := by
  have ho : width BinaryPRGRecognition.one = 1 := rfl
  have hu := apply_width .sub BinaryPRGRecognition.one scalar BinaryPRGRecognition.one_canonical.1 hT
  rw [ho] at hu
  have hum := max_le hW ht
  have hu' : width (BinaryQuadraticData.apply .sub BinaryPRGRecognition.one scalar) ≤ 3*W+1 := by omega
  have hx := apply_width .mul (BinaryQuadraticData.apply .sub BinaryPRGRecognition.one scalar) first
    (apply_valid .sub _ _ BinaryPRGRecognition.one_canonical.1 hT) hP
  have hym := max_le ht hq
  have hy := apply_width .mul scalar second hT hQ
  have hxm : max (width (BinaryQuadraticData.apply .sub BinaryPRGRecognition.one scalar)) (width first) ≤ 3*W+1 :=
    max_le hu' (by omega)
  exact ⟨hu',by omega,by omega⟩

def bound (W : ℕ) : ℕ := 4*(BinaryQuadraticLifetime.opcodeBound (9*W+4)+BinaryQuadraticLifetime.opcodeFrames (9*W+4))+128

theorem coordinate_usage (first second scalar : SignedWord)
    (hP : BinaryRationalOpcode.Valid first) (hQ : BinaryRationalOpcode.Valid second) (hT : BinaryRationalOpcode.Valid scalar)
    (W : ℕ) (hW : 1 ≤ W) (hp : width first ≤ W) (hq : width second ≤ W) (ht : width scalar ≤ W) :
    usage (coordinateWithTrace first second scalar).2 ≤ bound W := by
  have hh := operand_widths first second scalar hP hQ hT W hW hp hq ht
  let u := BinaryQuadraticLifetime.applyWithTrace .sub BinaryPRGRecognition.one scalar
  let x := BinaryQuadraticLifetime.applyWithTrace .mul u.1 first
  let y := BinaryQuadraticLifetime.applyWithTrace .mul scalar second
  have hu : width u.1 ≤ 3*W+1 := by simpa only [u,BinaryQuadraticLifetime.applyWithTrace_erases] using hh.1
  have hx : width x.1 ≤ 9*W+4 := by simpa only [x,u,BinaryQuadraticLifetime.applyWithTrace_erases] using hh.2.1
  have hy : width y.1 ≤ 3*W+1 := by simpa only [y,BinaryQuadraticLifetime.applyWithTrace_erases] using hh.2.2
  have huCost := BinaryQuadraticLifetime.applyWithTrace_bounds .sub BinaryPRGRecognition.one scalar (9*W+4)
    (show width BinaryPRGRecognition.one ≤ 9*W+4 by change 1 ≤ _; omega) (by omega)
  have hxCost := BinaryQuadraticLifetime.applyWithTrace_bounds .mul u.1 first (9*W+4) (by omega) (by omega)
  have hyCost := BinaryQuadraticLifetime.applyWithTrace_bounds .mul scalar second (9*W+4) (by omega) (by omega)
  have hzCost := BinaryQuadraticLifetime.applyWithTrace_bounds .add x.1 y.1 (9*W+4) hx (by omega)
  have hw := wrap_usage 64 2 [u.2,x.2,y.2,(BinaryQuadraticLifetime.applyWithTrace .add x.1 y.1).2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (coordinateWithTrace first second scalar).2 ≤ _ at hw
  change _ ≤ bound W
  unfold bound usage BinaryPRGHeapPrimitiveLifetime.cells at *
  change listCells u.2+arraySlots u.2 ≤ _ ∧ framePeak u.2 ≤ _ at huCost
  change listCells x.2+arraySlots x.2 ≤ _ ∧ framePeak x.2 ≤ _ at hxCost
  change listCells y.2+arraySlots y.2 ≤ _ ∧ framePeak y.2 ≤ _ at hyCost
  omega

theorem coordinate_work (first second scalar : SignedWord)
    (hP : BinaryRationalOpcode.Valid first) (hQ : BinaryRationalOpcode.Valid second) (hT : BinaryRationalOpcode.Valid scalar)
    (W : ℕ) (hW : 1 ≤ W) (hp : width first ≤ W) (hq : width second ≤ W) (ht : width scalar ≤ W) :
    (coordinateWithWork first second scalar).2 ≤ 44000*(9*W+5)^2+16 := by
  have hh := operand_widths first second scalar hP hQ hT W hW hp hq ht
  let u := BinaryQuadraticOpcode.applyWithWork .sub BinaryPRGRecognition.one scalar
  let x := BinaryQuadraticOpcode.applyWithWork .mul u.1 first
  let y := BinaryQuadraticOpcode.applyWithWork .mul scalar second
  have hu : width u.1 ≤ 3*W+1 := by simpa only [u,BinaryQuadraticData.apply_erasure] using hh.1
  have hx : width x.1 ≤ 9*W+4 := by simpa only [x,u,BinaryQuadraticData.apply_erasure] using hh.2.1
  have hy : width y.1 ≤ 3*W+1 := by simpa only [y,BinaryQuadraticData.apply_erasure] using hh.2.2
  have primitive : ∀ op a b,width a ≤ 9*W+4 → width b ≤ 9*W+4 →
      (BinaryQuadraticOpcode.applyWithWork op a b).2 ≤ 11000*(9*W+5)^2 := by
    intro op a b ha hb
    exact (BinaryQuadraticOpcode.applyWithWork_bound op a b).trans
      (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left (Nat.add_le_add_right (max_le ha hb) 1) 2))
  have hU := primitive .sub BinaryPRGRecognition.one scalar (by change 1 ≤ _; omega) (by omega)
  have hX := primitive .mul u.1 first (by omega) (by omega)
  have hY := primitive .mul scalar second (by omega) (by omega)
  have hZ := primitive .add x.1 y.1 hx (by omega)
  change u.2+x.2+y.2+(BinaryQuadraticOpcode.applyWithWork .add x.1 y.1).2+16 ≤ _
  change u.2 ≤ _ at hU
  change x.2 ≤ _ at hX
  change y.2 ≤ _ at hY
  omega

end Blotto.BinaryPhysicalInterpolation
