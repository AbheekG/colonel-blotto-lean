import Blotto.BinarySteinGCDLifetime
import Blotto.BinaryQuadraticData

/-! Allocation/lifetime realization of the actual quadratic Boolean backend.
The traced Stein-GCD output is consumed by both restoring divisions; reached
sign scan and both trims produce the normalized/canonical word. Opcodes use
only the unchanged raw Boolean arithmetic allocation producer before this
new normalization. Exact data-only erasure holds for all input bytes, and
valid operands preserve every old canonical result. All reservations stay
retained; original input words and other borrowed state are explicit.
The all-retained heap bound is cubic. It is separate from quadratic primitive
work, reclaimed space and host compiler/allocator behavior. -/
set_option autoImplicit false
namespace Blotto.BinaryQuadraticLifetime
open BinarySeedPreparationSpace BinaryRationalNormalization BinaryRationalEncoding
open BinaryBooleanPrimitiveLifetime

def normalizeWithTrace (word : SignedWord) : SignedWord×Trace :=
  let common := BinarySteinGCDLifetime.gcdWithTrace word.numerator word.denominator
  let numerator := divideWithTrace word.numerator common.1
  let denominator := divideWithTrace word.denominator common.1
  let sign := scanWithTrace numerator.1.1
  (⟨word.negative && sign.1,numerator.1.1,denominator.1.1⟩,[.frames 2,.arrayAllocation 16] ++
    under 2 common.2 ++ under 2 numerator.2 ++ under 2 denominator.2 ++ under 2 sign.2)

@[simp] theorem normalizeWithTrace_erases (word : SignedWord) :
    (normalizeWithTrace word).1=BinaryQuadraticData.normalize word := by
  simp only [normalizeWithTrace,BinaryQuadraticData.normalize,BinarySteinGCDLifetime.gcdWithTrace_erases,
    divideWithTrace_erases,scanWithTrace_erases]

theorem normalizeWithTrace_lengths (word : SignedWord) :
    (normalizeWithTrace word).1.numerator.length=word.numerator.length ∧
    (normalizeWithTrace word).1.denominator.length=word.denominator.length := by
  rw [normalizeWithTrace_erases,← BinaryQuadraticData.normalize_erasure]
  exact BinaryQuadraticNormalization.normalize_lengths word

theorem normalizeWithTrace_bounds (word : SignedWord) :
    listCells (normalizeWithTrace word).2+arraySlots (normalizeWithTrace word).2≤2000*(width word+2)^3 ∧
    framePeak (normalizeWithTrace word).2≤6*width word+26 := by
  let common := (BinarySteinGCDLifetime.gcdWithTrace word.numerator word.denominator).1
  have hGcd := BinarySteinGCDLifetime.gcdWithTrace_bounds word.numerator word.denominator
  change _≤500*(width word+2)^3 ∧ _≤6*width word+24 at hGcd
  have hCommon : common.length≤width word := by
    dsimp only [common]; rw [BinarySteinGCDLifetime.gcdWithTrace_erases]
    exact BinarySteinGCD.canonicalGcd_length word.numerator word.denominator
  have hA : word.numerator.length≤width word := Nat.le_max_left _ _
  have hB : word.denominator.length≤width word := Nat.le_max_right _ _
  have hNum := divideWithTrace_bounds word.numerator common (width word) hA hCommon
  have hDen := divideWithTrace_bounds word.denominator common (width word) hB hCommon
  have hNumLength : (divideWithTrace word.numerator common).1.1.length=word.numerator.length := by
    rw [divideWithTrace_erases]; exact (BinaryLongDivision.divide_lengths _ _).1
  have hSign := scanWithTrace_bounds (divideWithTrace word.numerator common).1.1
  rw [hNumLength] at hSign
  have hg := framePeak_under 2 (BinarySteinGCDLifetime.gcdWithTrace word.numerator word.denominator).2
  have hn := framePeak_under 2 (divideWithTrace word.numerator common).2
  have hd := framePeak_under 2 (divideWithTrace word.denominator common).2
  have hs := framePeak_under 2 (scanWithTrace (divideWithTrace word.numerator common).1.1).2
  have hp : width word+2≤(width word+2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<width word+2) (by decide : 1≤3)
  unfold normalizeWithTrace
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  dsimp only [common] at hNum hDen hSign hn hd hs
  exact ⟨by nlinarith only [hGcd.1,hNum.1,hDen.1,hSign.1,hA,hp],by omega⟩

def canonicalizeWithTrace (word : SignedWord) : SignedWord×Trace :=
  let normalized := normalizeWithTrace word
  let numerator := trimWithTrace normalized.1.numerator
  let denominator := trimWithTrace normalized.1.denominator
  (⟨normalized.1.negative,numerator.1,denominator.1⟩,[.frames 2,.arrayAllocation 16] ++
    under 2 normalized.2 ++ under 2 numerator.2 ++ under 2 denominator.2)

@[simp] theorem canonicalizeWithTrace_erases (word : SignedWord) :
    (canonicalizeWithTrace word).1=BinaryQuadraticData.canonicalize word := by
  simp only [canonicalizeWithTrace,normalizeWithTrace_erases,trimWithTrace_erases]
  rfl

theorem canonicalizeWithTrace_state (word : SignedWord) (hValid : BinaryRationalOpcode.Valid word) :
    (canonicalizeWithTrace word).1=BinaryRationalOpcode.canonicalize word := by
  rw [canonicalizeWithTrace_erases,← BinaryQuadraticData.canonicalize_erasure]
  exact BinaryQuadraticNormalization.canonicalizeWithWork_state word hValid

theorem canonicalizeWithTrace_bounds (word : SignedWord) :
    listCells (canonicalizeWithTrace word).2+arraySlots (canonicalizeWithTrace word).2≤3000*(width word+2)^3 ∧
    framePeak (canonicalizeWithTrace word).2≤6*width word+28 := by
  have hNorm := normalizeWithTrace_bounds word
  have hLengths := normalizeWithTrace_lengths word
  have hNum := trimWithTrace_bounds (normalizeWithTrace word).1.numerator
  have hDen := trimWithTrace_bounds (normalizeWithTrace word).1.denominator
  rw [hLengths.1] at hNum
  rw [hLengths.2] at hDen
  have hn := framePeak_under 2 (normalizeWithTrace word).2
  have hnf := framePeak_under 2 (trimWithTrace (normalizeWithTrace word).1.numerator).2
  have hdf := framePeak_under 2 (trimWithTrace (normalizeWithTrace word).1.denominator).2
  have hA : word.numerator.length≤width word := Nat.le_max_left _ _
  have hB : word.denominator.length≤width word := Nat.le_max_right _ _
  have hp : width word+2≤(width word+2)^3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0<width word+2) (by decide : 1≤3)
  unfold canonicalizeWithTrace
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under]
  exact ⟨by nlinarith only [hNorm.1,hNum.1,hDen.1,hA,hB,hp],by omega⟩

-- This is the raw producer shared by both backends, before any normalizer.
-- Its structural allocation observer includes source activations. Reserving
-- that allowance as frames overcounts nested scratch and Boolean list cells.
def rawWithTrace (op : RealArithmeticOp) (first second : SignedWord) : SignedWord×Trace :=
  let result := BinaryRationalOpcodeAllocation.rawApplyWithAllocation op first second
  (result.1,[.frames (result.2+8),.arrayAllocation 16,
    .listAllocation (BinaryRationalOpcodeAllocation.rawStorage op first second)])

@[simp] theorem rawWithTrace_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (rawWithTrace op first second).1=BinaryRationalOpcode.rawApply op first second :=
  BinaryRationalOpcodeAllocation.rawApplyWithAllocation_state op first second

theorem rawWithTrace_bounds (op : RealArithmeticOp) (first second : SignedWord) :
    listCells (rawWithTrace op first second).2+arraySlots (rawWithTrace op first second).2≤
      3000*(BinaryRationalArithmetic.pairWidth first second+1)^3+16 ∧
    framePeak (rawWithTrace op first second).2≤200*(BinaryRationalArithmetic.pairWidth first second+1)^2+8 := by
  have hSpace := BinaryRationalOpcodeAllocation.rawStorage_bound op first second
  have hFrames := BinaryRationalOpcodeAllocation.rawApplyWithAllocation_bound op first second
  simp only [rawWithTrace,listCells,arraySlots,framePeak]
  exact ⟨by omega,by omega⟩

def applyWithTrace (op : RealArithmeticOp) (first second : SignedWord) : SignedWord×Trace :=
  let raw := rawWithTrace op first second
  let canonical := canonicalizeWithTrace raw.1
  (canonical.1,[.frames 2,.arrayAllocation 16] ++ under 2 raw.2 ++ under 2 canonical.2)

@[simp] theorem applyWithTrace_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithTrace op first second).1=BinaryQuadraticData.apply op first second := by
  simp only [applyWithTrace,canonicalizeWithTrace_erases,rawWithTrace_erases,BinaryQuadraticData.apply]

theorem applyWithTrace_state (op : RealArithmeticOp) (first second : SignedWord)
    (hA : BinaryRationalOpcode.Valid first) (hB : BinaryRationalOpcode.Valid second) :
    (applyWithTrace op first second).1=BinaryRationalOpcode.apply op first second := by
  rw [applyWithTrace_erases,← BinaryQuadraticData.apply_erasure]
  exact BinaryQuadraticOpcode.applyWithWork_state op first second hA hB

def opcodeBound (W : ℕ) : ℕ := 200000*(W+2)^3
def opcodeFrames (W : ℕ) : ℕ := 500*(W+2)^2

theorem applyWithTrace_bounds (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first≤W) (hB : width second≤W) :
    listCells (applyWithTrace op first second).2+arraySlots (applyWithTrace op first second).2≤opcodeBound W ∧
    framePeak (applyWithTrace op first second).2≤opcodeFrames W := by
  have hRaw := rawWithTrace_bounds op first second
  have hCanonical := canonicalizeWithTrace_bounds (BinaryRationalOpcode.rawApply op first second)
  have hRawWidth := BinaryRationalOpcode.rawApply_width op first second
  have hw : BinaryRationalArithmetic.pairWidth first second≤W := max_le hA hB
  have hTop : width (BinaryRationalOpcode.rawApply op first second)+2≤4*(W+2) := by omega
  have hPower := Nat.pow_le_pow_left hTop 3
  have hC := hCanonical.1.trans (Nat.mul_le_mul_left 3000 hPower)
  have hR := hRaw.1.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 3000 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 3)) 16)
  have hRF := hRaw.2.trans (Nat.add_le_add_right
    (Nat.mul_le_mul_left 200 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2)) 8)
  have hf := framePeak_under 2 (rawWithTrace op first second).2
  have hc := framePeak_under 2 (canonicalizeWithTrace (rawWithTrace op first second).1).2
  rw [rawWithTrace_erases] at hc
  have hOne : 1≤(W+2)^3 := Nat.one_le_pow 3 _ (by omega)
  have hCube : (W+1)^3≤(W+2)^3 := Nat.pow_le_pow_left (by omega) 3
  have hLinear : W+2≤(W+2)^2 := by nlinarith
  have hSquare : (W+1)^2≤(W+2)^2 := Nat.pow_le_pow_left (by omega) 2
  have hSquareOne : 1≤(W+2)^2 := Nat.one_le_pow 2 _ (by omega)
  have hRawFrames : framePeak (under 2 (rawWithTrace op first second).2)≤500*(W+2)^2 := by
    nlinarith only [hRF,hf,hSquare,hSquareOne]
  have hCanonicalFrames : framePeak (under 2 (canonicalizeWithTrace (BinaryRationalOpcode.rawApply op first second)).2)≤500*(W+2)^2 := by
    nlinarith only [hCanonical.2,hRawWidth,hw,hLinear,hc]
  have hBaseFrames : 2≤500*(W+2)^2 := by nlinarith
  unfold applyWithTrace opcodeBound opcodeFrames
  simp only [listCells_append,arraySlots_append,framePeak_append,listCells,arraySlots,framePeak,listCells_under,arraySlots_under,
    rawWithTrace_erases]
  exact ⟨by nlinarith only [hR,hC,hOne,hCube],by omega⟩

theorem apply_all_prefix (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first≤W) (hB : width second≤W) (borrowedOtherCells steps : ℕ) :
    retainedHeap (BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+borrowedOtherCells)
      (applyWithTrace op first second).2 steps≤
      BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+borrowedOtherCells+opcodeBound W :=
  prefix_heap _ _ _ _ (applyWithTrace_bounds op first second W hA hB).1

theorem apply_all_prefix_frames (op : RealArithmeticOp) (first second : SignedWord) (W : ℕ)
    (hA : width first≤W) (hB : width second≤W) (steps : ℕ) :
    framePeak ((applyWithTrace op first second).2.take steps)≤opcodeFrames W :=
  (framePeak_take_le _ _).trans (applyWithTrace_bounds op first second W hA hB).2

end Blotto.BinaryQuadraticLifetime
