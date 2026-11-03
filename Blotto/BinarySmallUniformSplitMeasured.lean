import Blotto.BinaryNormalizedCoordinate
import Blotto.BinaryLifetimeArrayExtras
import Blotto.BinaryPlannedQuadratic
import Blotto.BinaryFourGuardMeasured
import Blotto.BinaryThreeReferenceMeasured
import Blotto.BinarySmallUniformSplitLifetime

/-! Five actual measured opcodes produce the proportional endpoint pair.
Their returned words feed measured four-word reference packing once. The
zero-total division follows the existing opcode. Native reference-bit,
observer and allocator realization remain separate from source charges. -/
namespace Blotto.BinarySmallUniformSplitMeasured
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryFactoryHeight
set_option autoImplicit false
attribute [local irreducible] BinaryPlannedQuadratic.apply BinaryPlannedQuadratic.applyMeasured
set_option maxHeartbeats 500000

def opcodePrice (s : ℕ) : ℕ := 11000*(2*s+2)^2

theorem opcode_work (op : RealArithmeticOp) (a b : SignedWord)
    (hA : CanonicalWord a) (hB : CanonicalWord b) (s : ℕ)
    (ha : RationalHeight (value a) s) (hb : RationalHeight (value b) s) :
    (BinaryQuadraticMeasured.apply op a b).2 ≤ opcodePrice s := by
  have hWA : width a ≤ 2*s+1 := by have h := hA.2.trans (rationalWordWidth_of_height ha); omega
  have hWB : width b ≤ 2*s+1 := by have h := hB.2.trans (rationalWordWidth_of_height hb); omega
  exact BinaryFourGuardMeasured.opcode_work op a b (2*s+1) hWA hWB

theorem apply_state (op : RealArithmeticOp) (a b : SignedWord)
    (ha : BinaryRationalOpcode.Valid a) (hb : BinaryRationalOpcode.Valid b) :
    (BinaryQuadraticMeasured.apply op a b).1.1 = BinaryRationalOpcode.apply op a b := by
  rw [BinaryQuadraticMeasured.apply_erases]
  exact BinaryQuadraticLifetime.applyWithTrace_state op a b ha hb

def joinArithmetic (total low high left right : (SignedWord × Trace) × ℕ) : ((SignedWord × SignedWord) × Trace) × ℕ :=
  (((left.1.1,right.1.1),wrap 32 6 [total.1.2,low.1.2,high.1.2,left.1.2,right.1.2]),
    total.2+low.2+high.2+left.2+right.2+16)

set_option cleanup.letToHave false in
def arithmeticWithExtras (first second coordinate : SignedWord) : (((SignedWord × SignedWord) × Trace) × ℕ) × ℕ :=
  let total := BinaryNormalizedCoordinate.opcode .add first second
  let low := BinaryNormalizedCoordinate.opcode .div first total.1.1.1
  let high := BinaryNormalizedCoordinate.opcode .div second total.1.1.1
  let left := BinaryNormalizedCoordinate.opcode .mul low.1.1.1 coordinate
  let right := BinaryNormalizedCoordinate.opcode .mul high.1.1.1 coordinate
  (joinArithmetic total.1 low.1 high.1 left.1 right.1,total.2+low.2+high.2+left.2+right.2)

def arithmetic (first second coordinate : SignedWord) : ((SignedWord × SignedWord) × Trace) × ℕ :=
  (arithmeticWithExtras first second coordinate).1

theorem arithmeticWithExtras_compat (first second coordinate : SignedWord) :
    (arithmeticWithExtras first second coordinate).1 = arithmetic first second coordinate := rfl

theorem arithmetic_record (first second coordinate : SignedWord) :
    arithmetic first second coordinate =
  let total := BinaryPlannedQuadratic.apply .add first second
  let low := BinaryPlannedQuadratic.apply .div first total.1.1
  let high := BinaryPlannedQuadratic.apply .div second total.1.1
  let left := BinaryPlannedQuadratic.apply .mul low.1.1 coordinate
  let right := BinaryPlannedQuadratic.apply .mul high.1.1 coordinate
  joinArithmetic total low high left right := by
  simp only [arithmetic,arithmeticWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record]

theorem arithmetic_eq (first second coordinate : SignedWord) : arithmetic first second coordinate =
    let total := BinaryQuadraticMeasured.apply .add first second
    let low := BinaryQuadraticMeasured.apply .div first total.1.1
    let high := BinaryQuadraticMeasured.apply .div second total.1.1
    joinArithmetic total low high (BinaryQuadraticMeasured.apply .mul low.1.1 coordinate)
      (BinaryQuadraticMeasured.apply .mul high.1.1 coordinate) := by
  simp only [arithmetic_record,BinaryPlannedQuadratic.apply_previous]

theorem joinArithmetic_work (total low high left right : (SignedWord × Trace) × ℕ) (W : ℕ)
    (ht : total.2 ≤ W) (hl : low.2 ≤ W) (hh : high.2 ≤ W) (hp : left.2 ≤ W) (hq : right.2 ≤ W) :
    (joinArithmetic total low high left right).2 ≤ 5*W+16 := by
  change total.2+low.2+high.2+left.2+right.2+16 ≤ _
  omega

theorem arithmetic_trace (first second coordinate : SignedWord) :
    (arithmetic first second coordinate).1.2 =
      (BinarySmallUniformSplitLifetime.splitWithTrace first second (FixedArrayTable.ofFn (fun _ => coordinate))).2 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,arithmetic_record,joinArithmetic,BinarySmallUniformSplitLifetime.splitWithTrace,
    FixedArrayTable.read_ofFn,BinaryQuadraticMeasured.apply_erases]

def collect (computed : ((SignedWord × SignedWord) × Trace) × ℕ)
    (packed : (FixedArrayTable 4 SignedWord × Trace) × ℕ) : (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  ((packed.1.1,wrap 16 2 [computed.1.2,packed.1.2]),computed.2+packed.2+8)

set_option cleanup.letToHave false in
def splitWithExtras (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) : ((FixedArrayTable 4 SignedWord × Trace) × ℕ) × ℕ :=
  let computed := arithmeticWithExtras first second (row.read 0)
  let packed := BinaryThreeReferenceMeasured.references 4 ![computed.1.1.1.1,computed.1.1.1.2,row.read 1,row.read 2]
  (collect computed.1 packed,computed.2)

def split (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    (FixedArrayTable 4 SignedWord × Trace) × ℕ :=
  (splitWithExtras first second row).1

theorem splitWithExtras_compat (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    (splitWithExtras first second row).1 = split first second row := rfl

theorem split_record (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    split first second row =
  let computed := arithmetic first second (row.read 0)
  let packed := BinaryThreeReferenceMeasured.references 4 ![computed.1.1.1,computed.1.1.2,row.read 1,row.read 2]
  collect computed packed := by
  simp only [split,splitWithExtras,BinaryLifetimeArrayExtras.build_record,BinaryNormalizedCoordinate.opcode_record,arithmeticWithExtras_compat]

theorem split_eq (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) : split first second row =
    let computed := arithmetic first second (row.read 0)
    let packed := BinaryThreeReferenceMeasured.references 4 ![computed.1.1.1,computed.1.1.2,row.read 1,row.read 2]
    collect computed packed := by
  rw [split_record]

theorem split_data (first second : SignedWord) (row : FixedArrayTable 3 SignedWord) :
    (split first second row).1.1 = (BinarySmallUniformSplitLifetime.splitWithTrace first second row).1 := by
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,split_record,collect,arithmetic_record,joinArithmetic,BinaryThreeReferenceMeasured.references_data,
    BinarySmallUniformSplitLifetime.splitWithTrace,BinaryQuadraticMeasured.apply_erases]

def workEnvelope (s : ℕ) : ℕ := 5*opcodePrice (expressionHeightBudget s 2)+1800
def envelope (s : ℕ) : ℕ := BinarySmallUniformSplitLifetime.envelope s+1000

theorem arithmetic_work (first second coordinate : SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second) (hCoordinateC : CanonicalWord coordinate)
    (s : ℕ) (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hCoordinate : RationalHeight (value coordinate) s) :
    (arithmetic first second coordinate).2 ≤ 5*opcodePrice (expressionHeightBudget s 2)+16 := by
  let total := BinaryQuadraticMeasured.apply .add first second
  let low := BinaryQuadraticMeasured.apply .div first total.1.1
  let high := BinaryQuadraticMeasured.apply .div second total.1.1
  let left := BinaryQuadraticMeasured.apply .mul low.1.1 coordinate
  let right := BinaryQuadraticMeasured.apply .mul high.1.1 coordinate
  have hTotalState : total.1.1 = BinaryRationalOpcode.apply .add first second :=
    apply_state .add first second hFirstC.1 hSecondC.1
  have hTotalC : CanonicalWord total.1.1 := by
    rw [hTotalState]
    exact BinaryReflectedFourSetup.opcode_canonical .add first second hFirstC hSecondC
  have hLowState : low.1.1 = BinaryRationalOpcode.apply .div first total.1.1 :=
    apply_state .div first total.1.1 hFirstC.1 hTotalC.1
  have hHighState : high.1.1 = BinaryRationalOpcode.apply .div second total.1.1 :=
    apply_state .div second total.1.1 hSecondC.1 hTotalC.1
  have hLowC : CanonicalWord low.1.1 := by
    rw [hLowState]
    exact BinaryReflectedFourSetup.opcode_canonical .div first total.1.1 hFirstC hTotalC
  have hHighC : CanonicalWord high.1.1 := by
    rw [hHighState]
    exact BinaryReflectedFourSetup.opcode_canonical .div second total.1.1 hSecondC hTotalC
  have hTotalH : RationalHeight (value total.1.1) (expressionHeightBudget s 1) := by
    rw [hTotalState,BinaryRationalOpcode.apply_value .add _ _ hFirstC.1 hSecondC.1]
    have hf : RationalHeight (value first) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hFirst
    have hs : RationalHeight (value second) (expressionHeightBudget s 0) := by
      simpa only [expressionHeightBudget_zero] using hSecond
    exact hf.add_level hs
  have hLowH : RationalHeight (value low.1.1) (expressionHeightBudget s 2) := by
    rw [hLowState,BinaryRationalOpcode.apply_value .div _ _ hFirstC.1 hTotalC.1]
    exact (hFirst.mono (expressionHeightBudget_ge_input s 1)).div_level hTotalH
  have hHighH : RationalHeight (value high.1.1) (expressionHeightBudget s 2) := by
    rw [hHighState,BinaryRationalOpcode.apply_value .div _ _ hSecondC.1 hTotalC.1]
    exact (hSecond.mono (expressionHeightBudget_ge_input s 1)).div_level hTotalH
  let W := 2 * expressionHeightBudget s 2 + 1
  have hFirstW : width first ≤ W := by
    have he := hFirstC.2.trans (rationalWordWidth_of_height hFirst)
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hSecondW : width second ≤ W := by
    have he := hSecondC.2.trans (rationalWordWidth_of_height hSecond)
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hTotalW : width total.1.1 ≤ W := by
    have he := hTotalC.2.trans (rationalWordWidth_of_height hTotalH)
    have hm := expressionHeightBudget_mono s (by decide : 1 ≤ 2)
    dsimp only [W]
    omega
  have hLowW : width low.1.1 ≤ W := by
    have he := hLowC.2.trans (rationalWordWidth_of_height hLowH)
    dsimp only [W]
    omega
  have hHighW : width high.1.1 ≤ W := by
    have he := hHighC.2.trans (rationalWordWidth_of_height hHighH)
    dsimp only [W]
    omega
  have hRowW : width coordinate ≤ W := by
    have he := hCoordinateC.2.trans (rationalWordWidth_of_height hCoordinate)
    have hm := expressionHeightBudget_ge_input s 2
    dsimp only [W]
    omega
  have hT := BinaryFourGuardMeasured.opcode_work .add first second W hFirstW hSecondW
  have hL := BinaryFourGuardMeasured.opcode_work .div first total.1.1 W hFirstW hTotalW
  have hH := BinaryFourGuardMeasured.opcode_work .div second total.1.1 W hSecondW hTotalW
  have hP := BinaryFourGuardMeasured.opcode_work .mul low.1.1 coordinate W hLowW hRowW
  have hQ := BinaryFourGuardMeasured.opcode_work .mul high.1.1 coordinate W hHighW hRowW
  have hPrice : 11000*(W+1)^2 = opcodePrice (expressionHeightBudget s 2) := by
    rfl
  rw [hPrice] at hT hL hH hP hQ
  have hResult := joinArithmetic_work total low high left right _ hT hL hH hP hQ
  rw [arithmetic_eq]
  simpa only [total,low,high,left,right] using hResult

theorem collect_bounds (computed : ((SignedWord × SignedWord) × Trace) × ℕ)
    (packed : (FixedArrayTable 4 SignedWord × Trace) × ℕ) (W U : ℕ)
    (hcW : computed.2 ≤ W+16) (hcU : usage computed.1.2 ≤ U)
    (hpW : packed.2 ≤ 1616) (hpU : usage packed.1.2 ≤ 915) :
    (collect computed packed).2 ≤ W+1800 ∧ usage (collect computed packed).1.2 ≤ U+1000 := by
  have hw := wrap_usage 16 2 [computed.1.2,packed.1.2]
  simp only [BinaryPlannedQuadratic.apply_previous,BinaryPlannedQuadratic.applyMeasured_previous,List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change computed.2+packed.2+8 ≤ _ ∧ usage (wrap 16 2 [computed.1.2,packed.1.2]) ≤ _
  exact ⟨by omega,by omega⟩

theorem split_bounds (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second)
    (hRowC : ∀ j,CanonicalWord (row.read j)) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hRow : ∀ j,RationalHeight (value (row.read j)) s) :
    (split first second row).2 ≤ workEnvelope s ∧ usage (split first second row).1.2 ≤ envelope s := by
  let computed := arithmetic first second (row.read 0)
  let packed := BinaryThreeReferenceMeasured.references 4 ![computed.1.1.1,computed.1.1.2,row.read 1,row.read 2]
  have hW := arithmetic_work first second (row.read 0) hFirstC hSecondC (hRowC 0) s hFirst hSecond (hRow 0)
  have hU : usage computed.1.2 ≤ BinarySmallUniformSplitLifetime.envelope s := by
    rw [arithmetic_trace]
    exact BinarySmallUniformSplitLifetime.splitWithTrace_usage first second _ hFirstC hSecondC
      (by intro j; simpa only [FixedArrayTable.read_ofFn] using hRowC 0) s hFirst hSecond
      (by intro j; simpa only [FixedArrayTable.read_ofFn] using hRow 0)
  have hPW : packed.2 ≤ 1616 := BinaryThreeReferenceMeasured.references_work 4 _
  have hPU : usage packed.1.2 ≤ 915 := BinaryThreeReferenceMeasured.references_usage 4 _
  have hResult := collect_bounds computed packed _ _ hW hU hPW hPU
  rw [split_eq]
  simpa only [computed,packed,workEnvelope,envelope] using hResult

theorem all_prefix (first second : SignedWord) (row : FixedArrayTable 3 SignedWord)
    (hFirstC : CanonicalWord first) (hSecondC : CanonicalWord second)
    (hRowC : ∀ j,CanonicalWord (row.read j)) (s : ℕ)
    (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s)
    (hRow : ∀ j,RationalHeight (value (row.read j)) s) (borrowed steps : ℕ) :
    retainedHeap borrowed (split first second row).1.2 steps ≤ borrowed+envelope s ∧
      framePeak ((split first second row).1.2.take steps) ≤ envelope s :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (split_bounds first second row hFirstC hSecondC hRowC s hFirst hSecond hRow).2 borrowed steps

end Blotto.BinarySmallUniformSplitMeasured
