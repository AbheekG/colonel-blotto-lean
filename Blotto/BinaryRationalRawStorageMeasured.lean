import Blotto.BinaryRationalComparisonMeasured

/-! Actual raw rational arithmetic returns value, allocation, retained storage
and source work in one reached producer. Old semantic/allocation/storage
programs occur only in correctness proofs. Native observer arithmetic, length
traversals, references and allocator/GC costs remain separate obligations. -/
namespace Blotto.BinaryRationalRawStorageMeasured
open BinaryRationalNormalization BinaryRationalArithmetic BinarySeedPreparationSpace
set_option autoImplicit false
set_option maxHeartbeats 3000000

structure Result where
  data : SignedWord
  allocated : ℕ
  storage : ℕ
  work : ℕ

def add (first second : SignedWord) : Result :=
  let leftProduced := BinaryCompareSignedMeasured.multiplyProduced (numeratorWord first) (denominatorWord second)
  let left := leftProduced.1.1
  let rightProduced := BinaryCompareSignedMeasured.multiplyProduced (numeratorWord second) (denominatorWord first)
  let right := rightProduced.1.1
  let numeratorProduced := BinaryCompareSignedMeasured.addProduced left.data right.data
  let numerator := numeratorProduced.1.1
  let denominatorProduced := BinaryAddMultiplyMetadata.multiplyProduced first.denominator second.denominator
  let denominator := denominatorProduced.1.1
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := left.allocated+right.allocated+numerator.allocated+denominator.allocated+4
  ⟨word,allocated,
    (1+leftProduced.2.1+rightProduced.2.2)+(1+rightProduced.2.1+leftProduced.2.2)+
      leftProduced.1.2+rightProduced.1.2+6+left.storage+right.storage+numerator.storage+
      (1+numeratorProduced.1.2+denominatorProduced.1.2)+denominator.storage+allocated,
    left.work+right.work+numerator.work+denominator.work+4⟩

theorem add_cached_record (first second : SignedWord) :
    add first second = (
  let left := BinaryCompareSignedMeasured.multiply (numeratorWord first) (denominatorWord second)
  let right := BinaryCompareSignedMeasured.multiply (numeratorWord second) (denominatorWord first)
  let numerator := BinaryCompareSignedMeasured.add left.data right.data
  let denominator := BinaryAddMultiplyMetadata.multiply first.denominator second.denominator
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := left.allocated+right.allocated+numerator.allocated+denominator.allocated+4
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      left.data.bits.length+right.data.bits.length+6+left.storage+right.storage+numerator.storage+
      BinaryRationalOpcodeAllocation.payload word+denominator.storage+allocated,
    left.work+right.work+numerator.work+denominator.work+4⟩) := by
  simp only [add,
    BinaryCompareSignedMeasured.multiplyProduced_lengths,BinaryCompareSignedMeasured.multiplyProduced_width,
    BinaryCompareSignedMeasured.multiplyProduced_public,BinaryCompareSignedMeasured.addProduced_width,
    BinaryCompareSignedMeasured.addProduced_public,BinaryCompareSignedMeasured.subtractProduced_width,
    BinaryCompareSignedMeasured.subtractProduced_public,BinaryAddMultiplyMetadata.multiplyProduced_lengths,
    BinaryAddMultiplyMetadata.multiplyProduced_width,BinaryAddMultiplyMetadata.multiply,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]

theorem add_previous_record (first second : SignedWord) :
    add first second = (
  let left := BinaryCompareSignedMeasured.multiply (numeratorWord first) (denominatorWord second)
  let right := BinaryCompareSignedMeasured.multiply (numeratorWord second) (denominatorWord first)
  let numerator := BinaryCompareSignedMeasured.add left.data right.data
  let denominator := BinaryCompareBitsMeasured.multiply first.denominator second.denominator
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := left.allocated+right.allocated+numerator.allocated+denominator.allocated+4
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      left.data.bits.length+right.data.bits.length+6+left.storage+right.storage+numerator.storage+
      BinaryRationalOpcodeAllocation.payload word+denominator.storage+allocated,
    left.work+right.work+numerator.work+denominator.work+4⟩) := by
  simp only [add_cached_record,BinaryAddMultiplyMetadata.multiply_exact]

theorem add_erases (first second : SignedWord) :
    ((add first second).data,(add first second).allocated) =
      BinaryRationalOpcodeAllocation.rawAddWithAllocation first second := by
  simp only [add_previous_record,BinaryRationalOpcodeAllocation.rawAddWithAllocation,
    ← BinaryCompareSignedMeasured.multiply_erases,← BinaryCompareSignedMeasured.add_erases,
    ← BinaryCompareBitsMeasured.multiply_erases]

theorem add_data (first second : SignedWord) : (add first second).data = rawAdd first second :=
  (congrArg Prod.fst (add_erases first second)).trans
    (BinaryRationalOpcodeAllocation.rawAddWithAllocation_state first second)

theorem add_allocated (first second : SignedWord) :
    (add first second).allocated = (BinaryRationalOpcodeAllocation.rawAddWithAllocation first second).2 :=
  congrArg Prod.snd (add_erases first second)

theorem add_storage (first second : SignedWord) :
    (add first second).storage = BinaryRationalOpcodeAllocation.rawAddStorage first second := by
  rw [BinaryRationalOpcodeAllocation.rawAddStorage,← add_data first second,← add_allocated first second]
  simp only [add_previous_record,BinaryRationalOpcodeAllocation.crossStorage,
    BinaryCompareSignedMeasured.multiply_storage,BinaryCompareSignedMeasured.multiply_data,
    BinaryCompareSignedMeasured.add_storage,BinaryCompareBitsMeasured.multiply_storage]

theorem add_work (first second : SignedWord) : (add first second).work = rawAddWork first second := by
  simp only [add_previous_record,rawAddWork,BinaryCompareSignedMeasured.multiply_work,
    BinaryCompareSignedMeasured.multiply_data,BinaryCompareSignedMeasured.add_work,
    BinaryCompareBitsMeasured.multiply_work]

def multiply (first second : SignedWord) : Result :=
  let numeratorProduced := BinaryCompareSignedMeasured.multiplyProduced (numeratorWord first) (numeratorWord second)
  let numerator := numeratorProduced.1.1
  let denominatorProduced := BinaryAddMultiplyMetadata.multiplyProduced first.denominator second.denominator
  let denominator := denominatorProduced.1.1
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+3
  ⟨word,allocated,
    (1+numeratorProduced.2.1+denominatorProduced.2.1)+(1+numeratorProduced.2.2+denominatorProduced.2.2)+
      (1+numeratorProduced.1.2+denominatorProduced.1.2)+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+3⟩

theorem multiply_cached_record (first second : SignedWord) :
    multiply first second = (
  let numerator := BinaryCompareSignedMeasured.multiply (numeratorWord first) (numeratorWord second)
  let denominator := BinaryAddMultiplyMetadata.multiply first.denominator second.denominator
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+3
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      BinaryRationalOpcodeAllocation.payload word+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+3⟩) := by
  simp only [multiply,
    BinaryCompareSignedMeasured.multiplyProduced_lengths,BinaryCompareSignedMeasured.multiplyProduced_width,
    BinaryCompareSignedMeasured.multiplyProduced_public,BinaryCompareSignedMeasured.addProduced_width,
    BinaryCompareSignedMeasured.addProduced_public,BinaryCompareSignedMeasured.subtractProduced_width,
    BinaryCompareSignedMeasured.subtractProduced_public,BinaryAddMultiplyMetadata.multiplyProduced_lengths,
    BinaryAddMultiplyMetadata.multiplyProduced_width,BinaryAddMultiplyMetadata.multiply,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]

theorem multiply_previous_record (first second : SignedWord) :
    multiply first second = (
  let numerator := BinaryCompareSignedMeasured.multiply (numeratorWord first) (numeratorWord second)
  let denominator := BinaryCompareBitsMeasured.multiply first.denominator second.denominator
  let word : SignedWord := ⟨numerator.data.negative,numerator.data.bits,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+3
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      BinaryRationalOpcodeAllocation.payload word+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+3⟩) := by
  simp only [multiply_cached_record,BinaryAddMultiplyMetadata.multiply_exact]

theorem multiply_erases (first second : SignedWord) :
    ((multiply first second).data,(multiply first second).allocated) =
      BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation first second := by
  simp only [multiply_previous_record,BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation,
    ← BinaryCompareSignedMeasured.multiply_erases,← BinaryCompareBitsMeasured.multiply_erases]

theorem multiply_data (first second : SignedWord) : (multiply first second).data = rawMultiply first second :=
  (congrArg Prod.fst (multiply_erases first second)).trans
    (BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation_state first second)

theorem multiply_allocated (first second : SignedWord) :
    (multiply first second).allocated = (BinaryRationalOpcodeAllocation.rawMultiplyWithAllocation first second).2 :=
  congrArg Prod.snd (multiply_erases first second)

theorem multiply_storage (first second : SignedWord) :
    (multiply first second).storage = BinaryRationalOpcodeAllocation.rawMultiplyStorage first second := by
  rw [BinaryRationalOpcodeAllocation.rawMultiplyStorage,← multiply_data first second,← multiply_allocated first second]
  simp only [multiply_previous_record,BinaryCompareSignedMeasured.multiply_storage,BinaryCompareBitsMeasured.multiply_storage]

theorem multiply_work (first second : SignedWord) :
    (multiply first second).work = rawMultiplyWork first second := by
  simp only [multiply_previous_record,rawMultiplyWork,BinaryCompareSignedMeasured.multiply_work,
    BinaryCompareBitsMeasured.multiply_work]

def divideProduced (first second : SignedWord) : Result × ((ℕ × ℕ) × (ℕ × ℕ)) :=
  let numeratorProduced := BinaryAddMultiplyMetadata.multiplyProduced first.numerator second.denominator
  let numerator := numeratorProduced.1.1
  let denominatorProduced := BinaryAddMultiplyMetadata.multiplyProduced first.denominator second.numerator
  let denominator := denominatorProduced.1.1
  let word : SignedWord := ⟨Bool.xor first.negative second.negative,numerator.data,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+4
  (⟨word,allocated,
    (1+numeratorProduced.2.1+denominatorProduced.2.1)+(1+denominatorProduced.2.2+numeratorProduced.2.2)+
      (1+numeratorProduced.1.2+denominatorProduced.1.2)+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+4⟩,
    ((numeratorProduced.2.1,denominatorProduced.2.1),(denominatorProduced.2.2,numeratorProduced.2.2)))

theorem divideProduced_widths (first second : SignedWord) :
    (divideProduced first second).2 =
      ((first.numerator.length,first.denominator.length),(second.numerator.length,second.denominator.length)) := by
  simp only [divideProduced,BinaryAddMultiplyMetadata.multiplyProduced_lengths]

def divide (first second : SignedWord) : Result := (divideProduced first second).1

attribute [irreducible] divideProduced

theorem divideProduced_public (first second : SignedWord) :
    (divideProduced first second).1 = divide first second := rfl

theorem divide_cached_record (first second : SignedWord) :
    divide first second = (
  let numerator := BinaryAddMultiplyMetadata.multiply first.numerator second.denominator
  let denominator := BinaryAddMultiplyMetadata.multiply first.denominator second.numerator
  let word : SignedWord := ⟨Bool.xor first.negative second.negative,numerator.data,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+4
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      BinaryRationalOpcodeAllocation.payload word+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+4⟩) := by
  simp only [divide,divideProduced,
    BinaryCompareSignedMeasured.multiplyProduced_lengths,BinaryCompareSignedMeasured.multiplyProduced_width,
    BinaryCompareSignedMeasured.multiplyProduced_public,BinaryCompareSignedMeasured.addProduced_width,
    BinaryCompareSignedMeasured.addProduced_public,BinaryCompareSignedMeasured.subtractProduced_width,
    BinaryCompareSignedMeasured.subtractProduced_public,BinaryAddMultiplyMetadata.multiplyProduced_lengths,
    BinaryAddMultiplyMetadata.multiplyProduced_width,BinaryAddMultiplyMetadata.multiply,
    BinaryRationalOpcodeAllocation.payload,numeratorWord,denominatorWord]

theorem divide_previous_record (first second : SignedWord) :
    divide first second = (
  let numerator := BinaryCompareBitsMeasured.multiply first.numerator second.denominator
  let denominator := BinaryCompareBitsMeasured.multiply first.denominator second.numerator
  let word : SignedWord := ⟨Bool.xor first.negative second.negative,numerator.data,denominator.data⟩
  let allocated := numerator.allocated+denominator.allocated+4
  ⟨word,allocated,
    BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
      BinaryRationalOpcodeAllocation.payload word+5+numerator.storage+denominator.storage+allocated,
    numerator.work+denominator.work+4⟩) := by
  simp only [divide_cached_record,BinaryAddMultiplyMetadata.multiply_exact]

theorem divide_erases (first second : SignedWord) :
    ((divide first second).data,(divide first second).allocated) =
      BinaryRationalOpcodeAllocation.rawDivideWithAllocation first second := by
  simp only [divide_previous_record,BinaryRationalOpcodeAllocation.rawDivideWithAllocation,
    ← BinaryCompareBitsMeasured.multiply_erases]

theorem divide_data (first second : SignedWord) : (divide first second).data = rawDivide first second :=
  (congrArg Prod.fst (divide_erases first second)).trans
    (BinaryRationalOpcodeAllocation.rawDivideWithAllocation_state first second)

theorem divide_allocated (first second : SignedWord) :
    (divide first second).allocated = (BinaryRationalOpcodeAllocation.rawDivideWithAllocation first second).2 :=
  congrArg Prod.snd (divide_erases first second)

theorem divide_storage (first second : SignedWord) :
    (divide first second).storage = BinaryRationalOpcodeAllocation.rawDivideStorage first second := by
  rw [BinaryRationalOpcodeAllocation.rawDivideStorage,← divide_data first second,← divide_allocated first second]
  simp only [divide_previous_record,BinaryCompareBitsMeasured.multiply_storage]

theorem divide_work (first second : SignedWord) : (divide first second).work = rawDivideWork first second := by
  simp only [divide_previous_record,rawDivideWork,BinaryCompareBitsMeasured.multiply_work]

def wordWidths (word : SignedWord) : ℕ × ℕ :=
  (BinaryBorrowDropMetadata.countFrom word.numerator 0,BinaryBorrowDropMetadata.countFrom word.denominator 0)

theorem wordWidths_exact (word : SignedWord) :
    wordWidths word = (word.numerator.length,word.denominator.length) := by
  simp only [wordWidths,BinaryBorrowDropMetadata.count_exact,Nat.zero_add]

def apply : RealArithmeticOp → SignedWord → SignedWord → Result
  | .add,first,second => add first second
  | .sub,first,second =>
      let result := add first (BinaryRationalArithmetic.negate second)
      ⟨result.data,result.allocated+1,result.storage+1,1+result.work⟩
  | .mul,first,second => multiply first second
  | .div,first,second =>
      let scan := BinaryNormalizationAllocation.scanWithFrames second.numerator
      if scan.1 then
        let produced := divideProduced first second
        let result := produced.1
        ⟨result.data,result.allocated+scan.2+2,
          (1+produced.2.1.1+produced.2.1.2)+(1+produced.2.2.1+produced.2.2.2)+
            scan.2+4+result.storage,
          3*(produced.2.2.1+1)+2+result.work⟩
      else
        let a := wordWidths first
        let b := wordWidths second
        ⟨BinaryRationalOpcode.zero,scan.2+3,(1+a.1+a.2)+(1+b.1+b.2)+scan.2+4+2,
          3*(b.1+1)+2+2⟩
  | .minimum,first,second =>
      let produced := BinaryRationalComparisonMeasured.compareProduced first second
      let compared := produced.1
      ⟨if compared.data then first else second,compared.allocated+2,
        compared.storage+produced.2.1+produced.2.2+2,compared.work+2⟩
  | .maximum,first,second =>
      let produced := BinaryRationalComparisonMeasured.compareProduced first second
      let compared := produced.1
      ⟨if compared.data then second else first,compared.allocated+2,
        compared.storage+produced.2.1+produced.2.2+2,compared.work+2⟩

theorem apply_previous_record (op : RealArithmeticOp) (first second : SignedWord) :
    apply op first second = (
match op with
  | .add => add first second
  | .sub =>
      let result := add first (BinaryRationalArithmetic.negate second)
      ⟨result.data,result.allocated+1,result.storage+1,1+result.work⟩
  | .mul => multiply first second
  | .div =>
      let scan := BinaryNormalizationAllocation.scanWithFrames second.numerator
      if scan.1 then
        let result := divide first second
        ⟨result.data,result.allocated+scan.2+2,
          BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
            scan.2+4+result.storage,
          3*(second.numerator.length+1)+2+result.work⟩
      else ⟨BinaryRationalOpcode.zero,scan.2+3,
        BinaryRationalOpcodeAllocation.payload first+BinaryRationalOpcodeAllocation.payload second+
          scan.2+4+BinaryRationalOpcodeAllocation.payload BinaryRationalOpcode.zero,
        3*(second.numerator.length+1)+2+2⟩
  | .minimum =>
      let compared := BinaryRationalComparisonMeasured.compare first second
      ⟨if compared.data then first else second,compared.allocated+2,
        compared.storage+BinaryRationalOpcodeAllocation.payload first+
          BinaryRationalOpcodeAllocation.payload second+2,compared.work+2⟩
  | .maximum =>
      let compared := BinaryRationalComparisonMeasured.compare first second
      ⟨if compared.data then second else first,compared.allocated+2,
        compared.storage+BinaryRationalOpcodeAllocation.payload first+
          BinaryRationalOpcodeAllocation.payload second+2,compared.work+2⟩) := by
  cases op <;> simp only [apply,divideProduced_public,divideProduced_widths,wordWidths_exact,
    BinaryRationalComparisonMeasured.compareProduced_public,
    BinaryRationalComparisonMeasured.compareProduced_payloads,BinaryRationalOpcodeAllocation.payload,
    BinaryRationalOpcode.zero,List.length_nil,List.length_cons] <;> rfl

theorem apply_erases (op : RealArithmeticOp) (first second : SignedWord) :
    ((apply op first second).data,(apply op first second).allocated) =
      BinaryRationalOpcodeAllocation.rawApplyWithAllocation op first second := by
  cases op <;> simp only [apply_previous_record,BinaryRationalOpcodeAllocation.rawApplyWithAllocation,
    ← add_erases,← multiply_erases,← divide_erases,← BinaryRationalComparisonMeasured.compare_erases]
  split <;> rfl

theorem apply_data (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).data = BinaryRationalOpcode.rawApply op first second :=
  (congrArg Prod.fst (apply_erases op first second)).trans
    (BinaryRationalOpcodeAllocation.rawApplyWithAllocation_state op first second)

theorem apply_allocated (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).allocated =
      (BinaryRationalOpcodeAllocation.rawApplyWithAllocation op first second).2 :=
  congrArg Prod.snd (apply_erases op first second)

theorem apply_storage (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).storage = BinaryRationalOpcodeAllocation.rawStorage op first second := by
  cases op <;> simp only [apply_previous_record,BinaryRationalOpcodeAllocation.rawStorage,add_storage,multiply_storage,
    divide_storage,BinaryRationalComparisonMeasured.compare_storage,
    BinaryNormalizationAllocation.scanWithFrames_state]
  by_cases hScan : BinaryEuclideanGCD.nonzero second.numerator = true <;>
    simp only [hScan,Bool.false_eq_true,ite_true,ite_false]

theorem apply_work (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).work = BinaryRationalOpcode.rawApplyWork op first second := by
  cases op <;> simp only [apply_previous_record,BinaryRationalOpcode.rawApplyWork,add_work,multiply_work,divide_work,
    BinaryRationalComparisonMeasured.compare_work,BinaryNormalizationAllocation.scanWithFrames_state]
  by_cases hScan : BinaryEuclideanGCD.nonzero second.numerator = true <;>
    simp only [hScan,Bool.false_eq_true,ite_true,ite_false]

theorem apply_storage_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).storage ≤ 3000*(pairWidth first second+1)^3 := by
  rw [apply_storage]
  exact BinaryRationalOpcodeAllocation.rawStorage_bound op first second

theorem apply_work_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (apply op first second).work ≤ 510*(pairWidth first second+1)^2 := by
  rw [apply_work]
  exact BinaryRationalOpcode.rawApplyWork_bound op first second

def traced (op : RealArithmeticOp) (first second : SignedWord) : (SignedWord × Trace) × ℕ :=
  let result := apply op first second
  ((result.data,[.frames (result.allocated+8),.arrayAllocation 16,.listAllocation result.storage]),result.work)

theorem traced_erases (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).1 = BinaryQuadraticLifetime.rawWithTrace op first second := by
  simp only [traced,BinaryQuadraticLifetime.rawWithTrace,apply_allocated,apply_storage,apply_data,
    BinaryRationalOpcodeAllocation.rawApplyWithAllocation_state]

theorem traced_data (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).1.1 = BinaryRationalOpcode.rawApply op first second := apply_data _ _ _

theorem traced_work (op : RealArithmeticOp) (first second : SignedWord) :
    (traced op first second).2 = BinaryRationalOpcode.rawApplyWork op first second := apply_work _ _ _

theorem traced_all_prefix (op : RealArithmeticOp) (first second : SignedWord) (borrowed steps : ℕ) :
    retainedHeap borrowed (traced op first second).1.2 steps ≤
      borrowed+3000*(pairWidth first second+1)^3+16 ∧
    framePeak ((traced op first second).1.2.take steps) ≤ 200*(pairWidth first second+1)^2+8 := by
  rw [traced_erases]
  have h := BinaryQuadraticLifetime.rawWithTrace_bounds op first second
  have hl := listCells_take_le (BinaryQuadraticLifetime.rawWithTrace op first second).2 steps
  have ha := arraySlots_take_le (BinaryQuadraticLifetime.rawWithTrace op first second).2 steps
  have hf := framePeak_take_le (BinaryQuadraticLifetime.rawWithTrace op first second).2 steps
  exact ⟨by unfold retainedHeap; omega,hf.trans h.2⟩


end Blotto.BinaryRationalRawStorageMeasured
