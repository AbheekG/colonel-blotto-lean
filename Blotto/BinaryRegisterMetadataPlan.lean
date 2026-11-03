import Blotto.BinaryRegisterBooleanCount
import Blotto.BinaryRegisterTreePlan

/-! Reached Boolean-list and register-tree metadata scans supply the existing
source charges. Those charges pay their actual case counts without changing
the old numeric ledger. Cursor carry produces its final-depth plan directly.
Native arithmetic/reference/record/allocator and physical-space joins remain. -/
namespace Blotto.BinaryRegisterMetadataPlan
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGWordControllerWordStore BinaryTracePlanMeasured BinaryTraceDepth
open BinaryNumericalReadbackPlan (view offset)
set_option autoImplicit false
set_option maxHeartbeats 3000000

def bitsFrom : List Bool → ℕ → ℕ × ℕ
  | [],count => (count,count+1)
  | _::rest,count => bitsFrom rest (count+1)

theorem bitsFrom_data (word : List Bool) (count : ℕ) : (bitsFrom word count).1 = count+word.length := by
  induction word generalizing count with
  | nil => rfl
  | cons bit rest ih => simp only [bitsFrom,List.length_cons,ih]; omega

theorem bitsFrom_work (word : List Bool) (count : ℕ) : (bitsFrom word count).2 = count+word.length+1 := by
  induction word generalizing count with
  | nil => rfl
  | cons bit rest ih => simp only [bitsFrom,List.length_cons,ih]; omega

def bits (word : List Bool) : ℕ × ℕ := BinaryRegisterBooleanCount.bits word

theorem bits_prior (word : List Bool) : bits word = bitsFrom word 0 := by
  apply Prod.ext
  · simp only [bits,BinaryRegisterBooleanCount.bits_record,bitsFrom_data,Nat.zero_add]
  · simp only [bits,BinaryRegisterBooleanCount.bits_record,bitsFrom_work,Nat.zero_add]

theorem bits_data (word : List Bool) : (bits word).1 = word.length := by
  simp only [bits,BinaryRegisterBooleanCount.bits_record]

theorem bits_work (word : List Bool) : (bits word).2 = word.length+1 := by
  simp only [bits,BinaryRegisterBooleanCount.bits_record]

def payload (word : SignedWord) : ℕ × ℕ :=
  let numerator := bits word.numerator
  let denominator := bits word.denominator
  (1+numerator.1+denominator.1,numerator.2+denominator.2+1)

theorem payload_data (word : SignedWord) : (payload word).1 = BinaryRationalExpression.payloadWords word := by
  simp only [payload,bits_data,BinaryRationalExpression.payloadWords]

theorem payload_work (word : SignedWord) : (payload word).2 = (payload word).1+2 := by
  simp only [payload,bits_data,bits_work]; omega

theorem payload_positive (word : SignedWord) : 1 ≤ (payload word).1 := by
  simp only [payload,bits_data]; omega

def readCharge (word : SignedWord) : ℕ := (payload word).2+44

theorem read_exact (word : SignedWord) : readCharge word = 46+BinaryRationalExpression.payloadWords word := by
  simp only [readCharge,payload_work,payload_data]; omega

theorem read_pays (word : SignedWord) : (payload word).2 ≤ readCharge word := by
  simp only [readCharge]; omega

def writeCharge (word : SignedWord) : ℕ := (payload word).2+54

theorem write_exact (word : SignedWord) : writeCharge word = 56+BinaryRationalExpression.payloadWords word := by
  simp only [writeCharge,payload_work,payload_data]; omega

theorem write_pays (word : SignedWord) : (payload word).2 ≤ writeCharge word := by
  simp only [writeCharge]; omega

def copied : {height : ℕ} → Tree height → ℕ × ℕ
  | _,.leaf word =>
      let produced := payload word
      (produced.1,produced.2+1)
  | _,.branch left right =>
      let first := copied left
      let second := copied right
      (first.1+second.1,first.2+second.2+1)

theorem copied_data {height : ℕ} (tree : Tree height) : (copied tree).1 = copiedPayload tree := by
  induction tree with
  | leaf word => simp only [copied,copiedPayload,payload_data]
  | branch left right hl hr => simp only [copied,copiedPayload,hl,hr]

theorem copied_work {height : ℕ} (tree : Tree height) :
    (copied tree).2+1 = copiedPayload tree+4*2^height := by
  induction tree with
  | leaf word => simp only [copied,copiedPayload,payload_work,payload_data,pow_zero]; omega
  | @branch height left right hl hr =>
      simp only [copied,copiedPayload,pow_succ]; omega

def initialCharge (tree : Tree 4) : ℕ := (copied tree).2+155

theorem initial_exact (tree : Tree 4) : initialCharge tree = 218+copiedPayload tree := by
  have h := copied_work tree
  norm_num only [Nat.reducePow,Nat.reduceMul] at h
  simp only [initialCharge]; omega

theorem initial_pays (tree : Tree 4) : (copied tree).2 ≤ initialCharge tree := by
  simp only [initialCharge]; omega

def sourceCharge (source : BinaryRationalPairProgram.Source) : ℕ :=
  let a := payload source.lengthI
  let b := payload source.lengthJ
  let c := payload source.resourceI
  let d := payload source.resourceJ
  a.2+b.2+c.2+d.2+(a.1+b.1+c.1+d.1-4)

theorem source_exact (source : BinaryRationalPairProgram.Source) : sourceCharge source = source.sourcePayloadWork := by
  simp only [sourceCharge,payload_work,payload_data,BinaryRationalPairProgram.Source.sourcePayloadWork,
    BinaryRationalRegisterProgram.payloadWords,BinaryRationalExpression.payloadWords]
  omega

theorem source_pays (source : BinaryRationalPairProgram.Source) :
    (payload source.lengthI).2+(payload source.lengthJ).2+
      (payload source.resourceI).2+(payload source.resourceJ).2 ≤ sourceCharge source := by
  simp only [sourceCharge]; omega

def cursorAt {width : ℕ} (word : FixedBinaryWord width) (depth : ℕ) :
    ((FixedBinaryWord width × Bool) × Plan) × ℕ :=
  let next := BinaryWordCoinPrimitivesMeasured.incrementBitsAt word.bits (depth+2)
  have hSize : next.1.1.1.length = width := by
    rw [BinaryWordCoinPrimitivesMeasured.incrementBitsAt_erases,
      BinaryWordStoreLifetime.incrementBitsWithTrace_erases,BinaryIndexWord.incrementBits_length,word.size]
  (((⟨next.1.1.1,hSize⟩,next.1.1.2),
    .join (.block [.frames (depth+2),.arrayAllocation 8]) (.block next.1.2)),next.2+2*width+2)

theorem cursor_refines {width : ℕ} (word : FixedBinaryWord width) (depth : ℕ) :
    view (cursorAt word depth) = offset depth (BinaryHeapEnumerationMeasured.advance word) := by
  simp only [cursorAt,BinaryHeapEnumerationMeasured.advance,BinaryWordCoinPrimitivesMeasured.incrementBits,
    view,offset,denote,BinaryWordCoinPrimitivesMeasured.incrementBitsAt_erases,
    BinaryWordCoinPrimitivesMeasured.incrementBitsAt_work,under_append,under_compose,under_zero]
  rfl

theorem cursor_bound {width : ℕ} (word : FixedBinaryWord width) (depth : ℕ) :
    nodes (cursorAt word depth).1.2 ≤ 2*BinaryTracePlanMeasured.payload (cursorAt word depth).1.2 := by
  simp only [cursorAt,nodes,BinaryTracePlanMeasured.payload,List.length_cons,List.length_nil]; omega

theorem cursor_work {width : ℕ} (word : FixedBinaryWord width) (depth : ℕ) :
    (cursorAt word depth).2 = 4*BinaryIndexWord.incrementVisits word.bits+2*width+2 := by
  simp only [cursorAt,BinaryWordCoinPrimitivesMeasured.incrementBitsAt_work]

-- Semantic work observers for the reached Boolean counter layer. The
-- producers retain their old two numeric fields and old source charges.
def counterPrice (word : SignedWord) : ℕ :=
  BinaryRegisterBooleanCount.sourcePrice word.numerator+BinaryRegisterBooleanCount.sourcePrice word.denominator

theorem counter_payload (word : SignedWord) : counterPrice word ≤ 752*(payload word).2 := by
  have hn := BinaryRegisterBooleanCount.source_price word.numerator
  have hd := BinaryRegisterBooleanCount.source_price word.denominator
  simp only [counterPrice,payload,bits_work]
  omega

theorem counter_read (word : SignedWord) : counterPrice word ≤ 752*readCharge word :=
  (counter_payload word).trans (Nat.mul_le_mul_left 752 (read_pays word))

theorem counter_write (word : SignedWord) : counterPrice word ≤ 752*writeCharge word :=
  (counter_payload word).trans (Nat.mul_le_mul_left 752 (write_pays word))

def copiedCounterPrice : {height : ℕ} → Tree height → ℕ
  | _,.leaf word => counterPrice word
  | _,.branch left right => copiedCounterPrice left+copiedCounterPrice right

theorem counter_copied {height : ℕ} (tree : Tree height) : copiedCounterPrice tree ≤ 752*(copied tree).2 := by
  induction tree with
  | leaf word =>
      have h := counter_payload word
      simp only [copiedCounterPrice,copied]
      omega
  | branch left right hl hr =>
      simp only [copiedCounterPrice,copied]
      omega

theorem counter_initial (tree : Tree 4) : copiedCounterPrice tree ≤ 752*initialCharge tree :=
  (counter_copied tree).trans (Nat.mul_le_mul_left 752 (initial_pays tree))

def sourceCounterPrice (source : BinaryRationalPairProgram.Source) : ℕ :=
  counterPrice source.lengthI+counterPrice source.lengthJ+counterPrice source.resourceI+counterPrice source.resourceJ

theorem counter_source (source : BinaryRationalPairProgram.Source) :
    sourceCounterPrice source ≤ 752*sourceCharge source := by
  have ha := counter_payload source.lengthI
  have hb := counter_payload source.lengthJ
  have hc := counter_payload source.resourceI
  have hd := counter_payload source.resourceJ
  have h := Nat.mul_le_mul_left 752 (source_pays source)
  unfold sourceCounterPrice
  omega

end Blotto.BinaryRegisterMetadataPlan
