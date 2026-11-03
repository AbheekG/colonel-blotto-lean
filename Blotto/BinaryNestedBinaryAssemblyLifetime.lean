import Blotto.BinaryNestedSecondUniformLifetime

/-! Actual nine-plus-nine binary mixture assembly. The complement is computed
once; eighteen traced multiplications produce weights, and two retained arrays
copy the endpoint-row references. -/
namespace Blotto.BinaryNestedBinaryAssemblyLifetime
open BinaryRationalNormalization BinaryRationalEncoding BinarySeedPreparationSpace
open BinaryPRGHeapTraceUsage BinaryLifetimeUsage
set_option maxHeartbeats 2000000

abbrev Small := BinaryStoredOverlapEnvironment.Segment 3 9
abbrev Large := BinaryStoredOverlapEnvironment.Segment 3 18

def weightsWithTrace (p q : SignedWord) (first second : FixedArrayTable 9 SignedWord) :
    FixedArrayTable 18 SignedWord × Trace :=
  BinaryLifetimeArray.build 18 (fun slot => Fin.addCases (n := 9)
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul p (first.read j))
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul q (second.read j)) slot)

theorem weightsWithTrace_erasure (p q : SignedWord)
    (first second : FixedArrayTable 9 SignedWord)
    (hP : CanonicalWord p) (hQ : CanonicalWord q)
    (hFirst : ∀ j,CanonicalWord (first.read j)) (hSecond : ∀ j,CanonicalWord (second.read j)) :
    (weightsWithTrace p q first second).1 = FixedArrayTable.ofFn (Fin.addCases (n := 9)
      (fun j => BinaryRationalOpcode.apply .mul p (first.read j))
      (fun j => BinaryRationalOpcode.apply .mul q (second.read j))) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro slot
  refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot
  · simp only [weightsWithTrace,BinaryLifetimeArray.build_erases,
      FixedArrayTable.read_ofFn,Fin.addCases_left]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ hP.1 (hFirst j).1
  · simp only [weightsWithTrace,BinaryLifetimeArray.build_erases,
      FixedArrayTable.read_ofFn,Fin.addCases_right]
    exact BinaryQuadraticLifetime.applyWithTrace_state .mul _ _ hQ.1 (hSecond j).1

def weightEnvelope (W : ℕ) : ℕ := 19 * opcodeEnvelope W + 768

theorem weightsWithTrace_usage (p q : SignedWord)
    (first second : FixedArrayTable 9 SignedWord) (W : ℕ)
    (hP : width p ≤ W) (hQ : width q ≤ W)
    (hFirst : ∀ j,width (first.read j) ≤ W) (hSecond : ∀ j,width (second.read j) ≤ W) :
    usage (weightsWithTrace p q first second).2 ≤ weightEnvelope W := by
  let produce : Fin 18 → SignedWord × Trace := fun slot => Fin.addCases (n := 9) (m := 9)
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul p (first.read j))
    (fun j => BinaryQuadraticLifetime.applyWithTrace .mul q (second.read j)) slot
  have hEach : ∀ slot,usage (produce slot).2 ≤ opcodeEnvelope W := by
    intro slot
    refine Fin.addCases (n := 9) (m := 9) (fun j => ?_) (fun j => ?_) slot
    · simpa only [produce,Fin.addCases_left] using opcode_usage .mul p (first.read j) W hP (hFirst j)
    · simpa only [produce,Fin.addCases_right] using opcode_usage .mul q (second.read j) W hQ (hSecond j)
  have ha := array_usage 18 produce (opcodeEnvelope W) (opcodeEnvelope W)
    (by intro slot; have h := hEach slot; unfold usage BinaryPRGHeapPrimitiveLifetime.cells at h; omega)
    (by intro slot; have h := hEach slot; unfold usage at h; omega)
  change usage (BinaryLifetimeArray.build 18 produce).2 ≤ _
  unfold weightEnvelope
  omega

def rowsWithTrace {α : Type*} (first second : FixedArrayTable 9 α) :
    FixedArrayTable 18 α × Trace :=
  BinaryLifetimeArray.build 18 (fun slot =>
    (Fin.addCases (n := 9) first.read second.read slot,wrap 8 1 []))

theorem rowsWithTrace_erasure {α : Type*} (first second : FixedArrayTable 9 α) :
    (rowsWithTrace first second).1 =
      FixedArrayTable.ofFn (Fin.addCases (n := 9) first.read second.read) := rfl

theorem rowsWithTrace_usage {α : Type*} (first second : FixedArrayTable 9 α) :
    usage (rowsWithTrace first second).2 ≤ 899 := by
  let produce : Fin 18 → α × Trace := fun slot =>
    (Fin.addCases (n := 9) (m := 9) first.read second.read slot,wrap 8 1 [])
  have hCells : ∀ slot,listCells (produce slot).2 + arraySlots (produce slot).2 ≤ 8 := by
    intro slot
    change listCells (wrap 8 1 []) + arraySlots (wrap 8 1 []) ≤ 8
    simp [wrap,combine,listCells,arraySlots]
  have hFrames : ∀ slot,framePeak (produce slot).2 ≤ 1 := by
    intro slot
    change framePeak (wrap 8 1 []) ≤ 1
    simp [wrap,combine,framePeak]
  have ha := array_usage (α := α) 18 produce 8 1 hCells hFrames
  change usage (BinaryLifetimeArray.build 18 produce).2 ≤ _
  omega

def binaryWithTrace (p : SignedWord) (first second : Small) : Large × Trace :=
  let complement := BinaryQuadraticLifetime.applyWithTrace .sub
    BinaryExpressionCompiler.Constant.one.word p
  let weights := weightsWithTrace p complement.1 first.weight second.weight
  let P := rowsWithTrace first.P second.P
  let Q := rowsWithTrace first.Q second.Q
  (⟨weights.1,P.1,Q.1⟩,wrap 40 3 [complement.2,weights.2,P.2,Q.2])

theorem binaryWithTrace_erasure (p : SignedWord) (first second : Small)
    (hP : CanonicalWord p) (hFirst : first.Canonical) (hSecond : second.Canonical) :
    (binaryWithTrace p first second).1 = BinarySegmentAssembly.binary p first second := by
  have hOne := BinaryExpressionCompiler.Constant.word_canonical .one
  have hComplement := BinaryQuadraticLifetime.applyWithTrace_state .sub
    BinaryExpressionCompiler.Constant.one.word p hOne.1 hP.1
  have hComplementC : CanonicalWord
      (BinaryQuadraticLifetime.applyWithTrace .sub BinaryExpressionCompiler.Constant.one.word p).1 := by
    rw [hComplement]
    exact BinaryReflectedFourSetup.opcode_canonical .sub _ _ hOne hP
  dsimp only [binaryWithTrace]
  rw [weightsWithTrace_erasure _ _ _ _ hP hComplementC hFirst.1 hSecond.1]
  simp only [BinarySegmentAssembly.binary,rowsWithTrace_erasure,hComplement]

def envelope (W : ℕ) : ℕ := 20 * opcodeEnvelope (3 * W + 1) + 4096

theorem binaryWithTrace_usage (p : SignedWord) (first second : Small)
    (hP : CanonicalWord p) (W : ℕ) (hW : 1 ≤ W) (hp : width p ≤ W)
    (hFirst : ∀ j,width (first.weight.read j) ≤ W)
    (hSecond : ∀ j,width (second.weight.read j) ≤ W) :
    usage (binaryWithTrace p first second).2 ≤ envelope W := by
  let complement := BinaryQuadraticLifetime.applyWithTrace .sub
    BinaryExpressionCompiler.Constant.one.word p
  let weights := weightsWithTrace p complement.1 first.weight second.weight
  let P := rowsWithTrace first.P second.P
  let Q := rowsWithTrace first.Q second.Q
  have hOne : width BinaryExpressionCompiler.Constant.one.word ≤ W := by
    change 1 ≤ W
    exact hW
  have hComplementW : width complement.1 ≤ 3*W+1 := by
    rw [BinaryQuadraticLifetime.applyWithTrace_state .sub _ _
      (BinaryExpressionCompiler.Constant.word_canonical .one).1 hP.1]
    have h := BinaryPRGPreparationWork.apply_stored_width .sub
      BinaryExpressionCompiler.Constant.one.word p
    have hm : BinaryRationalArithmetic.pairWidth BinaryExpressionCompiler.Constant.one.word p ≤ W :=
      max_le hOne hp
    omega
  have hComplement := opcode_usage .sub BinaryExpressionCompiler.Constant.one.word p
    (3*W+1) (by omega) (by omega)
  change usage complement.2 ≤ _ at hComplement
  have hWeights := weightsWithTrace_usage p complement.1 first.weight second.weight
    (3*W+1) (by omega) hComplementW (fun j => (hFirst j).trans (by omega))
      (fun j => (hSecond j).trans (by omega))
  change usage weights.2 ≤ _ at hWeights
  have hRowsP := rowsWithTrace_usage first.P second.P
  have hRowsQ := rowsWithTrace_usage first.Q second.Q
  change usage P.2 ≤ _ at hRowsP
  change usage Q.2 ≤ _ at hRowsQ
  have hw := wrap_usage 40 3 [complement.2,weights.2,P.2,Q.2]
  simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil] at hw
  change usage (wrap 40 3 [complement.2,weights.2,P.2,Q.2]) ≤ _
  unfold envelope weightEnvelope at *
  omega

theorem all_prefix (p : SignedWord) (first second : Small)
    (hP : CanonicalWord p) (W : ℕ) (hW : 1 ≤ W) (hp : width p ≤ W)
    (hFirst : ∀ j,width (first.weight.read j) ≤ W)
    (hSecond : ∀ j,width (second.weight.read j) ≤ W) (borrowed steps : ℕ) :
    retainedHeap borrowed (binaryWithTrace p first second).2 steps ≤ borrowed + envelope W ∧
    framePeak ((binaryWithTrace p first second).2.take steps) ≤ envelope W :=
  BinaryPRGHeapTraceUsage.all_prefix _ _
    (binaryWithTrace_usage p first second hP W hW hp hFirst hSecond) borrowed steps

end Blotto.BinaryNestedBinaryAssemblyLifetime
