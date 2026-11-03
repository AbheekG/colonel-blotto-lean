import Blotto.BinaryPRGWordControllerFramed
import Blotto.BinaryPRGFrameCostJoin

/-! Source-derived Store construction and actual quadratic output scaling /
coordinate framing for the executed raw controller.  Every data word is the
word produced by the selected backend.  Canonical source heights transfer by
semantic refinement; another backend's execution or allocation price does not.
The unjoined body factories/terminal/routes are explicitly outside this suffix
ledger, so this component bound is not called complete machine work. -/

namespace Blotto.BinaryPRGWordControllerFrameWork
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryPRGOutputPrimitiveWork RationalLottoResourceSystem
open scoped BigOperators

def rescaleWithWork {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    FixedArrayTable n SignedWord × ℕ :=
  let cells := FixedArrayTable.ofFn (fun j => BinaryQuadraticOpcode.applyWithWork .mul budget (row.read j))
  (FixedArrayTable.ofFn (fun j => (cells.read j).1),
    (∑ j, (cells.read j).2) + n * (n + 1) + 2 * n + 2)

theorem rescaleWithWork_erasure {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord) :
    (rescaleWithWork budget row).1 = FixedArrayTable.ofFn
      (fun j => BinaryQuadraticData.apply .mul budget (row.read j)) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [rescaleWithWork, FixedArrayTable.read_ofFn, BinaryQuadraticData.apply_erasure]

def scalingBound (n s : ℕ) : ℕ := n * (11000 * (2 * s + 2)^2) + n * (n + 1) + 2 * n + 2

theorem rescaleWithWork_bound {n : ℕ} (budget : SignedWord) (row : FixedArrayTable n SignedWord)
    (hB : CanonicalWord budget) (hC : ∀ j, CanonicalWord (row.read j)) (s : ℕ)
    (hH : RationalHeight (value budget) s) (hRow : ∀ j, RationalHeight (value (row.read j)) s) :
    (rescaleWithWork budget row).2 ≤ scalingBound n s := by
  have hBudget := hB.2.trans (rationalWordWidth_of_height hH)
  have hEach : ∀ j, (BinaryQuadraticOpcode.applyWithWork .mul budget (row.read j)).2 ≤
      11000 * (2 * s + 2)^2 := by
    intro j
    have hw := (hC j).2.trans (rationalWordWidth_of_height (hRow j))
    have hp : BinaryRationalArithmetic.pairWidth budget (row.read j) + 1 ≤ 2 * s + 2 := by
      unfold BinaryRationalArithmetic.pairWidth
      omega
    exact (BinaryQuadraticOpcode.applyWithWork_bound .mul budget (row.read j)).trans
      (Nat.mul_le_mul_left 11000 (Nat.pow_le_pow_left hp 2))
  have hSum : (∑ j, (BinaryQuadraticOpcode.applyWithWork .mul budget (row.read j)).2) ≤
      n * (11000 * (2 * s + 2)^2) := by
    calc
      _ ≤ ∑ _j : Fin n, (11000 * (2 * s + 2)^2) := Finset.sum_le_sum (fun j _ => hEach j)
      _ = _ := by simp
  unfold rescaleWithWork scalingBound
  simp only [FixedArrayTable.read_ofFn]
  omega

def normalized {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : FixedArrayTable n SignedWord :=
  BinaryPRGWordControllerRequest.vectorFixedSample prepared.request rich prepared.request.precision
    (coinBitBudget n prepared.request.precision) tables.outer.read tables.scalar.read tables.choice.read

theorem normalized_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    normalized prepared rich tables =
      (BinaryPRGCachedPrimitiveRun.sample prepared.request rich prepared.request.precision tables.flat).1 := by
  unfold normalized
  rw [BinaryPRGWordControllerRequest.vectorFixedSample_state,
    ← tables.outer_eq, ← tables.scalar_eq, ← tables.choice_eq]
  rw [BinaryPRGCachedPrimitiveRun.sample_state]
  rfl

theorem normalized_canonical {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    ∀ j, CanonicalWord ((normalized prepared rich tables).read j) := by
  rw [normalized_state]
  exact normalizedSample_canonical prepared.request rich prepared.request.precision tables.flat

theorem normalized_height {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) (j : Fin n) :
    RationalHeight (value ((normalized prepared rich tables).read j))
      (normalizedHeight prepared.request prepared.request.precision) := by
  rw [normalized_state]
  exact normalizedSample_height prepared.request rich prepared.request.precision tables.flat j

theorem scaled_state {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables)).1 =
      (BinaryPRGCachedPrimitiveRun.originalSample prepared.request rich tables.flat).1 := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  rw [rescaleWithWork_erasure]
  simp only [FixedArrayTable.read_ofFn, BinaryPRGCachedPrimitiveRun.originalSample,
    BinaryPRGOriginalSampler.rescale]
  rw [← BinaryQuadraticData.apply_erasure,
    BinaryQuadraticOpcode.applyWithWork_state .mul _ _ prepared.request.valid.2.1.1.1
      (normalized_canonical prepared rich tables j).1, normalized_state]

def outputSuffixWithWork {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) : List Bool × ℕ :=
  let scaled := rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables)
  let coordinates := List.ofFn scaled.1.read
  (prepared.header.bytes ++ BinaryStoredRowFrame.words coordinates,
    scaled.2 + BinaryStoredRowFrameWork.wordsVisits coordinates +
      prepared.header.bytes.length + 2 * n + 3)

theorem outputSuffixWithWork_erasure {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputSuffixWithWork prepared rich tables).1 = BinaryPRGWordControllerFramed.output prepared rich tables := by
  unfold outputSuffixWithWork BinaryPRGWordControllerFramed.output
  dsimp only
  rw [rescaleWithWork_erasure]
  rfl

noncomputable def suffixBound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) : ℕ :=
  scalingBound n (normalizedHeight prepared.request prepared.request.precision) +
    16 * n * outputWidth prepared.request + 12 * n + prepared.header.bytes.length + 3

theorem outputSuffixWithWork_bound {n : ℕ} (prepared : BinaryPRGAccuracyRulerRequest.Request n) (rich : Bool)
    (tables : BinaryPRGSeedBlocks.Tables n prepared.request.precision) :
    (outputSuffixWithWork prepared rich tables).2 ≤ suffixBound prepared := by
  have hScale := rescaleWithWork_bound prepared.request.prepared.original.a (normalized prepared rich tables)
    prepared.request.valid.2.1.1 (normalized_canonical prepared rich tables)
    (normalizedHeight prepared.request prepared.request.precision)
    (scale_height prepared.request prepared.request.precision) (normalized_height prepared rich tables)
  have hWords := BinaryStoredRowFrameWork.wordsVisits_bound (List.ofFn
    (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables)).1.read)
  have hSpines := storedSpines_bound (List.ofFn
    (rescaleWithWork prepared.request.prepared.original.a (normalized prepared rich tables)).1.read)
    (outputWidth prepared.request) (by
      intro word hw
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hw
      rw [scaled_state]
      exact originalSample_width prepared.request rich tables.flat j)
  simp only [List.length_ofFn] at hWords hSpines
  unfold outputSuffixWithWork suffixBound
  dsimp only
  nlinarith

/-- The choice array produces the exact list used by vectorFixedSample's Store.
The incoming seed is never used before successful block validation. -/
def storePreparationWork {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) : ℕ :=
  BinarySeedLookupTree.preparationCells (List.ofFn tables.choice.read) + 3 * coinBitBudget n K + 1

theorem storePreparationWork_bound {n K : ℕ} (tables : BinaryPRGSeedBlocks.Tables n K) :
    storePreparationWork tables ≤ 36 * coinBitBudget n K + 7 := by
  have h := BinarySeedLookupTree.preparationCells_bound (List.ofFn tables.choice.read)
  rw [List.length_ofFn] at h
  unfold storePreparationWork
  omega

noncomputable def frameSuffixEnvelope (length : ℕ) : ℕ :=
  let t := length + 1
  scalingBound t (expressionHeightBudget (16 * t) 75) +
    16 * t * (1 + 2 * expressionHeightBudget (16 * t) 76) + 14 * t + 6

theorem read_suffixBound (frame : List Bool)
    (parsed : (Σ n, BinaryPRGAccuracyRulerRequest.Request n) × List Bool)
    (h : (BinaryPRGAccuracyRulerRequest.read frame).1 = some parsed) :
    suffixBound parsed.1.2 ≤ frameSuffixEnvelope frame.length := by
  have hn := BinaryPRGSeedRequestBound.read_dimension_bound frame parsed h
  have hK := BinaryPRGAccuracyRulerRequest.read_precision_bound frame parsed h
  have hW := BinaryPRGFrameCostJoin.read_source_width frame parsed h
  let t := frame.length + 1
  have hnT : parsed.1.1 ≤ t := by dsimp [t]; omega
  have hBase : max (3 + parsed.1.2.request.source.originalInputWordWidth)
      (parsed.1.2.request.precision + 2) ≤ 16 * t := by
    apply max_le <;> dsimp [t] <;> omega
  have hNormalized : normalizedHeight parsed.1.2.request parsed.1.2.request.precision ≤
      expressionHeightBudget (16 * t) 75 := by
    unfold normalizedHeight
    simp only [BinaryPRGFrameCostJoin.expressionHeightBudget_affine]
    gcongr
  have hOutput : outputHeight parsed.1.2.request parsed.1.2.request.precision ≤
      expressionHeightBudget (16 * t) 76 := by
    unfold outputHeight
    simp only [BinaryPRGFrameCostJoin.expressionHeightBudget_affine]
    gcongr
  have hHeader : parsed.1.2.header.bytes.length ≤ 2 * (t + 1) + 1 := by
    rw [parsed.1.2.header.correct, BinaryNatFrame.encode_length]
    have hLog : binaryWordWidth parsed.1.1 ≤ t + 1 := by
      unfold binaryWordWidth
      exact Nat.add_le_add_right ((Nat.log2_le_self _).trans hnT) 1
    omega
  unfold suffixBound frameSuffixEnvelope scalingBound outputWidth
  dsimp only
  have hScale := Nat.mul_le_mul hnT (Nat.mul_le_mul_left 11000
    (Nat.pow_le_pow_left (by omega : 2 * normalizedHeight parsed.1.2.request parsed.1.2.request.precision + 2 ≤
      2 * expressionHeightBudget (16 * t) 75 + 2) 2))
  have hArray := Nat.mul_le_mul hnT (Nat.add_le_add_right hnT 1)
  have hFrame := Nat.mul_le_mul (Nat.mul_le_mul_left 16 hnT)
    (by omega : 1 + 2 * outputHeight parsed.1.2.request parsed.1.2.request.precision ≤
      1 + 2 * expressionHeightBudget (16 * t) 76)
  change _ ≤ t * (11000 * (2 * expressionHeightBudget (16 * t) 75 + 2)^2) +
    t * (t + 1) + 2 * t + 2 + 16 * t * (1 + 2 * expressionHeightBudget (16 * t) 76) + 14 * t + 6
  omega

set_option exponentiation.threshold 1024 in
theorem frameSuffixEnvelope_polynomial (length : ℕ) :
    frameSuffixEnvelope length ≤ 2^192 * (length + 1)^3 := by
  let t := length + 1
  have ht : 1 ≤ t := by dsimp [t]; omega
  have h1 : t ≤ t^3 := by simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 1 ≤ 3)
  have h2 : t^2 ≤ t^3 := Nat.pow_le_pow_right (by omega : 0 < t) (by decide : 2 ≤ 3)
  have h0 : 1 ≤ t^3 := Nat.one_le_pow 3 t ht
  unfold frameSuffixEnvelope scalingBound
  change t * (11000 * (2 * expressionHeightBudget (16 * t) 75 + 2)^2) +
    t * (t + 1) + 2 * t + 2 + 16 * t * (1 + 2 * expressionHeightBudget (16 * t) 76) + 14 * t + 6 ≤ 2^192 * t^3
  simp only [BinaryPRGFrameCostJoin.expressionHeightBudget_affine]
  norm_num only [Nat.reducePow, Nat.reduceSub, Nat.reduceMul, Nat.reduceAdd]
  ring_nf
  nlinarith only [h0, h1, h2]

end Blotto.BinaryPRGWordControllerFrameWork
