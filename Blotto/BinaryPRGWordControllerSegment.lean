import Blotto.BinaryPRGWordControllerDataCategorical
import Blotto.BinaryPRGWordControllerWindow
import Blotto.BinaryStoredSegmentProgram
import Blotto.BinaryDirectDyadicMidpoint

/-! A complete retained segment draw uses the whole Boolean seed Store and an
absolute Boolean counter. Selected interpolation executes the quadratic data
backend; annotations are erased from the data path. All original stored bytes,
exhaustion and absolute positions are retained. The selected expression price
is source-derived; factory/array/physical-space composition is separate. -/

namespace Blotto.BinaryPRGWordControllerSegment
open BinarySeedLookupTree BinaryRationalNormalization BinaryRationalEncoding
open BinaryStoredOverlapEnvironment BinaryRationalExpression
open scoped BigOperators

def interpolate (first second scalar : SignedWord) : SignedWord :=
  BinaryQuadraticData.expression (BinarySegmentPoint.environment first second scalar)
    BinarySegmentPoint.program.compile

theorem interpolate_state (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second)
    (hScalar : CanonicalWord scalar) :
    interpolate first second scalar = BinarySegmentPoint.interpolate first second scalar :=
  BinaryQuadraticData.expression_state _ _
    (fun j => (BinarySegmentPoint.environment_canonical first second scalar hFirst hSecond hScalar j).1)
    (BinarySegmentPoint.program.compile.canonicalLiterals_valid BinarySegmentPoint.program.compile_canonical)

def point {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    FixedArrayTable n SignedWord :=
  let scalar := BinaryDirectDyadicMidpoint.sample (List.ofFn bits)
  FixedArrayTable.ofFn (fun j => interpolate ((table.P.read slot).read j) ((table.Q.read slot).read j) scalar)

theorem point_state {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    point table slot K bits = BinarySegmentPoint.sample table slot K bits := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [point,BinarySegmentPoint.sample,BinarySegmentPoint.atScalar,FixedArrayTable.read_ofFn,
    BinaryDirectDyadicMidpoint.sample_ofFn]
  exact interpolate_state _ _ _ (hC.2.1 slot j) (hC.2.2 slot j)
    (BinaryDyadicMidpoint.sample_canonical K bits)

def pointExpressionWork {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  ∑ j : Fin n, (BinaryQuadraticExpression.run
    (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j)
      (BinaryDyadicMidpoint.sample K bits)) BinarySegmentPoint.program.compile).2

theorem pointExpressionWork_bound {n k : ℕ} (table : Segment n k) (hC : table.Canonical)
    (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ slot j, RationalHeight (value ((table.P.read slot).read j)) s ∧
      RationalHeight (value ((table.Q.read slot).read j)) s)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    pointExpressionWork table slot K bits ≤
      9 * n * BinaryQuadraticExpression.uniformPrice (expressionHeightBudget (max s (K + 2)) 3) := by
  let W := max s (K + 2)
  have hW : 2 ≤ W := hs.trans (le_max_left _ _)
  have ht : RationalHeight (value (BinaryDyadicMidpoint.sample K bits)) W := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right _ _)
  have hEach : ∀ j : Fin n,
      (BinaryQuadraticExpression.run
        (BinarySegmentPoint.environment ((table.P.read slot).read j) ((table.Q.read slot).read j)
          (BinaryDyadicMidpoint.sample K bits)) BinarySegmentPoint.program.compile).2 ≤
      9 * BinaryQuadraticExpression.uniformPrice (expressionHeightBudget W 3) := by
    intro j
    have h := BinaryQuadraticExpression.run_work_bound BinarySegmentPoint.program.compile _
      (BinarySegmentPoint.environment_canonical _ _ _ (hC.2.1 slot j) (hC.2.2 slot j)
        (BinaryDyadicMidpoint.sample_canonical K bits)) BinarySegmentPoint.program.compile_canonical
      (expressionHeightBudget W 3) (by
        rw [BinarySegmentPoint.program_interpreted,BinarySegmentPoint.environment_refines]
        exact BinarySegmentPoint.interpolation_intermediates _ _ _ W hW
          ((hHeight slot j).1.mono (le_max_left _ _))
          ((hHeight slot j).2.mono (le_max_left _ _)) ht)
    rw [BinarySegmentPoint.program_interpreted,RationalInterpolationCode.operations] at h
    exact h
  exact (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp; ring)

abbrev Result (store : Store) (n : ℕ) := Option (FixedArrayTable n SignedWord) × FixedBinaryWord store.width

def run {n k : ℕ} (store : Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) : Result store n :=
  let selected := BinaryPRGWordControllerDataCategorical.run store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  (selected.1.map (fun slot => point prepared.table slot K scalar),selected.2)

def decoded {n : ℕ} (store : Store) (result : Result store n) : Option (FixedArrayTable n SignedWord) × ℕ :=
  (result.1,result.2.value)

theorem run_state {n k : ℕ} (store : Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    decoded store (run store prepared fallback K scalar pc hp) =
      prepared.runIndexed fallback K store.cap.value scalar
        (BinaryWordIndexCoinController.reader store) pc.value hp := by
  unfold run BinaryStoredSegmentProgram.Prepared.runIndexed BinaryStoredSegmentProgram.Prepared.selectIndexed
  have h := BinaryPRGWordControllerCategorical.run_state store fallback
    (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative) pc hp
  simp only [BinaryPRGWordControllerCategorical.decoded,
    BinaryPRGWordControllerDataCategorical.run_erasure] at h
  have hm := congrArg (fun result : Option (Fin k) × ℕ =>
    (result.1.map (fun slot => BinarySegmentPoint.sample prepared.table slot K scalar),result.2)) h
  simpa only [decoded,point_state prepared.table prepared.canonical] using hm

theorem run_position {n k : ℕ} (store : Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value) :
    pc.value ≤ (run store prepared fallback K scalar pc hp).2.value ∧
      (run store prepared fallback K scalar pc hp).2.value ≤ store.cap.value := by
  unfold run
  dsimp only
  rw [← BinaryPRGWordControllerDataCategorical.run_erasure]
  exact BinaryPRGWordControllerCategorical.run_position_bounds store fallback _ pc hp

theorem run_offset {n k : ℕ} (store : Store) (prepared : BinaryStoredSegmentProgram.Prepared n k)
    (fallback : Fin k) (K : ℕ) (scalar : Fin K → Bool)
    (base M : ℕ) (hSize : store.cap.value = base + M) (localBits : Fin M → Bool)
    (hBits : ∀ index : Fin M, localBits index =
      BinaryWordIndexCoinController.reader store ⟨base + index.val,by rw [hSize]; omega⟩)
    (pc : FixedBinaryWord store.width) (hp : pc.value ≤ store.cap.value)
    (localPos : ℕ) (hlp : localPos ≤ M) (hPos : pc.value = base + localPos) :
    decoded store (run store prepared fallback K scalar pc hp) =
      WordStateMachine.offsetConsumed base (prepared.runIndexed fallback K M scalar localBits localPos hlp) := by
  rw [run_state]
  have h := BinaryPRGWordControllerWindow.categorical_offset fallback store.cap.value M base hSize
    (BinaryWordIndexCoinController.reader store) localBits hBits
    (.remaining (NativeBinarySegmentSampler.weights prepared.table prepared.canonical prepared.nonnegative))
    pc.value localPos hp hlp hPos
  exact congrArg (fun result : Option (Fin k) × ℕ =>
    (result.1.map (fun slot => BinarySegmentPoint.sample prepared.table slot K scalar),result.2)) h

end Blotto.BinaryPRGWordControllerSegment
