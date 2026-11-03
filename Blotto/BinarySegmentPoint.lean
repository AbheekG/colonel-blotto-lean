import Blotto.BinarySegmentAssembly
import Blotto.BinaryDyadicMidpoint
import Blotto.RationalLotteryBoxes
import Blotto.RationalInterpolationCode

/-! Actual stored segment endpoints and a native Boolean dyadic midpoint emit
canonical stored whole-allocation coordinates. Four verified Boolean opcodes
compute each affine coordinate; the scalar word is produced once per row.
Exact rational/real interpretation transfers every-slot budget and box proofs,
including zero-weight slots. The work/storage observers are abstract Boolean
and list-cell contracts; categorical selection and physical compilation are
separate. -/

namespace Blotto.BinarySegmentPoint
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler
open BinaryStoredOverlapEnvironment
open scoped BigOperators

def program : Syntax 3 :=
  .add (.mul (.sub (.literal .one) (.input 2)) (.input 0)) (.mul (.input 2) (.input 1))

def environment (first second scalar : SignedWord) : FixedArrayTable 3 SignedWord :=
  FixedArrayTable.ofFn ![first,second,scalar]

def interpolate (first second scalar : SignedWord) : SignedWord :=
  ((program.compile.run (environment first second scalar))).1

theorem program_source : program.rational = RationalInterpolationCode.program := rfl

theorem program_interpreted : program.compile.interpreted = RationalInterpolationCode.program :=
  program.compile_interpreted.trans program_source

theorem environment_canonical (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar) :
    ∀ j, CanonicalWord ((environment first second scalar).read j) := by
  intro j
  simp only [environment, FixedArrayTable.read_ofFn]
  fin_cases j
  · exact hFirst
  · exact hSecond
  · exact hScalar

theorem environment_refines (first second scalar : SignedWord) :
    BinaryRationalExpression.interpretedEnvironment (environment first second scalar) =
      RationalInterpolationCode.environment (value first) (value second) (value scalar) := by
  apply BinaryOverlapInputPreparation.table_ext
  intro j
  simp only [BinaryRationalExpression.interpretedEnvironment, environment,
    RationalInterpolationCode.environment, FixedArrayTable.read_ofFn]
  fin_cases j <;> rfl

theorem interpolate_canonical (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar) :
    CanonicalWord (interpolate first second scalar) :=
  program.compile.run_canonical _ (environment_canonical first second scalar hFirst hSecond hScalar)
    program.compile_canonical

theorem interpolate_value (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar) :
    value (interpolate first second scalar) = (1 - value scalar) * value first + value scalar * value second := by
  have he := program.compile_run_value (environment first second scalar)
    (fun j => (environment_canonical first second scalar hFirst hSecond hScalar j).1)
  rw [program_source, environment_refines] at he
  exact he.trans (RationalInterpolationCode.value_eq _ _ _)

def atScalar {n k : ℕ} (table : Segment n k) (slot : Fin k) (scalar : SignedWord) : FixedArrayTable n SignedWord :=
  FixedArrayTable.ofFn (fun j => interpolate ((table.P.read slot).read j) ((table.Q.read slot).read j) scalar)

def sample {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) : FixedArrayTable n SignedWord :=
  atScalar table slot (BinaryDyadicMidpoint.sample K bits)

theorem atScalar_canonical {n k : ℕ} (table : Segment n k) (slot : Fin k) (scalar : SignedWord)
    (hTable : table.Canonical) (hScalar : CanonicalWord scalar) :
    ∀ j, CanonicalWord ((atScalar table slot scalar).read j) := by
  intro j
  rw [atScalar, FixedArrayTable.read_ofFn]
  exact interpolate_canonical _ _ scalar (hTable.2.1 slot j) (hTable.2.2 slot j) hScalar

theorem sample_canonical {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool)
    (hTable : table.Canonical) : ∀ j, CanonicalWord ((sample table slot K bits).read j) :=
  atScalar_canonical table slot _ hTable (BinaryDyadicMidpoint.sample_canonical K bits)

theorem sample_value {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) (j : Fin n) :
    value ((sample table slot K bits).read j) = source.point K slot bits j := by
  rw [sample, atScalar, FixedArrayTable.read_ofFn,
    interpolate_value _ _ _ (hTable.2.1 slot j) (hTable.2.2 slot j) (BinaryDyadicMidpoint.sample_canonical K bits),
    BinaryDyadicMidpoint.sample_value, hRefines.2.1 slot j, hRefines.2.2 slot j]
  rfl

theorem sample_real {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    (fun j => (value ((sample table slot K bits).read j) : ℝ)) = source.real.dyadicPoint K slot bits := by
  rw [← source.point_real]
  funext j
  rw [sample_value table source hTable hRefines]

theorem sample_fullBudget {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source) (B : ℝ)
    (hBudget : ∀ slot, FullBudget B (source.real.P slot) ∧ FullBudget B (source.real.Q slot))
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    FullBudget B (fun j => (value ((sample table slot K bits).read j) : ℝ)) := by
  rw [sample_real table source hTable hRefines]
  exact source.real.dyadicPoint_fullBudget K hBudget slot bits

theorem sample_feasible {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source) (B : ℝ)
    (hBudget : ∀ slot, FullBudget B (source.real.P slot) ∧ FullBudget B (source.real.Q slot))
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    Feasible B (fun j => (value ((sample table slot K bits).read j) : ℝ)) :=
  fullBudget_feasible (sample_fullBudget table source hTable hRefines B hBudget slot K bits)

theorem sample_inBox {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source) (lengths : Allocation n)
    (hBox : ∀ slot, InBox lengths (source.real.P slot) ∧ InBox lengths (source.real.Q slot))
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    InBox lengths (fun j => (value ((sample table slot K bits).read j) : ℝ)) := by
  have he : (fun j => (value ((sample table slot K bits).read j) : ℝ)) =
      (fun j => (source.point K slot bits j : ℝ)) := by
    funext j
    rw [sample_value table source hTable hRefines]
  rw [he]
  exact source.point_inBox K lengths hBox slot bits

theorem interpolation_intermediates (P Q t : ℚ) (s : ℕ) (hs : 2 ≤ s)
    (hP : RationalHeight P s) (hQ : RationalHeight Q s) (ht : RationalHeight t s) :
    RationalInterpolationCode.program.AllRunHeights (RationalInterpolationCode.environment P Q t)
      (expressionHeightBudget s 3) := by
  have he : ∀ j, RationalHeight ((RationalInterpolationCode.environment P Q t).read j) s := by
    intro j
    fin_cases j
    · simpa [RationalInterpolationCode.environment, FixedArrayTable.read_ofFn] using hP
    · simpa [RationalInterpolationCode.environment, FixedArrayTable.read_ofFn] using hQ
    · simpa [RationalInterpolationCode.environment, FixedArrayTable.read_ofFn] using ht
  have h := RationalInterpolationCode.program.run_all_heights _ s he
    (RationalInterpolationCode.program.LiteralHeights_mono hs RationalInterpolationCode.literals)
  rw [RationalInterpolationCode.depth] at h
  exact h

theorem interpolate_work (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar)
    (s : ℕ) (hs : 2 ≤ s) (hP : RationalHeight (value first) s)
    (hQ : RationalHeight (value second) s) (ht : RationalHeight (value scalar) s) :
    program.compile.bitWork (environment first second scalar) ≤
      9 * BinaryRationalExpression.uniformPrice (expressionHeightBudget s 3) := by
  have he := program.compile.bitWork_bound _ (environment_canonical first second scalar hFirst hSecond hScalar)
    program.compile_canonical (expressionHeightBudget s 3) (by
      rw [program_interpreted, environment_refines]
      exact interpolation_intermediates _ _ _ s hs hP hQ ht)
  rw [program_interpreted, RationalInterpolationCode.operations] at he
  exact he

theorem interpolate_workspace (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar)
    (s : ℕ) (hs : 2 ≤ s) (hP : RationalHeight (value first) s)
    (hQ : RationalHeight (value second) s) (ht : RationalHeight (value scalar) s) :
    program.compile.primitiveWorkspace (environment first second scalar) ≤
      9 * BinaryRationalExpression.workspacePrice (expressionHeightBudget s 3) := by
  have he := program.compile.primitiveWorkspace_bound _
    (environment_canonical first second scalar hFirst hSecond hScalar)
    program.compile_canonical (expressionHeightBudget s 3) (by
      rw [program_interpreted, environment_refines]
      exact interpolation_intermediates _ _ _ s hs hP hQ ht)
  rw [program_interpreted, RationalInterpolationCode.operations] at he
  exact he

theorem interpolate_width (first second scalar : SignedWord)
    (hFirst : CanonicalWord first) (hSecond : CanonicalWord second) (hScalar : CanonicalWord scalar)
    (s : ℕ) (hs : 2 ≤ s) (hP : RationalHeight (value first) s)
    (hQ : RationalHeight (value second) s) (ht : RationalHeight (value scalar) s) :
    width (interpolate first second scalar) ≤ 1 + 2 * expressionHeightBudget s 3 := by
  have hc := interpolate_canonical first second scalar hFirst hSecond hScalar
  have he := RationalInterpolationCode.output_height _ _ _ s hs hP hQ ht
  rw [← interpolate_value first second scalar hFirst hSecond hScalar] at he
  exact hc.2.trans (rationalWordWidth_of_height he)

-- The scalar producer runs once; actual four-opcode coordinate expressions,
-- every emitted signed-word payload and the output array cells are charged.
def sampleWork {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) : ℕ :=
  (BinaryDyadicMidpoint.sampleWithWork K bits).2 +
    (∑ j : Fin n, program.compile.bitWork (environment ((table.P.read slot).read j)
      ((table.Q.read slot).read j) (BinaryDyadicMidpoint.sample K bits))) +
    2 * (∑ j : Fin n, BinaryRationalExpression.payloadWords ((sample table slot K bits).read j)) + n + 4

def sampleWithWork {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    FixedArrayTable n SignedWord × ℕ := (sample table slot K bits, sampleWork table slot K bits)

theorem sampleWithWork_state {n k : ℕ} (table : Segment n k) (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    (sampleWithWork table slot K bits).1 = sample table slot K bits := rfl

theorem sampleWork_bound {n k : ℕ} (table : Segment n k) (source : RationalSegmentLottery n k)
    (hTable : table.Canonical) (hRefines : table.Refines source) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ slot j, RationalHeight (source.P slot j) s ∧ RationalHeight (source.Q slot j) s)
    (slot : Fin k) (K : ℕ) (bits : Fin K → Bool) :
    sampleWork table slot K bits ≤ 180 * (K + 3) ^ 3 +
      9 * n * BinaryRationalExpression.uniformPrice (expressionHeightBudget (max s (K + 2)) 3) +
      2 * n * (3 + 4 * expressionHeightBudget (max s (K + 2)) 3) + n + 4 := by
  let t := BinaryDyadicMidpoint.sample K bits
  let W := max s (K + 2)
  have hW : 2 ≤ W := hs.trans (le_max_left _ _)
  have ht : RationalHeight (value t) W := by
    rw [BinaryDyadicMidpoint.sample_value]
    exact (dyadicMidpointSample_height K bits).mono (le_max_right _ _)
  have hp : ∀ j, RationalHeight (value ((table.P.read slot).read j)) W := by
    intro j
    rw [hRefines.2.1 slot j]
    exact ((hHeight slot j).1).mono (le_max_left _ _)
  have hq : ∀ j, RationalHeight (value ((table.Q.read slot).read j)) W := by
    intro j
    rw [hRefines.2.2 slot j]
    exact ((hHeight slot j).2).mono (le_max_left _ _)
  have hWork : (∑ j : Fin n, program.compile.bitWork (environment ((table.P.read slot).read j)
      ((table.Q.read slot).read j) t)) ≤ 9 * n * BinaryRationalExpression.uniformPrice (expressionHeightBudget W 3) :=
    (Finset.sum_le_sum (fun j _ => interpolate_work _ _ t (hTable.2.1 slot j) (hTable.2.2 slot j)
      (BinaryDyadicMidpoint.sample_canonical K bits) W hW (hp j) (hq j) ht)).trans_eq (by simp; ring)
  have hEach : ∀ j, BinaryRationalExpression.payloadWords ((sample table slot K bits).read j) ≤
      3 + 4 * expressionHeightBudget W 3 := by
    intro j
    have hx : width ((sample table slot K bits).read j) ≤ 1 + 2 * expressionHeightBudget W 3 := by
      rw [sample, atScalar, FixedArrayTable.read_ofFn]
      exact interpolate_width _ _ t (hTable.2.1 slot j) (hTable.2.2 slot j)
        (BinaryDyadicMidpoint.sample_canonical K bits) W hW (hp j) (hq j) ht
    have he := BinaryRationalExpression.payloadWords_bound _ _ hx
    omega
  have hPayload : (∑ j : Fin n, BinaryRationalExpression.payloadWords ((sample table slot K bits).read j)) ≤
      n * (3 + 4 * expressionHeightBudget W 3) :=
    (Finset.sum_le_sum (fun j _ => hEach j)).trans_eq (by simp)
  have hm := BinaryDyadicMidpoint.sampleWithWork_bound K bits
  unfold sampleWork
  change (BinaryDyadicMidpoint.sampleWithWork K bits).2 +
    (∑ j : Fin n, program.compile.bitWork (environment ((table.P.read slot).read j)
      ((table.Q.read slot).read j) t)) +
    2 * (∑ j : Fin n, BinaryRationalExpression.payloadWords ((sample table slot K bits).read j)) + n + 4 ≤ _
  dsimp only [W] at hWork hPayload
  nlinarith

end Blotto.BinarySegmentPoint
