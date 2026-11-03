import Blotto.BinaryNestedParameterWork
import Blotto.BinaryNestedSpecProfile
import Blotto.BinaryPRGPreparationWork

/-! Shared semantic size predicates for actual stored factory environments and
segment fields. These certificates are proof measurements, not runtime source
objects. Primitive comparator/opcode prices follow canonical stored widths. -/

namespace Blotto.BinaryFactoryHeight
open BinaryRationalNormalization BinaryRationalEncoding BinaryExpressionCompiler BinaryStoredOverlapEnvironment
open BinarySyntaxUniformWork

def SegmentHeight {n k : ℕ} (table : Segment n k) (s : ℕ) : Prop :=
  (∀ slot, RationalHeight (value (table.weight.read slot)) s) ∧
    ∀ slot j, RationalHeight (value ((table.P.read slot).read j)) s ∧ RationalHeight (value ((table.Q.read slot).read j)) s

theorem SegmentHeight.mono {n k : ℕ} {table : Segment n k} {s t : ℕ} (h : SegmentHeight table s) (hst : s ≤ t) :
    SegmentHeight table t := ⟨fun slot => (h.1 slot).mono hst,fun slot j => ⟨(h.2 slot j).1.mono hst,(h.2 slot j).2.mono hst⟩⟩

theorem InputHeight.mono {input : BinaryNestedParameters.Input} {s t : ℕ}
    (h : BinaryNestedParameterWork.InputHeight input s) (hst : s ≤ t) : BinaryNestedParameterWork.InputHeight input t :=
  ⟨h.1.mono hst,h.2.1.mono hst,h.2.2.1.mono hst,h.2.2.2.1.mono hst,h.2.2.2.2.1.mono hst,h.2.2.2.2.2.mono hst⟩

theorem height_three {s d : ℕ} (hs : 3 ≤ s) : 3 ≤ expressionHeightBudget s d := hs.trans (expressionHeightBudget_ge_input s d)

def compareBound (s : ℕ) : ℕ := 500 * (2 + 2 * s) ^ 2
def opcodeBound (s : ℕ) : ℕ := 12000 * (2 + 2 * s) ^ 3

theorem comparator_bound (first second : SignedWord) (hC : CanonicalWord first) (hD : CanonicalWord second)
    (s : ℕ) (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s) :
    BinaryRationalArithmetic.lessEqualWork first second ≤ compareBound s := by
  have h := BinaryRationalArithmetic.lessEqualWork_bound first second
  have hf := hC.2.trans (rationalWordWidth_of_height hFirst)
  have hs := hD.2.trans (rationalWordWidth_of_height hSecond)
  have hw : BinaryRationalArithmetic.pairWidth first second + 1 ≤ 2 + 2 * s := by
    unfold BinaryRationalArithmetic.pairWidth
    have hm := max_le hf hs
    omega
  exact h.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hw 2))

theorem opcode_bound (op : RealArithmeticOp) (first second : SignedWord) (hC : CanonicalWord first) (hD : CanonicalWord second)
    (s : ℕ) (hFirst : RationalHeight (value first) s) (hSecond : RationalHeight (value second) s) :
    (BinaryRationalOpcode.applyWithWork op first second).2 ≤ opcodeBound s := by
  have h := BinaryPRGPreparationWork.operation_uniform_bound op first second (1 + 2 * s)
    (hC.2.trans (rationalWordWidth_of_height hFirst)) (hD.2.trans (rationalWordWidth_of_height hSecond))
  simpa only [opcodeBound,show 1 + 2 * s + 1 = 2 + 2 * s by omega] using h

theorem zero_height (s : ℕ) (hs : 3 ≤ s) : RationalHeight (value BinaryRationalOpcode.zero) s := by
  rw [BinaryRationalOpcode.zero_value]
  exact (constant_height .zero).mono hs

theorem one_height (s : ℕ) (hs : 3 ≤ s) : RationalHeight (value Constant.one.word) s := by
  rw [Constant.word_value]
  exact (constant_height .one).mono hs

end Blotto.BinaryFactoryHeight
