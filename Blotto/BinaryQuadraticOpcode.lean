import Blotto.BinaryQuadraticNormalization
import Blotto.RationalCostModel

/-! All six rational opcodes use the quadratic Boolean normalizer after the
existing verified Boolean raw arithmetic. Valid operands give exactly the old
canonical output bytes and rational value. The derived primitive work realizes
44000 times the named schoolbook size profile; no caller price oracle is used.
Annotations are erasable, and full interpreter/control/lifetime composition
and the sharper fast-Rat realization remain separate. -/

namespace Blotto.BinaryQuadraticOpcode
open BinaryRationalNormalization BinaryRationalOpcode

def applyWithWork (op : RealArithmeticOp) (first second : SignedWord) : SignedWord × ℕ :=
  let result := BinaryQuadraticNormalization.canonicalizeWithWork (rawApply op first second)
  (result.1,rawApplyWork op first second+result.2)

theorem applyWithWork_state (op : RealArithmeticOp) (first second : SignedWord)
    (ha : Valid first) (hb : Valid second) :
    (applyWithWork op first second).1 = BinaryRationalOpcode.apply op first second := by
  unfold applyWithWork BinaryRationalOpcode.apply
  exact BinaryQuadraticNormalization.canonicalizeWithWork_state _ (rawApply_valid op first second ha hb)

theorem applyWithWork_bound (op : RealArithmeticOp) (first second : SignedWord) :
    (applyWithWork op first second).2 ≤ 11000 * (BinaryRationalArithmetic.pairWidth first second+1)^2 := by
  have hr := rawApplyWork_bound op first second
  have hc := BinaryQuadraticNormalization.canonicalizeWithWork_bound (rawApply op first second)
  have hw := rawApply_width op first second
  have hWidth : width (rawApply op first second)+1 ≤ 4*(BinaryRationalArithmetic.pairWidth first second+1) := by omega
  have hp := hc.trans (Nat.mul_le_mul_left 600 (Nat.pow_le_pow_left hWidth 2))
  unfold applyWithWork
  dsimp only
  nlinarith

theorem valid_width_positive (word : SignedWord) (h : Valid word) : 1 ≤ width word := by
  have hd := BinaryBorrowWord.littleValue_bounds word.denominator
  have hw : word.denominator.length ≤ width word := Nat.le_max_right _ _
  by_contra hn
  have hz : word.denominator.length = 0 := by omega
  rw [hz] at hd
  change 0 < BinaryBigEndian.littleValue word.denominator at h
  norm_num at hd
  omega

theorem applyWithWork_schoolbook (op : RealArithmeticOp) (first second : SignedWord)
    (ha : Valid first) (_hb : Valid second) :
    (applyWithWork op first second).2 ≤ 44000 *
      RationalCostModel.schoolbook.rat (BinaryRationalArithmetic.pairWidth first second) := by
  have h := applyWithWork_bound op first second
  have hp := valid_width_positive first ha
  have hw : width first ≤ BinaryRationalArithmetic.pairWidth first second := Nat.le_max_left _ _
  simp only [RationalCostModel.schoolbook]
  nlinarith

theorem applyWithWork_contract (op : RealArithmeticOp) (first second : SignedWord)
    (ha : Valid first) (hb : Valid second) :
    (applyWithWork op first second).1 = BinaryRationalOpcode.apply op first second ∧
      value (applyWithWork op first second).1 = op.applyRat (value first) (value second) ∧
      BinaryRationalEncoding.CanonicalWord (applyWithWork op first second).1 ∧
      (applyWithWork op first second).2 ≤ 44000 *
        RationalCostModel.schoolbook.rat (BinaryRationalArithmetic.pairWidth first second) := by
  have hs := applyWithWork_state op first second ha hb
  refine ⟨hs,?_,?_,applyWithWork_schoolbook op first second ha hb⟩
  · rw [hs]
    exact apply_value op first second ha hb
  · rw [hs]
    refine ⟨apply_valid op first second ha hb,?_⟩
    have hw := apply_width op first second ha hb
    rw [← apply_value op first second ha hb] at hw
    exact hw

end Blotto.BinaryQuadraticOpcode
