import Blotto.BinaryThreeSpecCompiler
import Blotto.RationalThreeSpecHeight

/-! Explicit comparison, ordered-input and stored-coordinate-swap prices for
the actual Boolean three-spec compiler. This supplies a complete descriptor
work allowance while physical heap and controller composition remain separate. -/

namespace Blotto.BinaryThreeSpecCompiler
open BinaryRationalNormalization BinaryRationalEncoding
open scoped BigOperators

def swapPayload (segment : BinaryStoredOverlapEnvironment.Segment 3 9) : ℕ :=
  (∑ slot : Fin 9, ∑ j : Fin 3, BinaryRationalExpression.payloadWords ((segment.P.read slot).read j)) +
    (∑ slot : Fin 9, ∑ j : Fin 3, BinaryRationalExpression.payloadWords ((segment.Q.read slot).read j))

def descriptorWork (input : BinaryThreeInputCompiler.Input) : ℕ :=
  2 * BinaryRationalArithmetic.lessEqualWork input.a input.d + 20 +
    BinaryThreeInputCompiler.descriptorWork (ordered input) +
    if BinaryRationalArithmetic.lessEqual input.a input.d then 0 else
      2 * swapPayload (BinaryThreeInputCompiler.descriptor (ordered input)) + 200

theorem descriptorWork_bound (input : BinaryThreeInputCompiler.Input) (source : RationalThreeSpec)
    (hC : input.Canonical) (hR : Refines input source) (s : ℕ) (hs : 2 ≤ s)
    (hHeight : ∀ j, RationalHeight ((RationalThreeSpecCode.environment source).read j) s) :
    descriptorWork input ≤ BinaryThreeInputCompiler.workBound s + 1000 * (2*s+2)^2 +
      108 * (4*expressionHeightBudget s 4+3) + 220 := by
  have hA : RationalHeight (value input.a) s := by
    rw [hR.2.1]
    have he := hHeight (1 : Fin 5)
    change RationalHeight source.a s at he
    exact he
  have hD : RationalHeight (value input.d) s := by
    rw [hR.2.2.1]
    have he := hHeight (2 : Fin 5)
    change RationalHeight source.d s at he
    exact he
  have hWA := hC.2.1.2.trans (rationalWordWidth_of_height hA)
  have hWD := hC.2.2.1.2.trans (rationalWordWidth_of_height hD)
  have hCmp := BinaryRationalArithmetic.lessEqualWork_bound input.a input.d
  have hPW : BinaryRationalArithmetic.pairWidth input.a input.d+1 ≤ 2*s+2 := by
    unfold BinaryRationalArithmetic.pairWidth
    omega
  have hCmp' := hCmp.trans (Nat.mul_le_mul_left 500 (Nat.pow_le_pow_left hPW 2))
  have hOrdered := ordered_refines input source hC hR
  have hOC := ordered_canonical input hC
  have hOH := RationalThreeSpecCode.ordered_environment_height source s hHeight
  have hRun := BinaryThreeInputCompiler.descriptorWork_bound (ordered input) source.orderedInput hOC hOrdered s hs hOH
  have hRef := BinaryThreeInputCompiler.descriptor_refines (ordered input) source.orderedInput hOC hOrdered
  have hCan := BinaryThreeInputCompiler.descriptor_canonical (ordered input) hOC
  have hEndpoint := RationalThreeInputCode.segment_endpoint_heights source.orderedInput
  have hP : ∀ slot j, BinaryRationalExpression.payloadWords
      (((BinaryThreeInputCompiler.descriptor (ordered input)).P.read slot).read j) ≤ 4*expressionHeightBudget s 4+3 := by
    intro slot j
    have hh := (hEndpoint slot j s hs hOH).1
    rw [← hRef.2.1 slot j] at hh
    have hw := (hCan.2.1 slot j).2.trans (rationalWordWidth_of_height hh)
    have hp := BinaryRationalExpression.payloadWords_bound _ _ hw
    omega
  have hQ : ∀ slot j, BinaryRationalExpression.payloadWords
      (((BinaryThreeInputCompiler.descriptor (ordered input)).Q.read slot).read j) ≤ 4*expressionHeightBudget s 4+3 := by
    intro slot j
    have hh := (hEndpoint slot j s hs hOH).2
    rw [← hRef.2.2 slot j] at hh
    have hw := (hCan.2.2 slot j).2.trans (rationalWordWidth_of_height hh)
    have hp := BinaryRationalExpression.payloadWords_bound _ _ hw
    omega
  have hpSum : (∑ slot : Fin 9, ∑ j : Fin 3, BinaryRationalExpression.payloadWords
      (((BinaryThreeInputCompiler.descriptor (ordered input)).P.read slot).read j)) ≤
      27*(4*expressionHeightBudget s 4+3) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hP slot j))).trans_eq (by simp; ring)
  have hqSum : (∑ slot : Fin 9, ∑ j : Fin 3, BinaryRationalExpression.payloadWords
      (((BinaryThreeInputCompiler.descriptor (ordered input)).Q.read slot).read j)) ≤
      27*(4*expressionHeightBudget s 4+3) :=
    (Finset.sum_le_sum (fun slot _ => Finset.sum_le_sum (fun j _ => hQ slot j))).trans_eq (by simp; ring)
  unfold descriptorWork swapPayload
  split <;> omega

end Blotto.BinaryThreeSpecCompiler
