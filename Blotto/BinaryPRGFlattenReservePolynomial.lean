import Blotto.BinaryPRGNumericalPreparationLifetime

/-! A raw-length polynomial for the conservative numerical flatten reservation. -/
namespace Blotto.BinaryPRGFlattenReservePolynomial
open BinaryPRGNumericalPreparationLifetime
set_option autoImplicit false

theorem flatten_reserve_polynomial (length : ℕ) :
    flattenListReserve length (length+2) + flattenArrayReserve length (length+2) ≤
      300000000000000*(length+4)^8 := by
  let X := length+4
  have hX : 0 < X := by dsimp [X]; omega
  have hOp : BinaryQuadraticLifetime.opcodeBound (3*(length+2)+1) ≤
      5400000*X^3 := by
    calc
      BinaryQuadraticLifetime.opcodeBound (3*(length+2)+1) =
          200000*(3*length+9)^3 := by unfold BinaryQuadraticLifetime.opcodeBound; ring
      _ ≤ 200000*(3*X)^3 :=
        Nat.mul_le_mul_left 200000 (Nat.pow_le_pow_left (by dsimp [X]; omega) 3)
      _ = 5400000*X^3 := by ring
  have hB : flattenSinglePayloadBound length (length+2) ≤ 10800000*X^4 := by
    unfold flattenSinglePayloadBound
    calc
      2*length*BinaryQuadraticLifetime.opcodeBound (3*(length+2)+1) ≤
          2*X*(5400000*X^3) := by
        apply Nat.mul_le_mul
        · exact Nat.mul_le_mul_left 2 (by dsimp [X]; omega)
        · exact hOp
      _ = 10800000*X^4 := by ring
  have hOne : 1 ≤ X^4 := Nat.one_le_pow 4 X hX
  have hB1 : flattenSinglePayloadBound length (length+2)+1 ≤ 10800001*X^4 := by
    calc
      _ ≤ 10800000*X^4+X^4 := Nat.add_le_add hB hOne
      _ = 10800001*X^4 := by ring
  have hArray : flattenArrayReserve length (length+2) ≤ 233280043200002*X^8 := by
    unfold flattenArrayReserve
    calc
      2*(flattenSinglePayloadBound length (length+2)+1)^2 ≤
          2*(10800001*X^4)^2 :=
        Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hB1 2)
      _ = 233280043200002*X^8 := by ring
  have hPower : X^4 ≤ X^8 := Nat.pow_le_pow_right hX (by omega)
  have hList : flattenListReserve length (length+2) ≤ 43200000*X^8 := by
    unfold flattenListReserve
    calc
      4*flattenSinglePayloadBound length (length+2) ≤ 4*(10800000*X^4) :=
        Nat.mul_le_mul_left 4 hB
      _ = 43200000*X^4 := by ring
      _ ≤ 43200000*X^8 := Nat.mul_le_mul_left 43200000 hPower
  change flattenListReserve length (length+2) + flattenArrayReserve length (length+2) ≤
    300000000000000*X^8
  have h := Nat.add_le_add hList hArray
  omega

end Blotto.BinaryPRGFlattenReservePolynomial
