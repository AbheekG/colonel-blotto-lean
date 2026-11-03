import Blotto.PlayerSpecificAlgebraicNestedInteriorDraw

/-! The fixed-depth nested arithmetic bound is linear in the raw input
coefficient height and scalar precision, with one absolute constant. -/
namespace Blotto.PlayerSpecificAlgebraicNestedInteriorLinear
open PlayerSpecificAlgebraicHeightEnvelope
set_option autoImplicit false

def coefficient : ℕ := (PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3 *
  (4*((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35*
    ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^18+4))+10)

theorem base_linear (A T K S : ℕ) (h : S+1 ≤ A*(T+1)) : S+K+4 ≤ (A+4)*(T+K+4) := by
  have hn := Nat.zero_le (A*K)
  nlinarith only [h,hn,Nat.zero_le T,Nat.zero_le K,Nat.zero_le A]

theorem profile_linear (T K : ℕ) : PlayerSpecificAlgebraicNestedInteriorSizes.height T K+1 ≤
    ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35*
      ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^18+4))*(T+K+4) := by
  have hi := iterate_bound 18 T
  have hb := base_linear _ T K _ hi
  have hm := iterate_bound 35 (iterate 18 T+K+3)
  change iterate 35 (iterate 9 (iterate 9 T)+K+3)+1 ≤ _
  rw [PlayerSpecificAlgebraicThreeEnvironmentSizes.iterate_add]
  exact hm.trans (by simpa only [mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^35) hb)

theorem height_linear (T K : ℕ) : PlayerSpecificAlgebraicNestedInteriorDraw.height T K+1 ≤ coefficient*(T+K+1) := by
  have hi := profile_linear T K
  have hm := PlayerSpecificAlgebraicNestedFirstDrawSizes.linear_profile _ T K _ hi
  have ho := iterate_bound 3 (PlayerSpecificAlgebraicNestedInteriorSizes.height T K+2*K+6)
  exact ho.trans (by simpa only [coefficient,mul_assoc] using
    Nat.mul_le_mul_left ((PlayerSpecificAlgebraicHeightEnvelope.coefficient+1)^3) hm)

end Blotto.PlayerSpecificAlgebraicNestedInteriorLinear
