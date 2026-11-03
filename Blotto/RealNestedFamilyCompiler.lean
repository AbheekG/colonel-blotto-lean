import Blotto.RealNestedParametersCode

/-! The runtime family input uses the counted probability program. Its proof
fields are transported from the retained, exactly equal family input. -/

namespace Blotto.RealNestedParametersCode

noncomputable def atLength (i : NestedInput) (x : ℝ) (hx0 : 0 < x)
    (hx : x < i.u + i.v) : NestedInput :=
  let old := i.atLength x hx0 hx
  { old with
    q := RationalNestedParametersCode.familyProbability.realValue (environment i x)
    q_pos := by rw [familyProbability_value]; exact old.q_pos
    q_lt := by rw [familyProbability_value]; exact old.q_lt
    balance := by rw [familyProbability_value]; exact old.balance }

theorem atLength_eq (i : NestedInput) (x : ℝ) (hx0 : 0 < x)
    (hx : x < i.u + i.v) : atLength i x hx0 hx = i.atLength x hx0 hx := by
  unfold atLength
  simp only [familyProbability_value]
  rfl

end Blotto.RealNestedParametersCode
