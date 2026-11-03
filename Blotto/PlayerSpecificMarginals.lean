import Blotto.LottoResourceSystem

/-! Literal player-specific zero/uniform marginal parameters. Scalar
identities are valid over any ordered field, including the later algebraic
representation. This component does not yet provide parameter recognition. -/
namespace Blotto.PlayerSpecificMarginals
set_option autoImplicit false
set_option maxHeartbeats 1500000
variable {𝕂 : Type*} [Field 𝕂] [LinearOrder 𝕂] [IsStrictOrderedRing 𝕂]

def length (v w gamma scale : 𝕂) : 𝕂 := min v (gamma*w)/scale

def probA (v w gamma : 𝕂) : 𝕂 := min 1 (v/(gamma*w))

def probB (v w gamma : 𝕂) : 𝕂 := min 1 (gamma*w/v)

theorem length_pos {v w gamma scale : 𝕂} (hv : 0<v) (hw : 0<w)
    (hg : 0<gamma) (hs : 0<scale) : 0<length v w gamma scale :=
  div_pos (lt_min hv (mul_pos hg hw)) hs

theorem probA_pos {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    0<probA v w gamma := lt_min zero_lt_one (div_pos hv (mul_pos hg hw))

theorem probB_pos {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    0<probB v w gamma := lt_min zero_lt_one (div_pos (mul_pos hg hw) hv)

omit [IsStrictOrderedRing 𝕂] in
theorem probA_le_one (v w gamma : 𝕂) : probA v w gamma≤1 := min_le_left _ _

omit [IsStrictOrderedRing 𝕂] in
theorem probB_le_one (v w gamma : 𝕂) : probB v w gamma≤1 := min_le_left _ _

theorem low_formulas {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma)
    (h : v≤gamma*w) (scale : 𝕂) :
    length v w gamma scale=v/scale ∧ probA v w gamma=v/(gamma*w) ∧ probB v w gamma=1 := by
  simp only [length,probA,probB,min_eq_left h,
    min_eq_right ((div_le_one (mul_pos hg hw)).mpr h),min_eq_left ((one_le_div hv).mpr h),and_self]

theorem high_formulas {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma)
    (h : gamma*w≤v) (scale : 𝕂) :
    length v w gamma scale=gamma*w/scale ∧ probA v w gamma=1 ∧ probB v w gamma=gamma*w/v := by
  simp only [length,probA,probB,min_eq_right h,
    min_eq_left ((one_le_div (mul_pos hg hw)).mpr h),min_eq_right ((div_le_one hv).mpr h),and_self]

theorem complementary_atoms {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    (1-probA v w gamma)*(1-probB v w gamma)=0 := by
  rcases le_total v (gamma*w) with h | h
  · rw [(low_formulas hv hw hg h 1).2.2]
    ring
  · rw [(high_formulas hv hw hg h 1).2.1]
    ring

theorem weighted_probB {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    v*probB v w gamma=min v (gamma*w) := by
  rcases le_total v (gamma*w) with h | h
  · rw [(low_formulas hv hw hg h 1).2.2,min_eq_left h,mul_one]
  · rw [(high_formulas hv hw hg h 1).2.2,min_eq_right h]
    exact mul_div_cancel₀ _ hv.ne'

theorem weighted_probA {v w gamma : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    gamma*w*probA v w gamma=min v (gamma*w) := by
  rcases le_total v (gamma*w) with h | h
  · rw [(low_formulas hv hw hg h 1).2.1,min_eq_left h]
    exact mul_div_cancel₀ _ (mul_pos hg hw).ne'
  · rw [(high_formulas hv hw hg h 1).2.1,min_eq_right h,mul_one]

theorem slopeA {v w gamma scale : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) :
    v*probB v w gamma/length v w gamma scale=scale := by
  rw [weighted_probB hv hw hg,length]
  exact div_div_cancel₀ (ne_of_gt (lt_min hv (mul_pos hg hw)))

theorem slopeB {v w gamma scale : 𝕂} (hv : 0<v) (hw : 0<w) (hg : 0<gamma) (hs : 0<scale) :
    w*probA v w gamma/length v w gamma scale=scale/gamma := by
  have h := weighted_probA hv hw hg
  have hm := ne_of_gt (lt_min hv (mul_pos hg hw))
  calc
    _ = (gamma*w*probA v w gamma)/(gamma*length v w gamma scale) := by
      field_simp [hg.ne']
    _ = min v (gamma*w)/(gamma*(min v (gamma*w)/scale)) := by rw [h,length]
    _ = scale/gamma := by field_simp [hm,hg.ne',hs.ne']

end Blotto.PlayerSpecificMarginals
