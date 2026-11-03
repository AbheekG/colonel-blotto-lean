import Blotto.RationalFourGluingDescriptor
import Blotto.RationalSegmentFlat

/-! Native bounded fair-bit sampling of the gluing descriptor. Inactive
slots retain the fixed feasible budget row; no coordinate-box claim is made
for those artificial zero-weight endpoints. -/

namespace Blotto.RationalFourInput
open MeasureTheory

def gluingSampleBitBudget (K : ℕ) : ℕ := 3 * (80 + K) + K

theorem gluingSampleBitBudget_eq (K : ℕ) : gluingSampleBitBudget K = 4 * K + 240 := by
  unfold gluingSampleBitBudget
  omega

def gluingSample (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ)
    (bits : Fin (gluingSampleBitBudget K) → Bool) : Fin 4 → ℚ :=
  (i.gluingDescriptor hcase).flatSample 0 (3 * (80 + K)) K bits

noncomputable def gluingSampleLaw (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) : Mixed 4 :=
  (i.gluingDescriptor hcase).flatLaw 0 (3 * (80 + K)) K

theorem gluingSample_fullBudget (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ)
    (bits : Fin (gluingSampleBitBudget K) → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.gluingSample hcase K bits j : ℝ)) :=
  (i.gluingDescriptor hcase).flatSample_fullBudget 0 _ K (i.gluingDescriptor_endpoints hcase) bits

theorem gluingSampleLaw_actual (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) :
    i.gluingSampleLaw hcase K = (fairBitLaw (gluingSampleBitBudget K)).map
      (fun bits j => (i.gluingSample hcase K bits j : ℝ)) := rfl

theorem gluingSampleLaw_CDF_error (i : RationalFourInput) (hcase : (1 - i.p) * i.ell ≤ i.w) (K : ℕ) :
    CDFClose (i.gluingSampleLaw hcase K) (i.real.gluingCaseLaw (i.gluingCase_real hcase)) (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.gluingDescriptor hcase).flatLaw_CDF_error 0 K
  rw [i.gluingDescriptor_law] at h
  exact h

end Blotto.RationalFourInput
