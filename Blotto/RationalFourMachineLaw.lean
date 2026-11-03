import Blotto.RationalFourMachine

/-! Casewise ideal-law identities and one-cap allocation-law guarantees for
the complete ordered four-variable controller. -/

namespace Blotto.RationalFourInput
open MeasureTheory

noncomputable def fixedLaw (i : RationalFourInput) (K R : ℕ) (outerBits scalarBits : Fin K → Bool) : Mixed 4 :=
  (i.machine K outerBits scalarBits).rationalCappedLaw R (i.start K outerBits scalarBits) (i.fallback K outerBits scalarBits)

noncomputable def fixedIdealLaw (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Mixed 4 :=
  (i.machine K outerBits scalarBits).rationalIdealLaw (i.start K outerBits scalarBits)

theorem fixedIdealLaw_eq (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    i.fixedIdealLaw K outerBits scalarBits =
      if hcase : (1 - i.p) * i.ell ≤ i.w then (i.gluingDescriptor hcase).fixedIdeal K scalarBits
      else i.smallFixedIdealLaw (lt_of_not_ge hcase) K outerBits scalarBits := by
  unfold fixedIdealLaw WordStateMachine.rationalIdealLaw start
  by_cases hcase : (1 - i.p) * i.ell ≤ i.w
  · rw [dite_eq_left hcase, dite_eq_left hcase, i.gluing_specification]
    exact (i.gluingDescriptor hcase).machine_rationalIdealLaw 0 K scalarBits
  · rw [dite_eq_right hcase, dite_eq_right hcase, i.small_specification]
    rfl

theorem fixedLaw_CDF_error (i : RationalFourInput) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    CDFClose (i.fixedLaw K (3 * (80 + K)) outerBits scalarBits) (i.fixedIdealLaw K outerBits scalarBits) (1 / (2 : ℝ) ^ K) :=
  (i.machine K outerBits scalarBits).rationalCappedLaw_CDF_error 80 K (i.start K outerBits scalarBits)
    (i.machine_rank K outerBits scalarBits) (i.fallback K outerBits scalarBits)

noncomputable def midpointLaw (i : RationalFourInput) (K : ℕ) : Mixed 4 :=
  if hcase : (1 - i.p) * i.ell ≤ i.w then (i.gluingDescriptor hcase).real.dyadicLaw K
  else i.smallMidpointLaw (lt_of_not_ge hcase) K

theorem midpointLaw_CDF_error (i : RationalFourInput) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have he : (1 - i.p) * i.ell ≤ i.w ↔ (1 - i.real.p) * i.real.ell ≤ i.real.w := by
    dsimp only [real]
    norm_cast
  unfold midpointLaw FourInput.law
  by_cases hcase : (1 - i.p) * i.ell ≤ i.w
  · rw [dite_eq_left hcase, dite_eq_left (he.mp hcase)]
    have h := (i.gluingDescriptor hcase).real.dyadicLaw_CDF_error K
    rw [i.gluingDescriptor_law] at h
    exact h.mono (div_le_div_of_nonneg_right (by norm_num : (1 : ℝ) ≤ 3) (by positivity))
  · rw [dite_eq_right hcase, dite_eq_right (fun h => hcase (he.mpr h))]
    exact i.smallMidpointLaw_CDF_error _ K

theorem averaged_fixedIdeal (i : RationalFourInput) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.fixedIdealLaw K outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) =
      i.midpointLaw K := by
  unfold midpointLaw
  by_cases hcase : (1 - i.p) * i.ell ≤ i.w
  · rw [dite_eq_left hcase]
    calc
      _ = averagedLaw (fairBitLaw K) (fun _ => (i.gluingDescriptor hcase).real.dyadicLaw K) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro outerBits
        calc
          _ = averagedLaw (fairBitLaw K) (fun scalarBits => (i.gluingDescriptor hcase).fixedIdeal K scalarBits) (measurable_of_countable _) := by
            apply averaged_fairBit_congr
            intro scalarBits
            rw [i.fixedIdealLaw_eq, dite_eq_left hcase]
          _ = _ := (i.gluingDescriptor hcase).idealMidpointLaw_eq K
      _ = _ := averaged_fairBit_constant K _
  · rw [dite_eq_right hcase]
    calc
      _ = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
        (fun scalarBits => i.smallFixedIdealLaw (lt_of_not_ge hcase) K outerBits scalarBits) (measurable_of_countable _)) (measurable_of_countable _) := by
          apply averaged_fairBit_congr
          intro outerBits
          apply averaged_fairBit_congr
          intro scalarBits
          rw [i.fixedIdealLaw_eq, dite_eq_right hcase]
      _ = _ := i.averaged_smallFixedIdeal _ K

end Blotto.RationalFourInput
