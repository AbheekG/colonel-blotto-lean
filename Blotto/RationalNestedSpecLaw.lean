import Blotto.RationalNestedSpec

/-! The full rational nested descriptor's location average covers q=0/1
and either coordinate order, with the same location-only error 2^-K. -/

namespace Blotto.RationalNestedSpec
open MeasureTheory

noncomputable def locationLaw (i : RationalNestedSpec) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.law) (measurable_of_countable _)

theorem locationLaw_CDF_error (i : RationalNestedSpec) (K : ℕ) :
    CDFClose (i.locationLaw K) i.real.law (1 / (2 : ℝ) ^ K) := by
  have he0 : i.q = 0 ↔ i.real.q = 0 := by dsimp [real]; norm_cast
  have he1 : i.q = 1 ↔ i.real.q = 1 := by dsimp [real]; norm_cast
  have heA : i.a ≤ i.d ↔ i.real.a ≤ i.real.d := by dsimp [real]; norm_cast
  unfold NestedSpec.law
  by_cases hq0 : i.q = 0
  · rw [dite_eq_left (he0.mp hq0)]
    have hl : i.locationLaw K = (i.longInput hq0).real.law := by
      calc
        _ = averagedLaw (fairBitLaw K) (fun _ => (i.longInput hq0).real.law) (measurable_of_countable _) := by
          apply averaged_fairBit_congr
          intro bits
          rw [profile, dite_eq_left hq0, RationalSegmentLottery.padRight_law, RationalThreeSpec.segmentLottery_real]
          exact ProbabilityMeasure.toMeasure_injective ((i.longInput hq0).real.segmentLottery_law)
        _ = _ := averaged_fairBit_constant K _
    rw [hl, i.longInput_real]
    intro j z
    simp only [sub_self, abs_zero]
    positivity
  · rw [dite_eq_right (fun h => hq0 (he0.mpr h))]
    by_cases hq1 : i.q = 1
    · rw [dite_eq_left (he1.mp hq1)]
      have hl : i.locationLaw K = (i.shortInput hq1).real.law := by
        calc
          _ = averagedLaw (fairBitLaw K) (fun _ => (i.shortInput hq1).real.law) (measurable_of_countable _) := by
            apply averaged_fairBit_congr
            intro bits
            rw [profile, dite_eq_right hq0, dite_eq_left hq1, RationalSegmentLottery.padRight_law,
              RationalThreeSpec.segmentLottery_real]
            exact ProbabilityMeasure.toMeasure_injective ((i.shortInput hq1).real.segmentLottery_law)
          _ = _ := averaged_fairBit_constant K _
      rw [hl, i.shortInput_real]
      intro j z
      simp only [sub_self, abs_zero]
      positivity
    · rw [dite_eq_right (fun h => hq1 (he1.mpr h))]
      let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      have h := j.locationLaw_CDF_error K
      have hr := i.interiorInput_real (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
      change j.real = _ at hr
      rw [hr] at h
      by_cases had : i.a ≤ i.d
      · rw [ite_eq_left (heA.mp had)]
        have hl : i.locationLaw K = j.locationLaw K := by
          apply averaged_fairBit_congr
          intro bits
          rw [profile, dite_eq_right hq0, dite_eq_right hq1, ite_eq_left had]
        rw [hl]
        exact h
      · rw [ite_eq_right (fun ha => had (heA.mpr ha))]
        have hl : i.locationLaw K = swapLaw (j.locationLaw K) := by
          calc
            _ = averagedLaw (fairBitLaw K) (fun bits => swapLaw (j.profile K bits).real.law) (measurable_of_countable _) := by
              apply averaged_fairBit_congr
              intro bits
              rw [profile, dite_eq_right hq0, dite_eq_right hq1, ite_eq_right had,
                RationalSegmentLottery.swapFirst_law]
            _ = _ := averaged_fairBit_swap K _
        rw [hl]
        exact swapLaw_CDFClose h

end Blotto.RationalNestedSpec
