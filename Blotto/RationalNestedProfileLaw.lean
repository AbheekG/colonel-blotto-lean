import Blotto.RationalNestedProfile

/-! The rational descriptor's location average has the exact branch
decomposition and location-only CDF error 2^-K in every interior case. -/

namespace Blotto.RationalNestedInput
open MeasureTheory

noncomputable def secondLocationLaw (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.secondProfile htu K bits).real.law) (measurable_of_countable _)

theorem secondLocationLaw_eq (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    i.secondLocationLaw htu K =
      if hTt : i.mirrorLength < i.t then
        binaryLaw (i.secondAlpha : ℝ) (by exact_mod_cast
          (show 0 ≤ i.secondAlpha ∧ i.secondAlpha ≤ 1 from ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩))
          (i.familyLocationLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K)
          (i.secondUniformLottery htu hTt).real.law
      else i.familyLocationLaw i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K := by
  unfold secondLocationLaw
  by_cases hTt : i.mirrorLength < i.t
  · rw [dite_eq_left hTt]
    calc
      _ = averagedLaw (fairBitLaw K) (fun bits =>
          binaryLaw (i.secondAlpha : ℝ) (by exact_mod_cast
            (show 0 ≤ i.secondAlpha ∧ i.secondAlpha ≤ 1 from ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩))
            (i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K bits).real.law
            (i.secondUniformLottery htu hTt).real.law) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro bits
        rw [secondProfile, dite_eq_left hTt, RationalSegmentLottery.binary_law]
      _ = _ := by rw [averaged_fairBit_binary, averaged_fairBit_constant]; rfl
  · rw [dite_eq_right hTt]
    apply averaged_fairBit_congr
    intro bits
    rw [secondProfile, dite_eq_right hTt, RationalSegmentLottery.padRight_law]

theorem secondLocationLaw_CDF_error (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ) :
    CDFClose (i.secondLocationLaw htu K) (i.real.secondLaw (i.secondCase_real htu)) (1 / (2 : ℝ) ^ K) := by
  have heT : i.mirrorLength < i.t ↔ i.real.mirrorLength < i.real.t := by
    rw [← i.mirrorLength_real]
    change i.mirrorLength < i.t ↔ (i.mirrorLength : ℝ) < (i.t : ℝ)
    norm_cast
  have hf := i.familyLocationLaw_CDF_error i.mirrorLength (i.mirrorLength_bounds htu).1
    (i.mirrorLength_bounds htu).2.1 K
  rw [i.secondLocationLaw_eq]
  unfold NestedInput.secondLaw
  by_cases hTt : i.mirrorLength < i.t
  · rw [dite_eq_left hTt, dite_eq_left (heT.mp hTt)]
    have h := binaryLaw_CDFClose (i.secondAlpha : ℝ) (by exact_mod_cast
      (show 0 ≤ i.secondAlpha ∧ i.secondAlpha ≤ 1 from ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩)) hf
      (show CDFClose (i.secondUniformLottery htu hTt).real.law (i.secondUniformLottery htu hTt).real.law (1 / (2 : ℝ) ^ K)
        from fun _ _ => by simp only [sub_self, abs_zero]; positivity)
    simpa only [i.secondAlpha_real, i.mirrorLength_real, i.secondUniformLottery_law htu hTt] using h
  · rw [dite_eq_right hTt, dite_eq_right (fun h => hTt (heT.mpr h))]
    simpa only [i.mirrorLength_real] using hf

noncomputable def thirdLocationLaw (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.thirdProfile hvt htu K bits).real.law) (measurable_of_countable _)

theorem thirdLocationLaw_eq (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    i.thirdLocationLaw hvt htu K =
      if hv : 0 < i.v then
        binaryLaw (i.thirdAlpha : ℝ) (by exact_mod_cast
          (show 0 ≤ i.thirdAlpha ∧ i.thirdAlpha ≤ 1 from ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩))
          (i.familyLocationLaw i.v hv le_rfl K) (i.residualInput hvt htu).segmentLottery.real.law
      else (i.residualInput hvt htu).segmentLottery.real.law := by
  unfold thirdLocationLaw
  by_cases hv : 0 < i.v
  · rw [dite_eq_left hv]
    calc
      _ = averagedLaw (fairBitLaw K) (fun bits =>
          binaryLaw (i.thirdAlpha : ℝ) (by exact_mod_cast
            (show 0 ≤ i.thirdAlpha ∧ i.thirdAlpha ≤ 1 from ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩))
            (i.familyLottery i.v hv le_rfl K bits).real.law (i.residualInput hvt htu).segmentLottery.real.law)
          (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro bits
        rw [thirdProfile, dite_eq_left hv, RationalSegmentLottery.binary_law, RationalSegmentLottery.padRight_law]
      _ = _ := by rw [averaged_fairBit_binary, averaged_fairBit_constant]; rfl
  · rw [dite_eq_right hv]
    calc
      _ = averagedLaw (fairBitLaw K) (fun _ => (i.residualInput hvt htu).segmentLottery.real.law) (measurable_of_countable _) := by
        apply averaged_fairBit_congr
        intro bits
        rw [thirdProfile, dite_eq_right hv, RationalSegmentLottery.padRight_law, RationalSegmentLottery.padRight_law]
      _ = _ := averaged_fairBit_constant K _

theorem thirdLocationLaw_CDF_error (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ) :
    CDFClose (i.thirdLocationLaw hvt htu K) (i.real.thirdLaw
      (by rw [← i.v_real]; change (i.v : ℝ) < (i.t : ℝ); exact_mod_cast hvt)
      (by rw [← i.u_real]; change (i.t : ℝ) < (i.u : ℝ); exact_mod_cast htu)) (1 / (2 : ℝ) ^ K) := by
  have heV : 0 < i.v ↔ 0 < i.real.v := by rw [← i.v_real]; norm_cast
  have hvtR : i.real.v < i.real.t := by
    rw [← i.v_real]; change (i.v : ℝ) < (i.t : ℝ); exact_mod_cast hvt
  have htuR : i.real.t < i.real.u := by
    rw [← i.u_real]; change (i.t : ℝ) < (i.u : ℝ); exact_mod_cast htu
  rw [i.thirdLocationLaw_eq]
  unfold NestedInput.thirdLaw
  have hr : (i.residualInput hvt htu).segmentLottery.real.law = (i.real.residualInput hvtR htuR).law := by
    rw [RationalNestedResidual.segmentLottery_real, i.residualInput_real, NestedResidual.segmentLottery_law]
  by_cases hv : 0 < i.v
  · rw [dite_eq_left hv, dite_eq_left (heV.mp hv)]
    have hf := i.familyLocationLaw_CDF_error i.v hv le_rfl K
    have h := binaryLaw_CDFClose (i.thirdAlpha : ℝ) (by exact_mod_cast
      (show 0 ≤ i.thirdAlpha ∧ i.thirdAlpha ≤ 1 from ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩)) hf
      (show CDFClose (i.residualInput hvt htu).segmentLottery.real.law (i.residualInput hvt htu).segmentLottery.real.law (1 / (2 : ℝ) ^ K)
        from fun _ _ => by simp only [sub_self, abs_zero]; positivity)
    simpa only [i.thirdAlpha_real, i.v_real, hr] using h
  · rw [dite_eq_right hv, dite_eq_right (fun h => hv (heV.mpr h)), hr]
    intro j z
    simp only [sub_self, abs_zero]
    positivity

noncomputable def locationLaw (i : RationalNestedInput) (K : ℕ) : Mixed 3 :=
  averagedLaw (fairBitLaw K) (fun bits => (i.profile K bits).real.law) (measurable_of_countable _)

theorem locationLaw_CDF_error (i : RationalNestedInput) (K : ℕ) :
    CDFClose (i.locationLaw K) i.real.couplingLaw (1 / (2 : ℝ) ^ K) := by
  have heV : i.t ≤ i.v ↔ i.real.t ≤ i.real.v := by
    rw [← i.v_real]; change i.t ≤ i.v ↔ (i.t : ℝ) ≤ (i.v : ℝ); norm_cast
  have heU : i.u ≤ i.t ↔ i.real.u ≤ i.real.t := by
    rw [← i.u_real]; change i.u ≤ i.t ↔ (i.u : ℝ) ≤ (i.t : ℝ); norm_cast
  unfold NestedInput.couplingLaw
  by_cases htv : i.t ≤ i.v
  · rw [dite_eq_left (heV.mp htv)]
    have hl : i.locationLaw K = i.firstLocationLaw htv K := by
      apply averaged_fairBit_congr
      intro bits
      rw [profile, dite_eq_left htv, RationalSegmentLottery.padRight_law]
    rw [hl]
    exact i.firstLocationLaw_CDF_error htv K
  · rw [dite_eq_right (fun h => htv (heV.mpr h))]
    by_cases htu : i.u ≤ i.t
    · rw [dite_eq_left (heU.mp htu)]
      have hl : i.locationLaw K = i.secondLocationLaw htu K := by
        apply averaged_fairBit_congr
        intro bits
        rw [profile, dite_eq_right htv, dite_eq_left htu]
      rw [hl]
      exact i.secondLocationLaw_CDF_error htu K
    · rw [dite_eq_right (fun h => htu (heU.mpr h))]
      have hl : i.locationLaw K = i.thirdLocationLaw (lt_of_not_ge htv) (lt_of_not_ge htu) K := by
        apply averaged_fairBit_congr
        intro bits
        rw [profile, dite_eq_right htv, dite_eq_right htu]
      rw [hl]
      exact i.thirdLocationLaw_CDF_error _ _ K

end Blotto.RationalNestedInput
