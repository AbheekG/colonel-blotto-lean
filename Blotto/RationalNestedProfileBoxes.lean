import Blotto.RationalNestedEndpointBoxes
import Blotto.RationalNestedSpecProgram

/-! Every nested descriptor endpoint and every final fair-bit output is
inside the requested coordinate box, including q=0/1 and coordinate swaps. -/

namespace Blotto

namespace RationalNestedInput

theorem secondProfile_box (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ)
    (outerBits : Fin K → Bool) (slot : Fin 18) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.secondProfile htu K outerBits).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.secondProfile htu K outerBits).real.Q slot) := by
  unfold secondProfile
  dsimp only
  split_ifs with hTt
  · apply RationalSegmentLottery.binary_box
    · exact i.familyLottery_box _ _ _ K outerBits
    · exact i.secondUniformLottery_box htu hTt
  · apply RationalSegmentLottery.padRight_box
    exact i.familyLottery_box _ _ _ K outerBits

theorem thirdProfile_box (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ)
    (outerBits : Fin K → Bool) (slot : Fin 18) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.thirdProfile hvt htu K outerBits).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.thirdProfile hvt htu K outerBits).real.Q slot) := by
  unfold thirdProfile
  dsimp only
  split_ifs with hv
  · apply RationalSegmentLottery.binary_box
    · exact i.familyLottery_box i.v hv le_rfl K outerBits
    · apply RationalSegmentLottery.padRight_box
      exact i.residualLottery_box hvt htu
  · apply RationalSegmentLottery.padRight_box
    apply RationalSegmentLottery.padRight_box
    exact i.residualLottery_box hvt htu

theorem profile_box (i : RationalNestedInput) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.profile K outerBits).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  split_ifs with htv htu
  · apply RationalSegmentLottery.padRight_box
    exact i.firstConditionalLottery_box htv _ _
  · exact i.secondProfile_box htu K outerBits slot
  · exact i.thirdProfile_box _ _ K outerBits slot

theorem sample_inBox (i : RationalNestedInput) (K : ℕ) (bits : Fin (sampleBitBudget K) → Bool) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] (fun j => (i.sample K bits j : ℝ)) := by
  apply RationalSegmentLottery.flatSample_inBox
  exact i.profile_box K _

end RationalNestedInput

namespace RationalNestedSpec

theorem profile_box (i : RationalNestedSpec) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.profile K outerBits).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  split_ifs with hq0 hq1 had
  · apply RationalSegmentLottery.padRight_box
    intro edge
    rw [RationalThreeSpec.segmentLottery_real]
    exact ⟨(i.longInput hq0).real.segmentLottery_box.1 edge, (i.longInput hq0).real.segmentLottery_box.2 edge⟩
  · apply RationalSegmentLottery.padRight_box
    intro edge
    rw [RationalThreeSpec.segmentLottery_real]
    have hP := (i.shortInput hq1).real.segmentLottery_box.1 edge
    have hQ := (i.shortInput hq1).real.segmentLottery_box.2 edge
    constructor
    · apply inBox_mono _ hP
      intro coordinate
      fin_cases coordinate
      · exact le_rfl
      · exact le_rfl
      · change (i.t : ℝ) ≤ (i.c : ℝ)
        exact_mod_cast le_of_lt i.t_lt
    · apply inBox_mono _ hQ
      intro coordinate
      fin_cases coordinate
      · exact le_rfl
      · exact le_rfl
      · change (i.t : ℝ) ≤ (i.c : ℝ)
        exact_mod_cast le_of_lt i.t_lt
  · let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
    have h := j.profile_box K outerBits slot
    simpa [j, interiorInput, min_eq_left had, max_eq_right had] using h
  · have hda := le_of_lt (lt_of_not_ge had)
    let j := i.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0)) (lt_of_le_of_ne i.q_le hq1)
    have h := RationalSegmentLottery.swapFirst_box
      (j.profile K outerBits)
      ((min i.a i.d : ℚ) : ℝ) ((max i.a i.d : ℚ) : ℝ) (i.c : ℝ)
      (j.profile_box K outerBits) slot
    simpa only [max_eq_left hda, min_eq_right hda] using h

theorem sample_inBox (i : RationalNestedSpec) (K : ℕ)
    (bits : Fin (RationalNestedInput.sampleBitBudget K) → Bool) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] (fun j => (i.sample K bits j : ℝ)) := by
  apply RationalSegmentLottery.flatSample_inBox
  exact i.profile_box K _

end RationalNestedSpec
end Blotto
