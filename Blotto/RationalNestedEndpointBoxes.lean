import Blotto.RationalFirstConditionalPath
import Blotto.RationalNestedComponents
import Blotto.RationalLotteryBoxes

/-! Every native nested component has all endpoint coordinates inside its
original field lengths. This includes residual and translated components. -/

namespace Blotto.RationalNestedInput

theorem familyLottery_box (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 9) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.familyLottery x hx0 hxv K outerBits).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.familyLottery x hx0 hxv K outerBits).real.Q slot) :=
  (i.familyInput x hx0 hxv).firstConditionalLottery_box hxv _ _ slot

theorem secondUniformLottery_box (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (slot : Fin 9) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.secondUniformLottery htu hTt).real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.secondUniformLottery htu hTt).real.Q slot) := by
  unfold secondUniformLottery
  rw [RationalSegmentLottery.shiftThird_real, RationalThreeInput.segmentLottery_real]
  let j := (i.secondUniformInput htu hTt).real
  have hP := j.segmentLottery_box.1 slot
  have hQ := j.segmentLottery_box.2 slot
  change InBox ![(i.a : ℝ), (i.d : ℝ), ((i.t - i.mirrorLength : ℚ) : ℝ)] (j.segmentLottery.P slot) at hP
  change InBox ![(i.a : ℝ), (i.d : ℝ), ((i.t - i.mirrorLength : ℚ) : ℝ)] (j.segmentLottery.Q slot) at hQ
  rw [Rat.cast_sub] at hP hQ
  have hs : (0 : ℝ) ≤ i.mirrorLength := by exact_mod_cast le_of_lt (i.mirrorLength_bounds htu).1
  have hP' := shiftThird_inBox hs hP
  have hQ' := shiftThird_inBox hs hQ
  rw [sub_add_cancel] at hP' hQ'
  constructor
  · apply inBox_mono _ hP'
    intro coordinate
    fin_cases coordinate
    · exact le_rfl
    · exact le_rfl
    · change (i.t : ℝ) ≤ (i.c : ℝ)
      exact_mod_cast le_of_lt i.t_lt
  · apply inBox_mono _ hQ'
    intro coordinate
    fin_cases coordinate
    · exact le_rfl
    · exact le_rfl
    · change (i.t : ℝ) ≤ (i.c : ℝ)
      exact_mod_cast le_of_lt i.t_lt

theorem residualLottery_box (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (slot : Fin 3) :
    InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.residualInput hvt htu).segmentLottery.real.P slot) ∧
      InBox ![(i.a : ℝ), (i.d : ℝ), (i.c : ℝ)] ((i.residualInput hvt htu).segmentLottery.real.Q slot) := by
  rw [RationalNestedResidual.segmentLottery_real, i.residualInput_real]
  have hvtR : i.real.v < i.real.t := by
    rw [← i.v_real]; change (i.v : ℝ) < (i.t : ℝ); exact_mod_cast hvt
  have htuR : i.real.t < i.real.u := by
    rw [← i.u_real]; change (i.t : ℝ) < (i.u : ℝ); exact_mod_cast htu
  let j := i.real.residualInput hvtR htuR
  have hP := j.vertex_inBox (NestedResidual.edges slot).1
  have hQ := j.vertex_inBox (NestedResidual.edges slot).2
  have ha : j.g.a = (i.a : ℝ) := i.real.geometry_matches.1
  have hd : j.g.d = (i.d : ℝ) := i.real.geometry_matches.2.1
  have hc : j.g.c = (i.c : ℝ) := i.real.geometry_matches.2.2.1
  rw [ha, hd, hc] at hP hQ
  exact ⟨hP, hQ⟩

end Blotto.RationalNestedInput
