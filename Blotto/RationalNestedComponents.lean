import Blotto.RationalNestedParameters
import Blotto.RationalNestedResidual
import Blotto.RationalLotteryAssembly
import Blotto.RationalFirstProgram

/-! Native first-family and translated-uniform descriptors. Their exact law
identities and endpoint budgets supply the remaining nested branch assembly. -/

namespace Blotto.RationalNestedInput
open MeasureTheory

def familyInput (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) : RationalNestedInput :=
  i.atLength x hx0 (by linarith [i.lengths.2.2.1])

theorem familyInput_real (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v) :
    (i.familyInput x hx0 hxv).real = i.real.atLength x (by exact_mod_cast hx0)
      (by rw [← i.u_real, ← i.v_real]; exact_mod_cast (show x < i.u + i.v by linarith [i.lengths.2.2.1])) :=
  i.atLength_real x hx0 _

def familyLottery (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (K : ℕ) (outerBits : Fin K → Bool) : RationalSegmentLottery 3 9 :=
  let j := i.familyInput x hx0 hxv
  j.firstConditionalLottery hxv (j.midpointLocation K outerBits) (j.midpointLocation_bounds K outerBits)

theorem familyLottery_endpoints (i : RationalNestedInput) (x : ℚ) (hx0 : 0 < x) (hxv : x ≤ i.v)
    (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 9) :
    FullBudget (i.M : ℝ) ((i.familyLottery x hx0 hxv K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.familyLottery x hx0 hxv K outerBits).real.Q slot) :=
  (i.familyInput x hx0 hxv).firstConditionalLottery_endpoints hxv _ _ slot

def secondUniformLottery (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    RationalSegmentLottery 3 9 := (i.secondUniformInput htu hTt).segmentLottery.shiftThird i.mirrorLength

theorem secondUniformLottery_law (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t) :
    (i.secondUniformLottery htu hTt).real.law = i.real.secondUniformLaw (i.secondCase_real htu)
      (by rw [← i.mirrorLength_real]; change (i.mirrorLength : ℝ) < (i.t : ℝ); exact_mod_cast hTt) := by
  unfold secondUniformLottery
  rw [RationalSegmentLottery.shiftThird_law, RationalThreeInput.segmentLottery_real, i.secondUniformInput_real]
  have hTtR : i.real.mirrorLength < i.real.t := by
    rw [← i.mirrorLength_real]
    change (i.mirrorLength : ℝ) < (i.t : ℝ)
    exact_mod_cast hTt
  let j := i.real.secondUniformInput (i.secondCase_real htu) hTtR
  change shiftedLaw (i.mirrorLength : ℝ) j.segmentLottery.law = shiftedLaw i.real.mirrorLength j.couplingLaw
  have hl : j.segmentLottery.law = j.couplingLaw := ProbabilityMeasure.toMeasure_injective j.segmentLottery_law
  rw [hl, i.mirrorLength_real]

theorem secondUniformLottery_endpoints (i : RationalNestedInput) (htu : i.u ≤ i.t) (hTt : i.mirrorLength < i.t)
    (slot : Fin 9) :
    FullBudget (i.M : ℝ) ((i.secondUniformLottery htu hTt).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.secondUniformLottery htu hTt).real.Q slot) := by
  unfold secondUniformLottery
  rw [RationalSegmentLottery.shiftThird_real, RationalThreeInput.segmentLottery_real]
  let j := (i.secondUniformInput htu hTt).real
  have hB : j.B + (i.mirrorLength : ℝ) = (i.M : ℝ) := by
    change ((i.M - i.mirrorLength : ℚ) : ℝ) + (i.mirrorLength : ℝ) = (i.M : ℝ)
    rw [Rat.cast_sub]
    ring
  have hs : (0 : ℝ) ≤ i.mirrorLength := by exact_mod_cast le_of_lt (i.mirrorLength_bounds htu).1
  have hP := shiftThird_fullBudget hs (j.segmentLottery_endpoints.1 slot)
  have hQ := shiftThird_fullBudget hs (j.segmentLottery_endpoints.2 slot)
  rw [hB] at hP hQ
  exact ⟨hP, hQ⟩

theorem residualLottery_endpoints (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (slot : Fin 3) :
    FullBudget (i.M : ℝ) ((i.residualInput hvt htu).segmentLottery.real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.residualInput hvt htu).segmentLottery.real.Q slot) := by
  rw [RationalNestedResidual.segmentLottery_real, i.residualInput_real]
  constructor
  · change FullBudget i.real.M ((i.real.residualInput _ _).vertex (NestedResidual.edges slot).1)
    rw [← i.real.geometry_matches.2.2.2]
    exact (i.real.residualInput _ _).vertex_fullBudget (NestedResidual.edges slot).1
  · change FullBudget i.real.M ((i.real.residualInput _ _).vertex (NestedResidual.edges slot).2)
    rw [← i.real.geometry_matches.2.2.2]
    exact (i.real.residualInput _ _).vertex_fullBudget (NestedResidual.edges slot).2

end Blotto.RationalNestedInput
