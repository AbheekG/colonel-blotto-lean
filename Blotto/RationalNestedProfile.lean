import Blotto.RationalNestedLocationLaw

/-! Every ordered interior nested case compiles, at a fixed outer fair block,
to one constant-size rational segment table. Zero-weight padding retains
feasible endpoints. All component choices can consequently share one cap. -/

namespace Blotto.RationalNestedInput
open MeasureTheory

def secondProfile (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ)
    (outerBits : Fin K → Bool) : RationalSegmentLottery 3 18 :=
  let f := i.familyLottery i.mirrorLength (i.mirrorLength_bounds htu).1 (i.mirrorLength_bounds htu).2.1 K outerBits
  if hTt : i.mirrorLength < i.t then
    RationalSegmentLottery.binary i.secondAlpha
      ⟨le_of_lt (i.secondAlpha_bounds htu).1, (i.secondAlpha_bounds htu).2⟩ f (i.secondUniformLottery htu hTt)
  else f.padRight 9 0

def thirdProfile (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ)
    (outerBits : Fin K → Bool) : RationalSegmentLottery 3 18 :=
  let r := (i.residualInput hvt htu).segmentLottery.padRight 6 0
  if hv : 0 < i.v then
    RationalSegmentLottery.binary i.thirdAlpha
      ⟨le_of_lt (i.thirdAlpha_bounds hv hvt).1, le_of_lt (i.thirdAlpha_bounds hv hvt).2⟩
      (i.familyLottery i.v hv le_rfl K outerBits) r
  else r.padRight 9 0

def profile (i : RationalNestedInput) (K : ℕ) (outerBits : Fin K → Bool) : RationalSegmentLottery 3 18 :=
  if htv : i.t ≤ i.v then
    (i.firstConditionalLottery htv (i.midpointLocation K outerBits) (i.midpointLocation_bounds K outerBits)).padRight 9 0
  else if htu : i.u ≤ i.t then i.secondProfile htu K outerBits
  else i.thirdProfile (lt_of_not_ge htv) (lt_of_not_ge htu) K outerBits

theorem secondProfile_endpoints (i : RationalNestedInput) (htu : i.u ≤ i.t) (K : ℕ)
    (outerBits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (i.M : ℝ) ((i.secondProfile htu K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.secondProfile htu K outerBits).real.Q slot) := by
  unfold secondProfile
  dsimp only
  split_ifs with hTt
  · apply RationalSegmentLottery.binary_endpoints
    · exact i.familyLottery_endpoints _ _ _ K outerBits
    · exact i.secondUniformLottery_endpoints htu hTt
  · apply RationalSegmentLottery.padRight_endpoints
    exact i.familyLottery_endpoints _ _ _ K outerBits

theorem thirdProfile_endpoints (i : RationalNestedInput) (hvt : i.v < i.t) (htu : i.t < i.u) (K : ℕ)
    (outerBits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (i.M : ℝ) ((i.thirdProfile hvt htu K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.thirdProfile hvt htu K outerBits).real.Q slot) := by
  unfold thirdProfile
  dsimp only
  split_ifs with hv
  · apply RationalSegmentLottery.binary_endpoints
    · exact i.familyLottery_endpoints i.v hv le_rfl K outerBits
    · apply RationalSegmentLottery.padRight_endpoints
      exact i.residualLottery_endpoints hvt htu
  · apply RationalSegmentLottery.padRight_endpoints
    apply RationalSegmentLottery.padRight_endpoints
    exact i.residualLottery_endpoints hvt htu

theorem profile_endpoints (i : RationalNestedInput) (K : ℕ) (outerBits : Fin K → Bool) (slot : Fin 18) :
    FullBudget (i.M : ℝ) ((i.profile K outerBits).real.P slot) ∧
      FullBudget (i.M : ℝ) ((i.profile K outerBits).real.Q slot) := by
  unfold profile
  split_ifs with htv htu
  · apply RationalSegmentLottery.padRight_endpoints
    exact i.firstConditionalLottery_endpoints htv _ _
  · exact i.secondProfile_endpoints htu K outerBits slot
  · exact i.thirdProfile_endpoints _ _ K outerBits slot

end Blotto.RationalNestedInput
