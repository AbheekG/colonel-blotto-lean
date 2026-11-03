import Blotto.RationalFourSmallMachine
import Blotto.RationalMachineIdealTransport

/-! Whole-law identity of the native root mixture at fixed scalar blocks,
and exact averaging to the verified atom-conditioning midpoint law. -/

namespace Blotto.RationalFourInput
open MeasureTheory

noncomputable def smallFixedLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K R : ℕ)
    (outerBits scalarBits : Fin K → Bool) : Mixed 4 :=
  (i.smallMachine hcase K outerBits scalarBits).rationalCappedLaw R .start (i.smallFallback hcase K outerBits scalarBits)

noncomputable def smallFixedIdealLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) : Mixed 4 :=
  (i.smallMachine hcase K outerBits scalarBits).rationalIdealLaw .start

theorem smallFixedIdealLaw_eq (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    i.smallFixedIdealLaw hcase K outerBits scalarBits =
      binaryLaw (i.p : ℝ) (by exact_mod_cast (show 0 ≤ i.p ∧ i.p ≤ 1 from ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩))
        ((i.smallUniformLottery hcase).fixedIdeal K scalarBits)
        (((i.reflectedResourceSystem hcase).fixedIdealLaw K outerBits scalarBits).map
          (RationalAffineAllocation.reflectAppend i.originalLengths).real.value) := by
  unfold smallFixedIdealLaw smallMachine
  rw [binaryMachine_rationalIdealLaw, uniformMachine, RationalSegmentLottery.machine_rationalIdealLaw,
    reflectedMachine, WordStateMachine.rationalIdealLaw_mapped]
  have hp : i.smallWords.rational = i.p := ProbabilityWords.ofRat_rational i.p ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩
  simp only [hp]
  rfl

theorem smallFixedLaw_CDF_error (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    CDFClose (i.smallFixedLaw hcase K (3 * (20 + K)) outerBits scalarBits)
      (i.smallFixedIdealLaw hcase K outerBits scalarBits) (1 / (2 : ℝ) ^ K) :=
  (i.smallMachine hcase K outerBits scalarBits).rationalCappedLaw_CDF_error 20 K .start
    (i.smallMachine_rank hcase K outerBits scalarBits) (i.smallFallback hcase K outerBits scalarBits)

noncomputable def reflectedOuterIdealLaw (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell)
    (K : ℕ) (outerBits : Fin K → Bool) : Mixed 4 :=
  (((i.reflectedResourceSystem hcase).phase.specification (i.reflectedResourceSystem hcase).start).evalLaw
    (fun s => (((i.reflectedResourceSystem hcase).terminalData s).profile K outerBits).real.dyadicLaw K)).map
      (RationalAffineAllocation.reflectAppend i.originalLengths).real.value

theorem averaged_smallFixedIdeal_inner (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ)
    (outerBits : Fin K → Bool) :
    averagedLaw (fairBitLaw K) (fun scalarBits => i.smallFixedIdealLaw hcase K outerBits scalarBits) (measurable_of_countable _) =
      binaryLaw (i.p : ℝ) (by exact_mod_cast (show 0 ≤ i.p ∧ i.p ≤ 1 from ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩))
        (i.uniformMidpointLaw hcase K)
        (i.reflectedOuterIdealLaw hcase K outerBits) := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun scalarBits =>
        binaryLaw (i.p : ℝ) (by exact_mod_cast (show 0 ≤ i.p ∧ i.p ≤ 1 from ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩))
          ((i.smallUniformLottery hcase).fixedIdeal K scalarBits)
          (((i.reflectedResourceSystem hcase).fixedIdealLaw K outerBits scalarBits).map
            (RationalAffineAllocation.reflectAppend i.originalLengths).real.value)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      exact i.smallFixedIdealLaw_eq hcase K outerBits
    _ = _ := by
      unfold reflectedOuterIdealLaw
      rw [averaged_fairBit_binary, averaged_fairBit_affine,
        (i.reflectedResourceSystem hcase).averaged_fixedIdeal_inner K outerBits]
      have hu := (i.smallUniformLottery hcase).idealMidpointLaw_eq K
      rw [show averagedLaw (fairBitLaw K) (fun scalarBits => (i.smallUniformLottery hcase).fixedIdeal K scalarBits)
        (measurable_of_countable _) = i.uniformMidpointLaw hcase K from hu]

theorem averaged_smallFixedIdeal (i : RationalFourInput) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) :
    averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
      (fun scalarBits => i.smallFixedIdealLaw hcase K outerBits scalarBits) (measurable_of_countable _))
      (measurable_of_countable _) = i.smallMidpointLaw hcase K := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun outerBits =>
        binaryLaw (i.p : ℝ) (by exact_mod_cast (show 0 ≤ i.p ∧ i.p ≤ 1 from ⟨le_of_lt i.p_pos, le_of_lt i.p_lt⟩))
          (i.uniformMidpointLaw hcase K)
          (i.reflectedOuterIdealLaw hcase K outerBits)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      exact i.averaged_smallFixedIdeal_inner hcase K
    _ = _ := by
      unfold reflectedOuterIdealLaw
      rw [averaged_fairBit_binary, averaged_fairBit_constant, averaged_fairBit_affine,
        WordChoiceTree.evalLaw_averaged_fairBits]
      rfl

end Blotto.RationalFourInput
