import Blotto.RationalLottoFlatProgram
import Blotto.RationalTerminalProgramLaw
import Blotto.RationalSerialIdealLaw

/-! Native resource-coordinate means identify exact global marginals.
Independent scalar averages give the midpoint law of that same native
controller, without equating different selectors' whole-allocation laws. -/

namespace Blotto.RationalLottoResourceSystem
open MeasureTheory

theorem phase_weight_mean {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) :
    (i.phase.specification i.start).decode.mean (fun s => ((i.terminalData s).resource j : ℝ) / (i.length j : ℝ)) =
      (i.initial j : ℝ) / (i.length j : ℝ) := by
  rw [WordChoiceTree.mean_div_const, i.phase_mean]

theorem terminal_weight_bounds {n : ℕ} (i : RationalLottoResourceSystem n) (s : i.PhaseResult) (j : Fin n) :
    0 ≤ ((i.terminalData s).resource j : ℝ) / (i.length j : ℝ) ∧
      ((i.terminalData s).resource j : ℝ) / (i.length j : ℝ) ≤ 1 := by
  have hL : (0 : ℝ) < i.length j := by exact_mod_cast i.length_pos j
  have hb : (0 : ℝ) ≤ (i.terminalData s).resource j ∧
      ((i.terminalData s).resource j : ℝ) ≤ (i.length j : ℝ) := by exact_mod_cast (i.terminalData s).box j
  exact ⟨div_nonneg hb.1 (le_of_lt hL), (div_le_one hL).mpr hb.2⟩

noncomputable def exactLaw {n : ℕ} (i : RationalLottoResourceSystem n) : Mixed n :=
  (i.phase.specification i.start).evalLaw (fun s => (i.terminalData s).exactLaw)

theorem exactLaw_marginal {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) :
    (marginal i.exactLaw j : Measure ℝ) =
      affineMeasure ((i.initial j : ℝ) / (i.length j : ℝ)) (uniformLaw (i.length j : ℝ)) (Measure.dirac 0) := by
  unfold exactLaw
  rw [WordChoiceTree.evalLaw_affine_marginal _ _
    (fun s => ((i.terminalData s).resource j : ℝ) / (i.length j : ℝ))
    (fun s => i.terminal_weight_bounds s j) j (uniformLaw (i.length j : ℝ)) (Measure.dirac 0)
    (fun s => (i.terminalData s).exactLaw_contract.2 j), i.phase_weight_mean]

theorem exactLaw_marginal_eq {n : ℕ} (i : RationalLottoResourceSystem n) (j : Fin n) :
    (marginal i.exactLaw j : Measure ℝ) = (marginal i.real.law j : Measure ℝ) := by
  rw [i.exactLaw_marginal, i.real.law_contract.2 j]
  rfl

theorem fixedIdealLaw_eq {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ)
    (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).idealLaw =
      (i.phase.specification i.start).evalLaw (fun s => ((i.terminalData s).program K outerBits scalarBits).idealLaw) := by
  change (i.machine K outerBits scalarBits).rationalIdealLaw (i.samplingStart K outerBits scalarBits) = _
  rw [machine, samplingStart, WordStateMachine.serial_rationalIdealLaw]
  rfl

noncomputable def midpointLaw {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) : Mixed n :=
  (i.phase.specification i.start).evalLaw (fun s => (i.terminalData s).midpointLaw K)

theorem averagedIdealLaw_eq_midpoint {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    i.averagedIdealLaw K = i.midpointLaw K := by
  calc
    _ = averagedLaw (fairBitLaw K) (fun outerBits => averagedLaw (fairBitLaw K)
        (fun scalarBits => (i.phase.specification i.start).evalLaw
          (fun s => ((i.terminalData s).program K outerBits scalarBits).idealLaw))
            (measurable_of_countable _)) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      exact averaged_fairBit_congr K _ _ (i.fixedIdealLaw_eq K outerBits)
    _ = averagedLaw (fairBitLaw K) (fun outerBits =>
        (i.phase.specification i.start).evalLaw (fun s => averagedLaw (fairBitLaw K)
          (fun scalarBits => ((i.terminalData s).program K outerBits scalarBits).idealLaw)
            (measurable_of_countable _))) (measurable_of_countable _) := by
      apply averaged_fairBit_congr
      intro outerBits
      exact WordChoiceTree.evalLaw_averaged_fairBits _ K _
    _ = _ := WordChoiceTree.evalLaw_averaged_fairBits _ K _

theorem midpointLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.phase.specification i.start).evalLaw_CDFClose
    (fun s => (i.terminalData s).midpointLaw K) (fun s => (i.terminalData s).exactLaw)
    (fun s => (i.terminalData s).midpointLaw_CDF_error K)
  intro j z
  have hj := h j z
  unfold closedCDF at hj ⊢
  change |(marginal (i.midpointLaw K) j : Measure ℝ).real _ - (marginal i.exactLaw j : Measure ℝ).real _| ≤ _ at hj
  rw [i.exactLaw_marginal_eq j] at hj
  exact hj

theorem sampleLaw_CDF_error {n : ℕ} (i : RationalLottoResourceSystem n) (K : ℕ) :
    CDFClose (i.sampleLaw K) i.real.law (5 / (2 * (2 : ℝ) ^ K)) := by
  have hc := i.sampleLaw_cap_CDF_error K
  rw [i.averagedIdealLaw_eq_midpoint K] at hc
  have h := hc.triangle (i.midpointLaw_CDF_error K)
  have hsum : 1 / (2 : ℝ) ^ K + 3 / (2 * (2 : ℝ) ^ K) = 5 / (2 * (2 : ℝ) ^ K) := by field_simp; ring
  rw [hsum] at h
  exact h

end Blotto.RationalLottoResourceSystem
