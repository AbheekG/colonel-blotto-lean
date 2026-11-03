import Blotto.RealChoiceWordBridge

/-! Whole-law and leaf-contract preservation when a rational word controller
is driven by exact continuous threshold inputs instead of fair-bit digits. -/

namespace Blotto
open MeasureTheory

namespace WordChoiceTree

theorem realChoice_idealLaw {α : Type*} [MeasurableSpace α] (T : WordChoiceTree α) :
    T.realChoice.idealLaw = T.decode.idealLaw := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  have he : (T.realChoice.idealLaw : Measure α).real A = (T.decode.idealLaw : Measure α).real A := by
    rw [RealChoiceTree.idealLaw_real_event _ A hA, T.realChoice_mean,
      AdaptiveChoiceTree.idealLaw_real_event _ A hA]
  have h := congrArg ENNReal.ofReal he
  rw [ofReal_measureReal (measure_ne_top _ _), ofReal_measureReal (measure_ne_top _ _)] at h
  exact h

end WordChoiceTree

namespace WordStateMachine

theorem realMachine_output_law {S α : Type*} [MeasurableSpace α] (m : WordStateMachine S α)
    (C : ℕ) (s : S) (fallback : α) (hC : m.rank s ≤ C) :
    Measure.map (m.realMachine.output C s fallback) (RealUniformInputs.law C : Measure (Fin C → ℝ)) =
      ((m.specification s).decode.idealLaw : Measure α) := by
  rw [m.realMachine.output_law C s fallback hC, m.realMachine_specification,
    WordChoiceTree.realChoice_idealLaw]

theorem realMachine_output_forLeaves {S α : Type*} (m : WordStateMachine S α) (C : ℕ) (s : S)
    (fallback : α) (seed : Fin C → ℝ) (P : α → Prop)
    (h : (m.specification s).decode.ForLeaves P) (hFallback : P fallback) :
    P (m.realMachine.output C s fallback seed) := by
  rw [m.realMachine.output_refines]
  apply RealChoiceTree.output_forLeaves
  · rw [m.realMachine_specification, WordChoiceTree.realChoice_forLeaves]
    exact h
  · exact hFallback

end WordStateMachine
end Blotto
