import Blotto.RationalMachineLaw
import Blotto.WordMachineSerialLaw

/-! Exact whole-law semantics for a source controller followed by native
rational output continuations under one shared cap. -/

namespace Blotto.WordStateMachine
open MeasureTheory

theorem serial_rationalIdealLaw {S α : Type*} {T : α → Type*} {n : ℕ}
    (source : WordStateMachine S α) (next : ∀ a, WordStateMachine (T a) (Fin n → ℚ))
    (start : ∀ a, T a) (C : ℕ) (hC : ∀ a, (next a).rank (start a) ≤ C) (s : S) :
    (source.serial next start C hC).rationalIdealLaw (.source s) =
      (source.specification s).evalLaw (fun a => (next a).rationalIdealLaw (start a)) := by
  apply ProbabilityMeasure.toMeasure_injective
  apply Measure.ext
  intro A hA
  apply (ENNReal.toReal_eq_toReal_iff' (measure_ne_top _ _) (measure_ne_top _ _)).mp
  change ((source.serial next start C hC).rationalIdealLaw (.source s) : Measure (Allocation n)).real A =
    ((source.specification s).evalLaw (fun a => (next a).rationalIdealLaw (start a)) : Measure (Allocation n)).real A
  rw [rationalIdealLaw_event _ _ A hA, serial_mean, WordChoiceTree.evalLaw_real_event _ _ A hA]
  congr 1
  funext a
  exact ((next a).rationalIdealLaw_event (start a) A hA).symm

end Blotto.WordStateMachine
