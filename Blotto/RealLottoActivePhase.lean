import Blotto.RealDeferredArrayRefinement
import Blotto.LottoResourceSystem

/-! The global maintained-list source realizes the retained Lotto rounding
law. All reached resources are valid, independent of the supplied real values. -/

namespace Blotto.LottoResourceSystem
open MeasureTheory

noncomputable def realListPhaseReference {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) : Allocation n :=
  (realActiveResourceMachine i.length).output (n - 1)
    (n - 1, ActiveResourceList.initial i.length i.initial) i.initial seed

noncomputable def realPhase {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) : Allocation n :=
  (realActiveArrayMachine i.length).output (n - 1)
    (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) i.initial seed

theorem realPhase_eq_list_reference {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    i.realPhase seed = i.realListPhaseReference seed := by
  unfold realPhase realListPhaseReference RealStateMachine.output
  rw [realActiveArrayMachine_run_eq_list, ArrayResourceState.initial_view]

theorem realPhase_refines {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    i.realPhase seed = i.tree.realChoice.output (n - 1) i.initial seed := by
  change (realActiveArrayMachine i.length).output (n - 1)
    (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) i.initial seed = _
  rw [RealStateMachine.output_refines, realActiveArrayMachine_specification_ready, ArrayResourceState.initial_view]
  rfl

theorem realPhase_valid {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    i.Valid (i.realPhase seed) := by
  rw [i.realPhase_refines]
  apply RealChoiceTree.output_forLeaves_total
  · exact (i.tree.realChoice_forLeaves i.Valid).mpr i.tree_valid
  · rw [i.tree.realChoice_height]
    exact i.tree_height

theorem realPhase_measurable {n : ℕ} (i : LottoResourceSystem n) : Measurable i.realPhase := by
  have hEq : i.realPhase = i.tree.realChoice.output (n - 1) i.initial := funext i.realPhase_refines
  rw [hEq]
  exact RealChoiceTree.measurable_output _ _ _

theorem realPhase_law {n : ℕ} (i : LottoResourceSystem n) :
    Measure.map i.realPhase (RealUniformInputs.law (n - 1) : Measure (Fin (n - 1) → ℝ)) =
      (i.tree.realChoice.idealLaw : Measure (Allocation n)) := by
  have hEq : i.realPhase = i.tree.realChoice.output (n - 1) i.initial := funext i.realPhase_refines
  rw [hEq]
  exact i.tree.realChoice.output_law (n - 1) i.initial (by rw [i.tree.realChoice_height]; exact i.tree_height)

theorem realPhase_reads {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    ((realActiveResourceMachine i.length).run (n - 1)
      (n - 1, ActiveResourceList.initial i.length i.initial) seed).2 ≤ n - 1 :=
  (realActiveResourceMachine i.length).run_reads_rank _ _ _

theorem realPhase_calls {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (realActiveResourceMachine i.length).visits (n - 1) seed
      (n - 1, ActiveResourceList.initial i.length i.initial) 0 (Nat.zero_le _) ≤ (n - 1) + 1 :=
  (realActiveResourceMachine i.length).visits_bound _ _ _ _ _

theorem realPhase_array_reads {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    ((realActiveArrayMachine i.length).run (n - 1)
      (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) seed).2 ≤ n - 1 :=
  (realActiveArrayMachine i.length).run_reads_rank _ _ _

theorem realPhase_array_calls {n : ℕ} (i : LottoResourceSystem n) (seed : Fin (n - 1) → ℝ) :
    (realActiveArrayMachine i.length).visits (n - 1) seed
      (.ready (n - 1) (ArrayResourceState.initial i.length i.initial)) 0 (Nat.zero_le _) ≤ (n - 1) + 1 :=
  (realActiveArrayMachine i.length).visits_bound _ _ _ _ _

end Blotto.LottoResourceSystem
