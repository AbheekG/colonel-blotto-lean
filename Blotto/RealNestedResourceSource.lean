import Blotto.RealRoundingSource
import Blotto.RealTerminalResources
import Blotto.NestedResourceSystem

/-! The three-resource source needs at most two exact comparisons. It always
reaches a valid terminal, even when input values are outside the unit interval;
allocation feasibility uses the valid unit inputs of the terminal draw. -/

namespace Blotto.NestedResourceSystem
open MeasureTheory

noncomputable def realPhase (i : NestedResourceSystem) (seed : Fin 2 → ℝ) : Allocation 3 :=
  (realResourceMachine i.capacity (selectThreePair i.capacity)).output 2 (2, i.initial) i.initial seed

theorem realPhase_refines (i : NestedResourceSystem) (seed : Fin 2 → ℝ) :
    i.realPhase seed = i.tree.realChoice.output 2 i.initial seed := by
  change (realResourceMachine i.capacity (selectThreePair i.capacity)).output 2 (2, i.initial) i.initial seed = _
  rw [RealStateMachine.output_refines, realResourceMachine_specification]
  rfl

theorem realPhase_valid (i : NestedResourceSystem) (seed : Fin 2 → ℝ) : i.Valid (i.realPhase seed) := by
  rw [i.realPhase_refines]
  apply RealChoiceTree.output_forLeaves_total
  · exact (i.tree.realChoice_forLeaves i.Valid).mpr i.tree_valid
  · rw [i.tree.realChoice_height]
    exact i.tree_height

theorem realPhase_measurable (i : NestedResourceSystem) : Measurable i.realPhase := by
  have h : i.realPhase = i.tree.realChoice.output 2 i.initial := funext i.realPhase_refines
  rw [h]
  exact RealChoiceTree.measurable_output _ _ _

theorem realPhase_law (i : NestedResourceSystem) :
    Measure.map i.realPhase (RealUniformInputs.law 2 : Measure (Fin 2 → ℝ)) =
      (i.tree.realChoice.idealLaw : Measure (Allocation 3)) := by
  have h : i.realPhase = i.tree.realChoice.output 2 i.initial := funext i.realPhase_refines
  rw [h]
  exact i.tree.realChoice.output_law 2 i.initial (by rw [i.tree.realChoice_height]; exact i.tree_height)

theorem realPhase_reads (i : NestedResourceSystem) (seed : Fin 2 → ℝ) :
    ((realResourceMachine i.capacity (selectThreePair i.capacity)).run 2 (2, i.initial) seed).2 ≤ 2 :=
  (realResourceMachine i.capacity (selectThreePair i.capacity)).run_reads_rank 2 (2, i.initial) seed

theorem realPhase_calls (i : NestedResourceSystem) (seed : Fin 2 → ℝ) :
    (realResourceMachine i.capacity (selectThreePair i.capacity)).visits 2 seed (2, i.initial) 0 (Nat.zero_le _) ≤ 3 :=
  (realResourceMachine i.capacity (selectThreePair i.capacity)).visits_bound 2 seed (2, i.initial) 0 (Nat.zero_le _)

noncomputable def realSample (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ)) : Allocation 3 :=
  (i.terminal (i.realPhase seed.1) (i.realPhase_valid seed.1)).realSample seed.2

theorem realSample_fullBudget (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ))
    (h : ∀ j, 0 ≤ seed.2 j ∧ seed.2 j ≤ 1) : FullBudget i.M (i.realSample seed) :=
  (i.terminal (i.realPhase seed.1) (i.realPhase_valid seed.1)).realSample_fullBudget seed.2 h

theorem realSample_inBox (i : NestedResourceSystem) (seed : (Fin 2 → ℝ) × (Fin 11 → ℝ))
    (h : ∀ j, 0 ≤ seed.2 j ∧ seed.2 j ≤ 1) : InBox i.long (i.realSample seed) :=
  (i.terminal (i.realPhase seed.1) (i.realPhase_valid seed.1)).realSample_inBox seed.2 h

end Blotto.NestedResourceSystem
