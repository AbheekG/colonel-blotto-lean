import Blotto.RationalTerminalLottoHeight
import Blotto.RationalResourceLatticeMachine
import Blotto.WordTreeLeafContracts
import Blotto.RationalLottoPaperProgram

/-! Complete native normalized-budget output heights follow the retained
input lattice through the actual source phase and selected terminal compiler.
The bound holds for every cap/bit path and the direct paper fallback. -/

namespace Blotto.RationalLottoResourceSystem

def OnLattice {n : ℕ} (i : RationalLottoResourceSystem n) (D : ℕ) : Prop :=
  (∀ j, OnRationalLattice D (i.length j)) ∧ ∀ j, OnRationalLattice D (i.initial j)

theorem OnLattice.phase_leaves {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D) :
    (i.phase.specification i.start).decode.ForLeaves (fun value => value.1.resource.OnLattice D) := by
  have hInitial : i.initialState.resource.OnLattice D := by
    intro j
    change OnRationalLattice D ((RationalResourceArray.ofAllocation i.initial).allocation j)
    rw [RationalResourceArray.allocation_ofAllocation]
    exact h.2 j
  have hRaw := rationalResourceMachine_lattice_leaves i.length D h.1 (.ready i.initialState) hInitial
  have hEq : (i.phase.specification i.start).map Subtype.val =
      (rationalResourceMachine i.length).specification (.ready i.initialState) :=
    (rationalResourceMachine i.length).restricted_specification i.CursorInvariant i.TerminalState i.phaseProof i.start
  rw [← hEq] at hRaw
  exact (WordChoiceTree.forLeaves_map_iff _ Subtype.val _).mp hRaw

theorem OnLattice.terminalData {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (value : i.PhaseResult) (hValue : value.1.resource.OnLattice D) : (i.terminalData value).OnLattice D := ⟨h.1, hValue⟩

theorem OnLattice.program_leaves {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hBudget : RationalHeight i.B s)
    (hWidth : binaryWordWidth D ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    (i.program K outerBits scalarBits).LeavesHeight (expressionHeightBudget (max s (K + 2)) 75) := by
  change ((i.machine K outerBits scalarBits).specification (i.samplingStart K outerBits scalarBits)).decode.ForLeaves _
  rw [machine, samplingStart, WordStateMachine.serial_source_specification]
  apply WordChoiceTree.bind_forLeaves_of _ _ (fun value => value.1.resource.OnLattice D)
  · exact h.phase_leaves
  · intro value hValue
    exact (h.terminalData value hValue).program_leaves hD hB s hs hBudget hWidth K outerBits scalarBits

theorem fallbackAllocation_height {n : ℕ} (i : RationalLottoResourceSystem n) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (j : Fin n) : RationalHeight (i.fallbackAllocation j) s := by
  unfold fallbackAllocation
  split
  · exact hBudget
  · exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs

theorem OnLattice.paperFixedSample {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hBudget : RationalHeight i.B s)
    (hWidth : binaryWordWidth D ≤ s) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) (j : Fin n) :
    RationalHeight (i.paperFixedSample K R outerBits scalarBits choiceBits j) (expressionHeightBudget (max s (K + 2)) 75) := by
  rw [RationalLottoResourceSystem.paperFixedSample_refines, RationalLottoResourceSystem.paperFixedSampleReference, WordStateMachine.output_refines]
  have hm : s ≤ expressionHeightBudget (max s (K + 2)) 75 :=
    (le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (h.program_leaves hD hB s hs hBudget hWidth K outerBits scalarBits)
    (fun j => (i.fallbackAllocation_height s hs hBudget j).mono hm) j

theorem OnLattice.paperSample {n : ℕ} {i : RationalLottoResourceSystem n} {D : ℕ} (h : i.OnLattice D)
    (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s) (hBudget : RationalHeight i.B s)
    (hWidth : binaryWordWidth D ≤ s) (K : ℕ) (bits : Fin (sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.paperSample K bits j) (expressionHeightBudget (max s (K + 2)) 75) :=
  h.paperFixedSample hD hB s hs hBudget hWidth K _ _ _ _ j

end Blotto.RationalLottoResourceSystem
