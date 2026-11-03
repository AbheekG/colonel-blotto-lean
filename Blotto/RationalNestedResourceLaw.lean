import Blotto.RationalNestedResourcePhase
import Blotto.RationalTerminalProfileLaw
import Blotto.WordTreeAllocationLaw

/-! Exact ideal marginals and midpoint error of the native three-resource
phase followed by its terminal compiler. Joint-law equality with another
rounding selector is not assumed; coordinate means prove the marginal identity. -/

namespace Blotto.RationalNestedResourceSystem
open MeasureTheory

theorem phase_weight_mean (i : RationalNestedResourceSystem) (j : Fin 3) :
    (i.phase.specification i.start).decode.mean (fun s => (i.terminalData s).real.weight j) =
      (i.initial j : ℝ) / (i.capacity j : ℝ) := by
  have h : (fun s : {s : RationalActiveResources i.capacity // i.TerminalState s} => (i.terminalData s).real.weight j) =
      (fun s => (i.terminalData s).real.resource j / (i.capacity j : ℝ)) := by
    funext s
    unfold TerminalResources.weight TerminalResources.capacity
    change (s.1.resource.allocation j : ℝ) / ((i.long j : ℝ) - (i.short j : ℝ)) =
      (s.1.resource.allocation j : ℝ) / (i.capacity j : ℝ)
    rw [capacity, Rat.cast_sub]
  rw [h, WordChoiceTree.mean_div_const, i.phase_mean]

noncomputable def exactLaw (i : RationalNestedResourceSystem) : Mixed 3 :=
  (i.phase.specification i.start).evalLaw (fun s => (i.terminalData s).real.law)

theorem exactLaw_marginal (i : RationalNestedResourceSystem) (j : Fin 3) :
    (marginal i.exactLaw j : Measure ℝ) =
      affineMeasure ((i.initial j : ℝ) / (i.capacity j : ℝ)) (uniformLaw (i.short j : ℝ)) (uniformLaw (i.long j : ℝ)) := by
  unfold exactLaw
  rw [WordChoiceTree.evalLaw_affine_marginal _ _ (fun s => (i.terminalData s).real.weight j)
    (fun s => (i.terminalData s).real.weight_bounds j) j (uniformLaw (i.short j : ℝ)) (uniformLaw (i.long j : ℝ))
    (fun s => (i.terminalData s).real.law_contract.2 j), i.phase_weight_mean]

theorem exactLaw_marginal_eq (i : RationalNestedResourceSystem) (j : Fin 3) :
    (marginal i.exactLaw j : Measure ℝ) = (marginal i.real.law j : Measure ℝ) := by
  rw [i.exactLaw_marginal, i.real.law_contract.2 j]
  change affineMeasure ((i.initial j : ℝ) / (i.capacity j : ℝ)) (uniformLaw (i.short j : ℝ)) (uniformLaw (i.long j : ℝ)) =
    affineMeasure (i.real.initialWeight j) (uniformLaw (i.short j : ℝ)) (uniformLaw (i.long j : ℝ))
  congr 1
  rw [i.capacity_real]
  rfl

noncomputable def midpointLaw (i : RationalNestedResourceSystem) (K : ℕ) : Mixed 3 :=
  (i.phase.specification i.start).evalLaw (fun s => (i.terminalData s).midpointLaw K)

theorem midpointLaw_CDF_error (i : RationalNestedResourceSystem) (K : ℕ) :
    CDFClose (i.midpointLaw K) i.real.law (3 / (2 * (2 : ℝ) ^ K)) := by
  have h := (i.phase.specification i.start).evalLaw_CDFClose
    (fun s => (i.terminalData s).midpointLaw K) (fun s => (i.terminalData s).real.law)
    (fun s => (i.terminalData s).midpointLaw_CDF_error K)
  intro j z
  have hj := h j z
  unfold closedCDF at hj ⊢
  change |(marginal (i.midpointLaw K) j : Measure ℝ).real _ - (marginal i.exactLaw j : Measure ℝ).real _| ≤ _ at hj
  rw [i.exactLaw_marginal_eq j] at hj
  exact hj

theorem midpointLaw_fullBudget (i : RationalNestedResourceSystem) (K : ℕ) :
    ∀ᵐ x ∂(i.midpointLaw K : Measure (Allocation 3)), FullBudget (i.M : ℝ) x :=
  (i.phase.specification i.start).evalLaw_fullBudget _ (fun s => (i.terminalData s).midpointLaw_fullBudget K)

theorem midpointLaw_inBox (i : RationalNestedResourceSystem) (K : ℕ) :
    ∀ᵐ x ∂(i.midpointLaw K : Measure (Allocation 3)), InBox (fun j => (i.long j : ℝ)) x :=
  (i.phase.specification i.start).evalLaw_ae _ _ (fun s => (i.terminalData s).midpointLaw_inBox K)

end Blotto.RationalNestedResourceSystem
