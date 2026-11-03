import Blotto.RationalFourSpec

/-! The normalized four-variable controller exposes original-coordinate
outputs directly for the global continuation compiler, retaining rank 80. -/

namespace Blotto.RationalFourSpec

theorem machine_forLeaves (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.machine K outerBits scalarBits).specification (i.input.start K outerBits scalarBits)).decode.ForLeaves
      (fun x => FullBudget (i.B : ℝ) (fun j => (x j : ℝ))) := by
  rw [machine, WordStateMachine.mapped_specification]
  apply WordChoiceTree.map_forLeaves
  apply WordChoiceTree.forLeaves_mono _ _ _ _ (i.input.machine_forLeaves K outerBits scalarBits)
  intro x hx
  rw [RationalAffineAllocation.value_real, RationalAffineAllocation.permutation_real]
  exact permuteAllocation_fullBudget i.permutation hx

def fallback (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) : Fin 4 → ℚ :=
  (i.machine K outerBits scalarBits).chooseLeaf (i.input.start K outerBits scalarBits)

theorem fallback_fullBudget (i : RationalFourSpec) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    FullBudget (i.B : ℝ) (fun j => (i.fallback K outerBits scalarBits j : ℝ)) :=
  (i.machine K outerBits scalarBits).chooseLeaf_forLeaves (i.input.start K outerBits scalarBits) _
    (i.machine_forLeaves K outerBits scalarBits)

def fixedSample (i : RationalFourSpec) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : Fin 4 → ℚ :=
  (i.machine K outerBits scalarBits).output R (i.input.start K outerBits scalarBits) (i.fallback K outerBits scalarBits) choiceBits

theorem fixedSample_fullBudget (i : RationalFourSpec) (K R : ℕ) (outerBits scalarBits : Fin K → Bool)
    (choiceBits : Fin R → Bool) : FullBudget (i.B : ℝ) (fun j => (i.fixedSample K R outerBits scalarBits choiceBits j : ℝ)) := by
  rw [fixedSample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ (i.machine_forLeaves K outerBits scalarBits) (i.fallback_fullBudget K outerBits scalarBits)

end Blotto.RationalFourSpec
