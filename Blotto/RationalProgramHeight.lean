import Blotto.RationalAllocationProgram
import Blotto.RationalHeight

/-! Whole-coordinate height predicates transfer through native program output
maps, cap exhaustion and deterministic fallbacks. -/

namespace Blotto.RationalAllocationProgram

def LeavesHeight {n C : ℕ} (p : RationalAllocationProgram n C) (s : ℕ) : Prop :=
  (p.machine.specification p.start).decode.ForLeaves (fun x => ∀ j, RationalHeight (x j) s)

theorem mapped_leavesHeight {n m C : ℕ} (p : RationalAllocationProgram n C)
    (f : (Fin n → ℚ) → (Fin m → ℚ)) (s t : ℕ) (h : p.LeavesHeight s)
    (hF : ∀ x, (∀ j, RationalHeight (x j) s) → ∀ j, RationalHeight (f x j) t) :
    (p.mapped f).LeavesHeight t := by
  change ((p.machine.mapped f).specification p.start).decode.ForLeaves _
  rw [WordStateMachine.mapped_specification]
  apply WordChoiceTree.map_forLeaves
  exact WordChoiceTree.forLeaves_mono _ _ _ hF h

theorem fallback_height {n C : ℕ} (p : RationalAllocationProgram n C) (s : ℕ)
    (h : p.LeavesHeight s) (j : Fin n) : RationalHeight (p.fallback j) s :=
  p.machine.chooseLeaf_forLeaves p.start _ h j

theorem sample_height {n C : ℕ} (p : RationalAllocationProgram n C) (s : ℕ)
    (h : p.LeavesHeight s) (R : ℕ) (bits : Fin R → Bool) (j : Fin n) : RationalHeight (p.sample R bits j) s := by
  rw [sample, WordStateMachine.output_refines]
  exact WordChoiceTree.output_forLeaves _ _ _ _ _ h (p.fallback_height s h) j

end Blotto.RationalAllocationProgram
