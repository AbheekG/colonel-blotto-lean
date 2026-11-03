import Blotto.SharedResourceBudget
import Blotto.RationalResourceLatticeMachine

/-! The primary one-state pending cursor retains the resource lattice.
Word residual iterations leave the same resource state, and selected updates
preserve the input denominator. No depth-dependent denominator is introduced. -/

namespace Blotto.ResourceChoice

theorem select_on_lattice {n : ℕ} {L : Fin n → ℚ} (choice : ResourceChoice L) (D : ℕ)
    (hL : ∀ j, OnRationalLattice D (L j)) (hState : choice.state.resource.OnLattice D) (branch : Bool) :
    (choice.select branch).resource.OnLattice D := by
  have hEndpoint : (if branch then choice.upper else choice.lower) =
      (choice.state.pair choice.first choice.second choice.tail choice.head_pair).lower ∨
      (if branch then choice.upper else choice.lower) =
      (choice.state.pair choice.first choice.second choice.tail choice.head_pair).upper := by
    cases branch
    · exact Or.inl choice.lower_correct
    · exact Or.inr choice.upper_correct
  exact choice.state.update_on_lattice hL hState choice.first choice.second choice.tail choice.head_pair hEndpoint

end Blotto.ResourceChoice
namespace Blotto.SharedResourceCursor

def OnLattice {n : ℕ} {L : Fin n → ℚ} (D : ℕ) : SharedResourceCursor L → Prop
  | .ready state => state.resource.OnLattice D
  | .coin choice _ _ _ _ => choice.state.resource.OnLattice D

theorem prepared_on_lattice {n : ℕ} {L : Fin n → ℚ} (D : ℕ) (state : RationalActiveResources L)
    (hState : state.resource.OnLattice D) (p : PreparedResourceChoice L) (hPrepare : prepareResourceChoice state = .ask p) :
    (prepared p).OnLattice D := by
  have hOwner := prepareResourceChoice_owner state
  rw [hPrepare] at hOwner
  change p.choice.state = state at hOwner
  change p.choice.state.resource.OnLattice D
  rw [hOwner]
  exact hState

theorem done_on_lattice {n : ℕ} {L : Fin n → ℚ} (D : ℕ) (hL : ∀ j, OnRationalLattice D (L j))
    (state : RationalActiveResources L) (hState : state.resource.OnLattice D) (value : RationalActiveResources L)
    (hPrepare : prepareResourceChoice state = .done value) : value.resource.OnLattice D := by
  have hp := rationalResourceStep_lattice D hL state hState
  have he := prepareResourceChoice_refines state
  rw [hPrepare] at he
  change WordTransition.done value = rationalResourceStep state at he
  rw [← he] at hp
  exact hp

end Blotto.SharedResourceCursor
