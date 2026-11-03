import Blotto.RationalPRGLatticeInput
import Blotto.RationalResourceLatticeMachine

/-! Both native PRG resource phases retain the same input denominator.
Reduced stored words are bounded independently of the number of updates. -/

namespace Blotto.RationalPRGInput

theorem richState_on_lattice {n : ℕ} (i : RationalPRGInput n) : i.richState.resource.OnLattice i.latticeDenominator := by
  intro j
  change OnRationalLattice i.latticeDenominator ((RationalResourceArray.ofAllocation i.richInitial).allocation j)
  rw [RationalResourceArray.allocation_ofAllocation]
  exact i.richInitial_on_lattice j

theorem poorState_on_lattice {n : ℕ} (i : RationalPRGInput n) : i.poorState.resource.OnLattice i.latticeDenominator := by
  intro j
  change OnRationalLattice i.latticeDenominator ((RationalResourceArray.ofAllocation i.poorInitial).allocation j)
  rw [RationalResourceArray.allocation_ofAllocation]
  exact i.poorInitial_on_lattice j

theorem richResource_lattice_completed {n : ℕ} (i : RationalPRGInput n) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources i.lengths}
    (hr : ((rationalResourceMachine i.lengths).run R (.ready i.richState) bits).1 = some result) :
    result.resource.OnLattice i.latticeDenominator :=
  rationalResourceMachine_lattice_completed _ _ i.lengths_on_lattice (.ready i.richState) R bits i.richState_on_lattice hr

theorem poorResource_lattice_completed {n : ℕ} (i : RationalPRGInput n) (R : ℕ) (bits : Fin R → Bool)
    {result : RationalActiveResources i.lengths}
    (hr : ((rationalResourceMachine i.lengths).run R (.ready i.poorState) bits).1 = some result) :
    result.resource.OnLattice i.latticeDenominator :=
  rationalResourceMachine_lattice_completed _ _ i.lengths_on_lattice (.ready i.poorState) R bits i.poorState_on_lattice hr

theorem resource_reduced_word_bounds {n : ℕ} (i : RationalPRGInput n) (result : RationalActiveResources i.lengths)
    (hD : result.resource.OnLattice i.latticeDenominator)
    (hbox : InBox (fun j => (i.lengths j : ℝ)) result.resource.realAllocation) (j : Fin n) :
    (result.resource.allocation j).num.toNat ≤ i.latticeDenominator ∧
      (result.resource.allocation j).den ≤ i.latticeDenominator := by
  have hb := hbox j
  change (0 : ℝ) ≤ (result.resource.allocation j : ℝ) ∧ (result.resource.allocation j : ℝ) ≤ (i.lengths j : ℝ) at hb
  have hbQ : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ i.lengths j := by exact_mod_cast hb
  have h1 : 0 ≤ result.resource.allocation j ∧ result.resource.allocation j ≤ 1 :=
    ⟨hbQ.1, hbQ.2.trans ((i.small_fields j).trans i.b_le)⟩
  exact ⟨rationalLattice_reduced_numerator_le i.latticeDenominator_pos (hD j) h1,
    rationalLattice_den_le i.latticeDenominator_pos (hD j)⟩

end Blotto.RationalPRGInput
