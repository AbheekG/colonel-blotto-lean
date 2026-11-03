import Blotto.RationalLatticeWords
import Blotto.RationalResourceContracts

/-! Native selected resource updates preserve the fixed rational lattice.
Every intermediate numerator/denominator bound will therefore use the input
lattice, not a product of denominators along the rounding history. -/

namespace Blotto

namespace RationalRoundingPair

theorem total_on_lattice (p : RationalRoundingPair) {D : ℕ}
    (hi : OnRationalLattice D p.resourceI) (hj : OnRationalLattice D p.resourceJ) : OnRationalLattice D p.total := hi.add hj

theorem lower_on_lattice (p : RationalRoundingPair) {D : ℕ}
    (hi : OnRationalLattice D p.resourceI) (hj : OnRationalLattice D p.resourceJ)
    (hL : OnRationalLattice D p.lengthJ) : OnRationalLattice D p.lower :=
  (OnRationalLattice.zero D).max ((p.total_on_lattice hi hj).sub hL)

theorem upper_on_lattice (p : RationalRoundingPair) {D : ℕ}
    (hi : OnRationalLattice D p.resourceI) (hj : OnRationalLattice D p.resourceJ)
    (hL : OnRationalLattice D p.lengthI) : OnRationalLattice D p.upper :=
  hL.min (p.total_on_lattice hi hj)

end RationalRoundingPair

namespace RationalResourceArray

def OnLattice {n : ℕ} (a : RationalResourceArray n) (D : ℕ) : Prop := ∀ j, OnRationalLattice D (a.allocation j)

theorem updatePair_on_lattice {n : ℕ} (a : RationalResourceArray n) {D : ℕ} (ha : a.OnLattice D)
    (i j : Fin n) {z : ℚ} (hz : OnRationalLattice D z) : (a.updatePair i j z).OnLattice D := by
  intro k
  rw [a.allocation_updatePair]
  simp only [Function.update_apply]
  split_ifs
  · exact ((ha i).add (ha j)).sub hz
  · exact hz
  · exact ha k

end RationalResourceArray

namespace RationalActiveResources

theorem update_on_lattice {n : ℕ} {L : Fin n → ℚ} (s : RationalActiveResources L)
    {D : ℕ} (hL : ∀ j, OnRationalLattice D (L j)) (hs : s.resource.OnLattice D)
    (a b : Fin n) (tail : List (Fin n)) (he : s.active = a :: b :: tail) {z : ℚ}
    (hz : z = (s.pair a b tail he).lower ∨ z = (s.pair a b tail he).upper) :
    (s.update a b tail he z).resource.OnLattice D := by
  apply s.resource.updatePair_on_lattice hs
  rcases hz with rfl | rfl
  · exact (s.pair a b tail he).lower_on_lattice (hs a) (hs b) (hL b)
  · exact (s.pair a b tail he).upper_on_lattice (hs a) (hs b) (hL a)

end RationalActiveResources

end Blotto
