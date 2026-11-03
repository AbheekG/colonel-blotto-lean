import Blotto.RationalLatticeWords

/-! The native normalized PRG input supplies one denominator for both
players' capacities and initial resources, without an external certificate. -/

namespace Blotto.RationalPRGInput
open scoped BigOperators

def valueDenominator {n : ℕ} (i : RationalPRGInput n) : ℕ := ∏ j, (i.values j).den

def latticeDenominator {n : ℕ} (i : RationalPRGInput n) : ℕ := i.b.den * i.valueDenominator

theorem valueDenominator_pos {n : ℕ} (i : RationalPRGInput n) : 0 < i.valueDenominator := by
  exact Finset.prod_pos (fun j _ => (i.values j).den_pos)

theorem latticeDenominator_pos {n : ℕ} (i : RationalPRGInput n) : 0 < i.latticeDenominator :=
  Nat.mul_pos i.b.den_pos i.valueDenominator_pos

theorem values_on_lattice {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : OnRationalLattice i.valueDenominator (i.values j) :=
  Finset.dvd_prod_of_mem _ (Finset.mem_univ j)

theorem lengths_on_value_lattice {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : OnRationalLattice i.valueDenominator (i.lengths j) :=
  (i.values_on_lattice j).int_mul 2

theorem lengths_on_lattice {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : OnRationalLattice i.latticeDenominator (i.lengths j) :=
  (i.lengths_on_value_lattice j).enlarge (Nat.dvd_mul_left i.valueDenominator i.b.den)

theorem richInitial_on_lattice {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : OnRationalLattice i.latticeDenominator (i.richInitial j) :=
  i.lengths_on_lattice j

theorem poorInitial_on_lattice {n : ℕ} (i : RationalPRGInput n) (j : Fin n) : OnRationalLattice i.latticeDenominator (i.poorInitial j) :=
  OnRationalLattice.mul (D := i.b.den) (E := i.valueDenominator) (dvd_refl _) (i.lengths_on_value_lattice j)

end Blotto.RationalPRGInput
