import Blotto.PreparedGroupEmissionCost

/-! The cached output coordinate pass performs at most one multiplication
per ordinary field, plus one addition per mixed field. Group-vector production,
addressing/branching/copies and the physical allocation backend are separate. -/

namespace Blotto.PreparedGroupOutput
open scoped BigOperators

def routedArithmeticWork {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) (j : Fin n) : ℕ :=
  match (p.table.read j).1 with
  | none => 0
  | some _ => 1

def emitArithmeticWork {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) : ℕ :=
  ∑ j, p.routedArithmeticWork j

theorem emitArithmeticWork_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) :
    p.emitArithmeticWork ≤ n := by
  have hp : ∀ j, p.routedArithmeticWork j ≤ 1 := by
    intro j
    unfold routedArithmeticWork
    split <;> omega
  calc
    _ ≤ ∑ _j : Fin n, 1 := Finset.sum_le_sum (fun j _ => hp j)
    _ = _ := by simp

def emitMixedArithmeticWork {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) : ℕ :=
  ∑ j, (p.routedArithmeticWork j + 1)

theorem emitMixedArithmeticWork_bound {n m : ℕ} {G : RationalProportionalGroups n m} (p : PreparedGroupOutput G) :
    p.emitMixedArithmeticWork ≤ 2 * n := by
  unfold emitMixedArithmeticWork
  rw [Finset.sum_add_distrib]
  have hp := p.emitArithmeticWork_bound
  change (∑ j, p.routedArithmeticWork j) ≤ n at hp
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, Nat.mul_one]
  omega

end Blotto.PreparedGroupOutput
