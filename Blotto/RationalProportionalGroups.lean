import Blotto.RationalGreedyPacking
import Blotto.ProportionalGroups

/-! Rational group partitions with cached group totals. The sum-based split
is a specification; the cached routing-array emitter is built separately. -/

namespace Blotto
open scoped BigOperators

structure RationalProportionalGroups (n m : ℕ) where
  length : Fin n → ℚ
  length_pos : ∀ j, 0 < length j
  members : Fin m → List (Fin n)
  nodup : ∀ g, (members g).Nodup
  disjoint : ∀ g h, g ≠ h → List.Disjoint (members g) (members h)
  totalData : RationalResourceArray m
  total_eq : ∀ g, totalData.allocation g = rationalGroupLength length (members g)
  total_pos : ∀ g, 0 < totalData.allocation g

namespace RationalProportionalGroups

def total {n m : ℕ} (G : RationalProportionalGroups n m) (g : Fin m) : ℚ := G.totalData.allocation g

noncomputable def real {n m : ℕ} (G : RationalProportionalGroups n m) : ProportionalGroups n m where
  length := fun j => G.length j
  length_pos := fun j => by exact_mod_cast G.length_pos j
  members := fun g => (G.members g).toFinset
  disjoint := by
    intro g h hgh
    exact Finset.disjoint_left.mpr (by
      intro j hj hk
      exact List.disjoint_left.mp (G.disjoint g h hgh)
        (List.mem_toFinset.mp hj) (List.mem_toFinset.mp hk))
  total_pos := by
    intro g
    rw [List.sum_toFinset _ (G.nodup g)]
    change 0 < groupLength (fun j => (G.length j : ℝ)) (G.members g)
    rw [← rationalGroupLength_real, ← G.total_eq]
    exact_mod_cast G.total_pos g

theorem total_real {n m : ℕ} (G : RationalProportionalGroups n m) (g : Fin m) :
    (G.total g : ℝ) = G.real.total g := by
  change (G.totalData.allocation g : ℝ) = ∑ j ∈ (G.members g).toFinset, (G.length j : ℝ)
  rw [G.total_eq, rationalGroupLength_real]
  exact (List.sum_toFinset _ (G.nodup g)).symm

def coefficient {n m : ℕ} (G : RationalProportionalGroups n m) (g : Fin m) (j : Fin n) : ℚ :=
  if j ∈ G.members g then G.length j / G.total g else 0

def split {n m : ℕ} (G : RationalProportionalGroups n m) (y : Fin m → ℚ) : Fin n → ℚ :=
  fun j => ∑ g, G.coefficient g j * y g

def splitMixed {n m : ℕ} (G : RationalProportionalGroups n m) (pivot : Fin n)
    (y : Fin (m + 1) → ℚ) : Fin n → ℚ :=
  fun j => G.split (fun g => y g.castSucc) j + if j = pivot then y (Fin.last m) else 0

theorem coefficient_real {n m : ℕ} (G : RationalProportionalGroups n m) (g : Fin m) (j : Fin n) :
    (G.coefficient g j : ℝ) = G.real.coefficient g j := by
  change (↑(if j ∈ G.members g then G.length j / G.total g else 0) : ℝ) =
    if j ∈ (G.members g).toFinset then (G.length j : ℝ) / G.real.total g else 0
  simp only [List.mem_toFinset]
  split_ifs <;> simp [Rat.cast_div, G.total_real]

theorem split_real {n m : ℕ} (G : RationalProportionalGroups n m) (y : Fin m → ℚ) :
    (fun j => (G.split y j : ℝ)) = G.real.split (fun g => (y g : ℝ)) := by
  funext j
  simp only [split, Rat.cast_sum, Rat.cast_mul, G.coefficient_real, ProportionalGroups.split]

theorem splitMixed_real {n m : ℕ} (G : RationalProportionalGroups n m) (pivot : Fin n)
    (y : Fin (m + 1) → ℚ) :
    (fun j => (G.splitMixed pivot y j : ℝ)) = G.real.splitMixed pivot (fun g => (y g : ℝ)) := by
  funext j
  simp only [splitMixed, Rat.cast_add, ProportionalGroups.splitMixed]
  rw [congrFun (G.split_real (fun g => y g.castSucc)) j]
  by_cases h : j = pivot <;> simp [h]

theorem split_fullBudget {n m : ℕ} (G : RationalProportionalGroups n m) {B : ℚ} {y : Fin m → ℚ}
    (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (B : ℝ) (fun j => (G.split y j : ℝ)) := by
  rw [G.split_real]
  exact G.real.split_fullBudget hy

theorem splitMixed_fullBudget {n m : ℕ} (G : RationalProportionalGroups n m) (pivot : Fin n)
    {B : ℚ} {y : Fin (m + 1) → ℚ} (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) :
    FullBudget (B : ℝ) (fun j => (G.splitMixed pivot y j : ℝ)) := by
  rw [G.splitMixed_real]
  exact G.real.splitMixed_fullBudget pivot hy

end RationalProportionalGroups
end Blotto
