import Blotto.FixedArrayTable
import Blotto.RationalProportionalGroups

/-! Prepare one cached route and rational coefficient per original field.
Assignments traverse each disjoint group once; emission reads no member list
and recomputes no group total. Array ownership/cost is a separate contract. -/

namespace Blotto
open scoped BigOperators

abbrev GroupRoute (m : ℕ) := Option (Fin m) × ℚ

namespace RationalProportionalGroups

def routeAssignments {n m : ℕ} (G : RationalProportionalGroups n m) : List (Fin n × GroupRoute m) :=
  (List.finRange m).flatMap (fun g => (G.members g).map (fun j => (j, (some g, G.length j / G.total g))))

def routes {n m : ℕ} (G : RationalProportionalGroups n m) : FixedArrayTable n (GroupRoute m) :=
  (FixedArrayTable.ofFn (fun _ => (none, 0))).patch G.routeAssignments

def emit {n m : ℕ} (_G : RationalProportionalGroups n m) (table : FixedArrayTable n (GroupRoute m))
    (y : Fin m → ℚ) : RationalResourceArray n :=
  RationalResourceArray.ofAllocation (fun j =>
    let r := table.read j
    match r.1 with
    | none => 0
    | some g => r.2 * y g)

theorem mem_routeAssignments {n m : ℕ} (G : RationalProportionalGroups n m) (e : Fin n × GroupRoute m) :
    e ∈ G.routeAssignments ↔ ∃ g, e.1 ∈ G.members g ∧ e.2 = (some g, G.length e.1 / G.total g) := by
  simp only [routeAssignments, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨g, j, hj, he⟩
    cases he
    exact ⟨g, hj, rfl⟩
  · rintro ⟨g, hj, he⟩
    exact ⟨g, e.1, hj, by cases e; simp_all⟩

theorem routeAssignments_keys {n m : ℕ} (G : RationalProportionalGroups n m) (j : Fin n) :
    j ∈ G.routeAssignments.map Prod.fst ↔ ∃ g, j ∈ G.members g := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, he, hj⟩
    rcases (G.mem_routeAssignments e).mp he with ⟨g, hg, _⟩
    exact ⟨g, hj ▸ hg⟩
  · rintro ⟨g, hj⟩
    refine ⟨(j, (some g, G.length j / G.total g)), ?_, rfl⟩
    exact (G.mem_routeAssignments _).mpr ⟨g, hj, rfl⟩

theorem routes_group {n m : ℕ} (G : RationalProportionalGroups n m) {g : Fin m} {j : Fin n}
    (hj : j ∈ G.members g) : G.routes.read j = (some g, G.length j / G.total g) := by
  apply FixedArrayTable.read_patch_at
  · intro e he hej
    rcases (G.mem_routeAssignments e).mp he with ⟨h, hh, heh⟩
    have hgj : h = g := by
      by_contra hne
      exact List.disjoint_left.mp (G.disjoint h g hne) (hej ▸ hh) hj
    rw [heh, hej, hgj]
  · exact (G.routeAssignments_keys j).mpr ⟨g, hj⟩

theorem routes_inactive {n m : ℕ} (G : RationalProportionalGroups n m) {j : Fin n}
    (hj : ∀ g, j ∉ G.members g) : G.routes.read j = (none, 0) := by
  have he : j ∉ G.routeAssignments.map Prod.fst := by
    rw [G.routeAssignments_keys]
    rintro ⟨g, hg⟩
    exact hj g hg
  rw [routes, FixedArrayTable.patch_preserves _ _ _ he, FixedArrayTable.read_ofFn]

theorem emit_group {n m : ℕ} (G : RationalProportionalGroups n m) {g : Fin m} {j : Fin n}
    (hj : j ∈ G.members g) (y : Fin m → ℚ) :
    (G.emit G.routes y).allocation j = G.length j / G.total g * y g := by
  simp only [emit, RationalResourceArray.allocation_ofAllocation, G.routes_group hj]

theorem emit_inactive {n m : ℕ} (G : RationalProportionalGroups n m) {j : Fin n}
    (hj : ∀ g, j ∉ G.members g) (y : Fin m → ℚ) : (G.emit G.routes y).allocation j = 0 := by
  simp only [emit, RationalResourceArray.allocation_ofAllocation, G.routes_inactive hj]

theorem emit_real {n m : ℕ} (G : RationalProportionalGroups n m) (y : Fin m → ℚ) :
    (G.emit G.routes y).realAllocation = G.real.split (fun g => (y g : ℝ)) := by
  classical
  funext j
  by_cases he : ∃ g, j ∈ G.members g
  · rcases he with ⟨g, hg⟩
    have hr := G.real.split_group_coordinate (by simpa [real] using hg) (fun g => (y g : ℝ))
    rw [hr]
    change ((G.emit G.routes y).allocation j : ℝ) = (G.length j : ℝ) / G.real.total g * (y g : ℝ)
    rw [G.emit_group hg, Rat.cast_mul, Rat.cast_div, G.total_real]
  · have hj : ∀ g, j ∉ G.members g := by simpa using he
    have hr := G.real.split_inactive_coordinate (by simpa [real] using hj) (fun g => (y g : ℝ))
    rw [hr]
    change ((G.emit G.routes y).allocation j : ℝ) = 0
    rw [G.emit_inactive hj, Rat.cast_zero]

theorem emit_fullBudget {n m : ℕ} (G : RationalProportionalGroups n m) {B : ℚ} {y : Fin m → ℚ}
    (hy : FullBudget (B : ℝ) (fun g => (y g : ℝ))) : FullBudget (B : ℝ) (G.emit G.routes y).realAllocation := by
  rw [G.emit_real]
  exact G.real.split_fullBudget hy

end RationalProportionalGroups
end Blotto
