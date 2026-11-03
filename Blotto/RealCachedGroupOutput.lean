import Blotto.FixedArrayTable
import Blotto.ProportionalGroups

/-! Real output preparation caches each group total once and writes one
route/coefficient per member. Emission materializes the small draw once and
performs one output-array pass, with no member search or total recomputation. -/

namespace Blotto
open scoped Classical

abbrev RealGroupRoute (m : ℕ) := Option (Fin m) × ℝ

namespace ProportionalGroups

noncomputable def realRouteAssignments {n m : ℕ} (G : ProportionalGroups n m)
    (totals : FixedArrayTable m ℝ) : List (Fin n × RealGroupRoute m) :=
  (List.finRange m).flatMap fun g => (G.members g).toList.map fun j => (j, (some g, G.length j / totals.read g))

noncomputable def realRoutes {n m : ℕ} (G : ProportionalGroups n m) (totals : FixedArrayTable m ℝ) :
    FixedArrayTable n (RealGroupRoute m) :=
  (FixedArrayTable.ofFn (fun _ => (none, 0))).patch (G.realRouteAssignments totals)

theorem mem_realRouteAssignments {n m : ℕ} (G : ProportionalGroups n m) (totals : FixedArrayTable m ℝ)
    (e : Fin n × RealGroupRoute m) :
    e ∈ G.realRouteAssignments totals ↔ ∃ g, e.1 ∈ G.members g ∧ e.2 = (some g, G.length e.1 / totals.read g) := by
  simp only [realRouteAssignments, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map, Finset.mem_toList]
  constructor
  · rintro ⟨g, j, hj, he⟩
    cases he
    exact ⟨g, hj, rfl⟩
  · rintro ⟨g, hj, he⟩
    exact ⟨g, e.1, hj, by cases e; simp_all⟩

theorem realRouteAssignments_keys {n m : ℕ} (G : ProportionalGroups n m) (totals : FixedArrayTable m ℝ) (j : Fin n) :
    j ∈ (G.realRouteAssignments totals).map Prod.fst ↔ ∃ g, j ∈ G.members g := by
  simp only [List.mem_map]
  constructor
  · rintro ⟨e, he, hj⟩
    rcases (G.mem_realRouteAssignments totals e).mp he with ⟨g, hg, _⟩
    exact ⟨g, hj ▸ hg⟩
  · rintro ⟨g, hj⟩
    refine ⟨(j, (some g, G.length j / totals.read g)), ?_, rfl⟩
    exact (G.mem_realRouteAssignments totals _).mpr ⟨g, hj, rfl⟩

theorem realRoutes_group {n m : ℕ} (G : ProportionalGroups n m) (totals : FixedArrayTable m ℝ)
    {g : Fin m} {j : Fin n} (hj : j ∈ G.members g) :
    (G.realRoutes totals).read j = (some g, G.length j / totals.read g) := by
  apply FixedArrayTable.read_patch_at
  · intro e he hej
    rcases (G.mem_realRouteAssignments totals e).mp he with ⟨h, hh, heh⟩
    have hgj : h = g := by
      by_contra hne
      exact Finset.disjoint_left.mp (G.disjoint h g hne) (hej ▸ hh) hj
    rw [heh, hej, hgj]
  · exact (G.realRouteAssignments_keys totals j).mpr ⟨g, hj⟩

theorem realRoutes_inactive {n m : ℕ} (G : ProportionalGroups n m) (totals : FixedArrayTable m ℝ)
    {j : Fin n} (hj : ∀ g, j ∉ G.members g) : (G.realRoutes totals).read j = (none, 0) := by
  have he : j ∉ (G.realRouteAssignments totals).map Prod.fst := by
    rw [G.realRouteAssignments_keys]
    rintro ⟨g, hg⟩
    exact hj g hg
  rw [realRoutes, FixedArrayTable.patch_preserves _ _ _ he, FixedArrayTable.read_ofFn]

end ProportionalGroups

structure RealPreparedGroupOutput {n m : ℕ} (G : ProportionalGroups n m) where
  totals : FixedArrayTable m ℝ
  total_correct : ∀ g, totals.read g = G.total g
  table : FixedArrayTable n (RealGroupRoute m)
  table_correct : ∀ j, table.read j = (G.realRoutes totals).read j

namespace RealPreparedGroupOutput

noncomputable def prepare {n m : ℕ} (G : ProportionalGroups n m) : RealPreparedGroupOutput G :=
  let totals := FixedArrayTable.ofFn G.total
  ⟨totals, FixedArrayTable.read_ofFn G.total, G.realRoutes totals, fun _ => rfl⟩

noncomputable def emit {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (y : Allocation m) : FixedArrayTable n ℝ :=
  let sampled := FixedArrayTable.ofFn y
  FixedArrayTable.ofFn fun j =>
    let r := p.table.read j
    match r.1 with
    | none => 0
    | some g => r.2 * sampled.read g

theorem emit_allocation {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (y : Allocation m) : (p.emit y).read = G.split y := by
  funext j
  simp only [emit, FixedArrayTable.read_ofFn, p.table_correct]
  by_cases he : ∃ g, j ∈ G.members g
  · rcases he with ⟨g, hg⟩
    rw [G.realRoutes_group p.totals hg, G.split_group_coordinate hg]
    dsimp only
    rw [p.total_correct]
  · have hj : ∀ g, j ∉ G.members g := by simpa using he
    rw [G.realRoutes_inactive p.totals hj, G.split_inactive_coordinate hj]

noncomputable def emitMixed {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (pivot : Fin n) (y : Allocation (m + 1)) : FixedArrayTable n ℝ :=
  let sampled := FixedArrayTable.ofFn y
  FixedArrayTable.ofFn fun j =>
    (let r := p.table.read j
     match r.1 with
     | none => 0
     | some g => r.2 * sampled.read g.castSucc) + if j = pivot then sampled.read (Fin.last m) else 0

theorem emitMixed_allocation {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (pivot : Fin n) (y : Allocation (m + 1)) : (p.emitMixed pivot y).read = G.splitMixed pivot y := by
  funext j
  have hEmit := congrFun (p.emit_allocation (fun g => y g.castSucc)) j
  simp only [emit, FixedArrayTable.read_ofFn] at hEmit
  simp only [emitMixed, FixedArrayTable.read_ofFn, ProportionalGroups.splitMixed]
  rw [hEmit]

theorem emit_fullBudget {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    {B : ℝ} {y : Allocation m} (hy : FullBudget B y) : FullBudget B (p.emit y).read := by
  rw [p.emit_allocation]
  exact G.split_fullBudget hy

theorem emitMixed_fullBudget {n m : ℕ} {G : ProportionalGroups n m} (p : RealPreparedGroupOutput G)
    (pivot : Fin n) {B : ℝ} {y : Allocation (m + 1)} (hy : FullBudget B y) :
    FullBudget B (p.emitMixed pivot y).read := by
  rw [p.emitMixed_allocation]
  exact G.splitMixed_fullBudget pivot hy

end RealPreparedGroupOutput
end Blotto
