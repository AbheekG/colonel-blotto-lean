import Blotto.RealTerminalPacking

/-! Cached routing assignments traverse the greedy scan's raw lists. Their
keys are exactly the saturated fields, with no duplicate writes. -/

namespace Blotto.RealTerminalPacking
open scoped Classical

noncomputable def routeAssignments {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) : List (Fin n × RealGroupRoute i.groups.length) :=
  (List.finRange i.groups.length).flatMap fun g =>
    (p.groups.read g).1.map fun j => (j, (some g, i.length j / totals.read g))

theorem mem_routeAssignments {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) (e : Fin n × RealGroupRoute i.groups.length) :
    e ∈ p.routeAssignments totals ↔ ∃ g, e.1 ∈ i.partition.members g ∧ e.2 = (some g, i.length e.1 / totals.read g) := by
  simp only [routeAssignments, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨g, j, hj, he⟩
    cases he
    exact ⟨g, (p.mem_group g j).mp hj, rfl⟩
  · rintro ⟨g, hj, he⟩
    refine ⟨g, e.1, (p.mem_group g e.1).mpr hj, ?_⟩
    cases e
    simp_all

theorem routeAssignments_keys_eq {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) :
    (p.routeAssignments totals).map Prod.fst = i.uniformItems := by
  have hGroups : ((List.finRange i.groups.length).map (fun g => (p.groups.read g).1)) = i.groups := by
    simp only [p.members_correct, List.map_get_finRange]
  simp only [routeAssignments, List.map_flatMap, List.map_map, Function.comp_def, List.map_id']
  change ((List.finRange i.groups.length).flatMap (fun g => (p.groups.read g).1)) = i.uniformItems
  rw [List.flatMap_def, hGroups]
  exact greedyGroups_flatten i.length i.B i.uniformItems

theorem routeAssignments_length {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) : (p.routeAssignments totals).length = i.uniformItems.length := by
  have h := congrArg List.length (p.routeAssignments_keys_eq totals)
  simpa only [List.length_map] using h

theorem routeAssignments_nodup_keys {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) : ((p.routeAssignments totals).map Prod.fst).Nodup := by
  rw [p.routeAssignments_keys_eq]
  exact i.uniformItems_nodup

theorem routeAssignments_length_le {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i)
    (totals : FixedArrayTable i.groups.length ℝ) : (p.routeAssignments totals).length ≤ n := by
  rw [p.routeAssignments_length]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))

noncomputable def prepareOutput {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i) : RealPreparedGroupOutput i.partition := by
  let totals := FixedArrayTable.ofFn fun g => (p.groups.read g).2
  let entries := p.routeAssignments totals
  let table : FixedArrayTable n (RealGroupRoute i.groups.length) :=
    (FixedArrayTable.ofFn (fun _ => (none, 0))).patch entries
  refine ⟨totals, ?_, table, ?_⟩
  · intro g
    rw [FixedArrayTable.read_ofFn]
    exact p.total_correct g
  · intro j
    by_cases he : ∃ g, j ∈ i.partition.members g
    · rcases he with ⟨g, hg⟩
      rw [i.partition.realRoutes_group totals hg]
      apply FixedArrayTable.read_patch_at
      · intro e he hej
        rcases (p.mem_routeAssignments totals e).mp he with ⟨h, hh, heh⟩
        have hgj : h = g := by
          by_contra hne
          exact Finset.disjoint_left.mp (i.partition.disjoint h g hne) (hej ▸ hh) hg
        rw [heh, hej, hgj]
        rfl
      · refine List.mem_map.mpr ⟨(j, (some g, i.length j / totals.read g)), ?_, rfl⟩
        exact (p.mem_routeAssignments totals _).mpr ⟨g, hg, rfl⟩
    · have hj : ∀ g, j ∉ i.partition.members g := by simpa using he
      rw [i.partition.realRoutes_inactive totals hj]
      have hAbsent : j ∉ entries.map Prod.fst := by
        rintro hMem
        rcases List.mem_map.mp hMem with ⟨e, he, hej⟩
        rcases (p.mem_routeAssignments totals e).mp he with ⟨g, hg, _⟩
        exact hj g (hej ▸ hg)
      change ((FixedArrayTable.ofFn (fun _ => (none, 0) : Fin n → RealGroupRoute i.groups.length)).patch entries).read j = _
      rw [FixedArrayTable.patch_preserves _ _ _ hAbsent, FixedArrayTable.read_ofFn]

end Blotto.RealTerminalPacking
