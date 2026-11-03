import Blotto.RationalTerminalPacking
import Blotto.PreparedGroupOutput

/-! The cached rational packing feeds raw lists and stored totals directly to
routing. Every saturated field receives one coefficient, without member search.
The returned prepared table refines the retained partition's routes. -/

namespace Blotto.RationalTerminalPacking

def routeAssignments {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    List (Fin n × GroupRoute i.groups.length) :=
  (List.finRange i.groups.length).flatMap fun g =>
    (p.groups.read g).1.map fun j => (j, (some g, i.length j / (p.groups.read g).2))

theorem mem_routeAssignments {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (e : Fin n × GroupRoute i.groups.length) :
    e ∈ p.routeAssignments ↔ ∃ g, e.1 ∈ i.partition.members g ∧ e.2 = (some g, i.length e.1 / i.partition.total g) := by
  simp only [routeAssignments, List.mem_flatMap, List.mem_finRange, true_and, List.mem_map]
  constructor
  · rintro ⟨g, j, hj, he⟩
    cases he
    exact ⟨g, (p.mem_group g j).mp hj, by rw [p.total_correct]⟩
  · rintro ⟨g, hj, he⟩
    refine ⟨g, e.1, (p.mem_group g e.1).mpr hj, ?_⟩
    rw [p.total_correct]
    cases e
    simp_all

theorem routeAssignments_keys_eq {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    p.routeAssignments.map Prod.fst = i.uniformItems := by
  have hGroups : (List.finRange i.groups.length).map (fun g => (p.groups.read g).1) = i.groups := by
    simp only [p.members_correct, List.map_get_finRange]
  simp only [routeAssignments, List.map_flatMap, List.map_map, Function.comp_def, List.map_id']
  change (List.finRange i.groups.length).flatMap (fun g => (p.groups.read g).1) = i.uniformItems
  rw [List.flatMap_def, hGroups]
  exact i.groups_flatten

theorem routeAssignments_length {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    p.routeAssignments.length = i.uniformItems.length := by
  have h := congrArg List.length p.routeAssignments_keys_eq
  simpa only [List.length_map] using h

theorem routeAssignments_nodup_keys {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    (p.routeAssignments.map Prod.fst).Nodup := by rw [p.routeAssignments_keys_eq]; exact i.uniformItems_nodup

theorem routeAssignments_length_le {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) :
    p.routeAssignments.length ≤ n := by
  rw [p.routeAssignments_length]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))

def prepareOutput {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i) : PreparedGroupOutput i.partition := by
  let table := (FixedArrayTable.ofFn (fun _ => (none, 0) : Fin n → GroupRoute i.groups.length)).patch p.routeAssignments
  refine ⟨table, ?_⟩
  intro j
  by_cases he : ∃ g, j ∈ i.partition.members g
  · rcases he with ⟨g, hg⟩
    rw [i.partition.routes_group hg]
    apply FixedArrayTable.read_patch_at
    · intro e he hej
      rcases (p.mem_routeAssignments e).mp he with ⟨h, hh, heh⟩
      have hgj : h = g := by
        by_contra hne
        exact List.disjoint_left.mp (i.partition.disjoint h g hne) (hej ▸ hh) hg
      rw [heh, hej, hgj]
      rfl
    · exact List.mem_map.mpr ⟨(j, (some g, i.length j / i.partition.total g)),
        (p.mem_routeAssignments _).mpr ⟨g, hg, rfl⟩, rfl⟩
  · have hj : ∀ g, j ∉ i.partition.members g := by simpa using he
    rw [i.partition.routes_inactive hj]
    have hAbsent : j ∉ p.routeAssignments.map Prod.fst := by
      rintro hMem
      rcases List.mem_map.mp hMem with ⟨e, he, hej⟩
      rcases (p.mem_routeAssignments e).mp he with ⟨g, hg, _⟩
      exact hj g (hej ▸ hg)
    change ((FixedArrayTable.ofFn (fun _ => (none, 0) : Fin n → GroupRoute i.groups.length)).patch p.routeAssignments).read j = _
    rw [FixedArrayTable.patch_preserves _ _ _ hAbsent, FixedArrayTable.read_ofFn]

end Blotto.RationalTerminalPacking
