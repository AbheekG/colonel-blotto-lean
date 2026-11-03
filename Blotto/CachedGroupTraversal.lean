import Blotto.PreparedGroupOutput
import Blotto.RationalTerminalLotto

/-! The prepared route table writes each saturated field exactly once.
These traversal counts are distinct from primitive-time/ownership bounds. -/

namespace Blotto

namespace RationalProportionalGroups

theorem routeAssignments_keys_eq {n m : ℕ} (G : RationalProportionalGroups n m) :
    G.routeAssignments.map Prod.fst = ((List.finRange m).map G.members).flatten := by
  simp [routeAssignments, List.map_map, List.flatMap_def, Function.comp_def]

end RationalProportionalGroups

namespace RationalTerminalLotto

theorem routeAssignments_keys {n : ℕ} (i : RationalTerminalLotto n) :
    i.partition.routeAssignments.map Prod.fst = i.uniformItems := by
  rw [RationalProportionalGroups.routeAssignments_keys_eq]
  change ((List.finRange i.groups.length).map i.groups.get).flatten = i.uniformItems
  rw [List.map_get_finRange, i.groups_flatten]

theorem routeAssignments_nodup_keys {n : ℕ} (i : RationalTerminalLotto n) :
    (i.partition.routeAssignments.map Prod.fst).Nodup := by
  rw [i.routeAssignments_keys]
  exact i.uniformItems_nodup

theorem routeAssignments_length {n : ℕ} (i : RationalTerminalLotto n) :
    i.partition.routeAssignments.length = i.uniformItems.length := by
  have he := congrArg List.length i.routeAssignments_keys
  simpa only [List.length_map] using he

theorem routeAssignments_length_le {n : ℕ} (i : RationalTerminalLotto n) :
    i.partition.routeAssignments.length ≤ n := by
  rw [i.routeAssignments_length]
  exact (List.length_filter_le _ _).trans_eq (List.length_finRange (n := n))

end RationalTerminalLotto
end Blotto
