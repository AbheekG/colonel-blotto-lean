import Blotto.RationalPackedGroups
import Blotto.RationalTerminalLotto
import Blotto.FixedArrayTable

/-! Native terminal packing stores raw member lists and closed-group sums in
one small array. Refinement identifies both with the retained partition. -/

namespace Blotto

structure RationalTerminalPacking {n : ℕ} (i : RationalTerminalLotto n) where
  groups : FixedArrayTable i.groups.length (List (Fin n) × ℚ)
  members_correct : ∀ g, (groups.read g).1 = i.groups.get g
  total_correct : ∀ g, (groups.read g).2 = i.partition.total g

namespace RationalTerminalPacking

def prepare {n : ℕ} (i : RationalTerminalLotto n) : RationalTerminalPacking i := by
  let packed := rationalPackedGroups i.length i.B i.uniformItems
  have hGroups : packed.map Prod.fst = i.groups := rationalPackedGroups_groups _ _ _
  have hLen : packed.length = i.groups.length := by
    have h := congrArg List.length hGroups
    simpa only [List.length_map] using h
  let table : FixedArrayTable i.groups.length (List (Fin n) × ℚ) := ⟨packed.toArray, by simp [hLen]⟩
  have hMembers : ∀ g, (table.read g).1 = i.groups.get g := by
    intro g
    have hg : g.val < packed.length := by rw [hLen]; exact g.isLt
    have he := List.getElem_of_eq hGroups (by rw [hGroups]; exact g.isLt)
    rw [List.getElem_map] at he
    change (packed[g.val]'hg).1 = i.groups.get g
    exact he
  have hTotals : ∀ g, (table.read g).2 = rationalGroupLength i.length (table.read g).1 := by
    intro g
    have hg : g.val < packed.length := by rw [hLen]; exact g.isLt
    exact rationalPackedGroups_totals i.length i.B i.uniformItems _ (List.getElem_mem hg)
  refine ⟨table, hMembers, ?_⟩
  intro g
  rw [hTotals, hMembers]
  exact (i.partition.total_eq g).symm

theorem mem_group {n : ℕ} {i : RationalTerminalLotto n} (p : RationalTerminalPacking i)
    (g : Fin i.groups.length) (j : Fin n) : j ∈ (p.groups.read g).1 ↔ j ∈ i.partition.members g := by
  rw [p.members_correct]
  rfl

end RationalTerminalPacking
end Blotto
