import Blotto.RealPackedGroups
import Blotto.RealCachedGroupOutput
import Blotto.TerminalLottoLaw

/-! Terminal packing retains raw member lists and cached totals in a small
array. Finite-set membership appears only in the representation proof. -/

namespace Blotto

structure RealTerminalPacking {n : ℕ} (i : TerminalLotto n) where
  groups : FixedArrayTable i.groups.length (List (Fin n) × ℝ)
  members_correct : ∀ g, (groups.read g).1 = i.groups.get g
  total_correct : ∀ g, (groups.read g).2 = i.partition.total g

namespace RealTerminalPacking

noncomputable def prepare {n : ℕ} (i : TerminalLotto n) : RealTerminalPacking i := by
  let packed := realPackedGroups i.length i.B i.uniformItems
  have hGroups : packed.map Prod.fst = i.groups := realPackedGroups_groups _ _ _
  have hLen : packed.length = i.groups.length := by
    have h := congrArg List.length hGroups
    simpa only [List.length_map] using h
  let table : FixedArrayTable i.groups.length (List (Fin n) × ℝ) := ⟨packed.toArray, by simp [hLen]⟩
  have hMembers : ∀ g, (table.read g).1 = i.groups.get g := by
    intro g
    have hg : g.val < packed.length := by rw [hLen]; exact g.isLt
    have he := List.getElem_of_eq hGroups (by rw [hGroups]; exact g.isLt)
    rw [List.getElem_map] at he
    change (packed[g.val]'hg).1 = i.groups.get g
    exact he
  have hTotals : ∀ g, (table.read g).2 = groupLength i.length (table.read g).1 := by
    intro g
    have hg : g.val < packed.length := by rw [hLen]; exact g.isLt
    exact realPackedGroups_totals i.length i.B i.uniformItems _ (List.getElem_mem hg)
  refine ⟨table, hMembers, ?_⟩
  intro g
  rw [hTotals, hMembers]
  change groupLength i.length (i.groups.get g) = (packingPartition i.length i.length_pos i.B
    i.uniformItems i.uniformItems_nodup (fun j _ => i.length_le j)).total g
  exact (packingPartition_total i.length i.length_pos i.B i.uniformItems i.uniformItems_nodup
    (fun j _ => i.length_le j) g).symm

theorem mem_group {n : ℕ} {i : TerminalLotto n} (p : RealTerminalPacking i) (g : Fin i.groups.length) (j : Fin n) :
    j ∈ (p.groups.read g).1 ↔ j ∈ i.partition.members g := by
  rw [p.members_correct]
  change j ∈ i.groups.get g ↔ j ∈ (i.groups.get g).toFinset
  simp

end RealTerminalPacking
end Blotto
