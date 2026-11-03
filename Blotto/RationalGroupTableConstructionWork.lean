import Blotto.WeightedArrayCopyWork
import Blotto.RationalTerminalPacketMetadata

/-! Construction of the cached group array retains member-label and stored
total payloads, full-prefix copying and the actual table loop. At most three
groups give a linear payload envelope. Physical pointers/ownership are separate. -/

namespace Blotto.RationalTerminalLotto

def groupEntryPayloadWordWidth {n : ℕ} (entry : List (Fin n) × ℚ) : ℕ :=
  1 + (entry.1.map (fun j => binaryWordWidth (j.val + 1))).sum + rationalWordWidth entry.2

def groupEntryPayloadWidth (n s : ℕ) : ℕ := 1 + n * binaryWordWidth (n + 4) + (1 + 2 * s)

theorem packedGroup_count {n : ℕ} (i : RationalTerminalLotto n) :
    (rationalPackedGroups i.length i.B i.uniformItems).length ≤ 3 := by
  have he := congrArg List.length (rationalPackedGroups_groups i.length i.B i.uniformItems)
  have hEq : (rationalPackedGroups i.length i.B i.uniformItems).length = i.groups.length := by
    simpa only [List.length_map, groups] using he
  rw [hEq]
  rcases i.groups_count with h | h <;> omega

theorem OnLattice.packedGroup_payloadWidth {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hWidth : binaryWordWidth D ≤ s)
    (entry : List (Fin n) × ℚ) (he : entry ∈ rationalPackedGroups i.length i.B i.uniformItems) :
    groupEntryPayloadWordWidth entry ≤ groupEntryPayloadWidth n s := by
  have hMem : entry.1 ∈ i.groups := by
    change entry.1 ∈ rationalGreedyGroups i.length i.B i.uniformItems
    rw [← rationalPackedGroups_groups]
    exact List.mem_map.mpr ⟨entry, he, rfl⟩
  have hNodup := (List.nodup_flatten.mp i.groups_nodup).1 entry.1 hMem
  have hLength : entry.1.length ≤ n := by simpa only [Fintype.card_fin] using hNodup.length_le_card
  have hLabels : (entry.1.map (fun j => binaryWordWidth (j.val + 1))).sum ≤ n * binaryWordWidth (n + 4) := by
    calc
      _ ≤ (entry.1.map (fun _ => binaryWordWidth (n + 4))).sum :=
        List.sum_le_sum (fun j _ => binaryWordWidth_mono (by omega : j.val + 1 ≤ n + 4))
      _ = entry.1.length * binaryWordWidth (n + 4) := by simp
      _ ≤ _ := Nat.mul_le_mul_right _ hLength
  have hTotal := rationalPackedGroups_totals i.length i.B i.uniformItems entry he
  have hBounds := i.groups_bounds entry.1 hMem
  have hLat : OnRationalLattice D entry.2 := by
    rw [hTotal]
    exact OnRationalLattice.list_sum i.length entry.1 (fun j _ => h.1 j)
  have hTotalHeight := rationalHeight_unit_lattice hD hLat
    (show 0 ≤ entry.2 ∧ entry.2 ≤ 1 by rw [hTotal]; exact ⟨hBounds.2.1.le, hBounds.2.2.trans hB⟩)
  have hTotalWords := rationalWordWidth_of_height (hTotalHeight.mono hWidth)
  unfold groupEntryPayloadWordWidth groupEntryPayloadWidth
  omega

def groupTableConstructionWork {n : ℕ} (i : RationalTerminalLotto n) (primitive : ℕ → ℕ) : ℕ :=
  let packed := rationalPackedGroups i.length i.B i.uniformItems
  wordArrayCopyWork groupEntryPayloadWordWidth packed 0 + indexedLoopMetadataBitWork primitive 0 packed.length

def groupTableConstructionBound (c n s : ℕ) : ℕ :=
  18 * groupEntryPayloadWidth n s + indexedLoopMetadataBound c 3

theorem groupTableConstructionBound_mono_fields (c s : ℕ) : Monotone (fun n => groupTableConstructionBound c n s) := by
  intro a b hab
  have hWidth := binaryWordWidth_mono (Nat.add_le_add_right hab 4)
  unfold groupTableConstructionBound groupEntryPayloadWidth
  dsimp only
  gcongr

theorem OnLattice.groupTableConstructionWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w) :
    i.groupTableConstructionWork primitive ≤ groupTableConstructionBound c n s := by
  let packed := rationalPackedGroups i.length i.B i.uniformItems
  have hCount := i.packedGroup_count
  have hCopy := wordArrayCopyWork_uniform_bound groupEntryPayloadWordWidth packed (groupEntryPayloadWidth n s)
    (fun entry he => h.packedGroup_payloadWidth hD hB s hWidth entry he)
  have hCountPrice : 2 * packed.length * packed.length ≤ 18 := by dsimp [packed]; nlinarith
  have hCopy18 := hCopy.trans (Nat.mul_le_mul_right _ hCountPrice)
  have hLoop := (indexedLoopMetadataBitWork_bound primitive c hPrimitive packed.length).trans
    (indexedLoopMetadataBound_mono c hCount)
  exact Nat.add_le_add hCopy18 hLoop

end Blotto.RationalTerminalLotto
