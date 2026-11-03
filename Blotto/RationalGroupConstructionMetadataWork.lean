import Blotto.RationalFourConstructionMetadataWork
import Blotto.RationalTerminalGroupCompleteProcessing

/-! Runtime terminal-factory metadata is zero on branches with no nested
resource continuation. The mixed three-group branch retains the four-variable
observer at its actual cap and position. Entry construction remains separate. -/

namespace Blotto.RationalMixedGroupSpec

noncomputable def runtimeConstructionMetadataWork {m : ℕ} (i : RationalMixedGroupSpec m)
    (hm : m = 2 ∨ m = 3) (primitive : ℕ → ℕ) (c K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ := by
  by_cases h2 : m = 2
  · exact 0
  · have h3 : m = 3 := hm.resolve_left h2
    subst m
    exact i.fourInput.runtimeConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos

theorem FieldsHeight.runtimeConstructionMetadataWork_bound {m : ℕ} {i : RationalMixedGroupSpec m} {s : ℕ}
    (h : i.FieldsHeight s) (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (primitive : ℕ → ℕ) (c : ℕ)
    (hPrimitive : ∀ w, primitive w ≤ c * w) (K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.runtimeConstructionMetadataWork hm primitive c K outerBits scalarBits N bits pos hpos ≤
      2592 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max s (K + 2)) 21) K := by
  rcases hm with rfl | rfl
  · exact Nat.zero_le _
  · exact h.fourInput.runtimeConstructionMetadataWork_bound hs primitive c hPrimitive K outerBits scalarBits N bits pos hpos

end Blotto.RationalMixedGroupSpec

namespace Blotto.RationalTerminalLotto

noncomputable def runtimeConstructionMetadataWork {n : ℕ} (i : RationalTerminalLotto n)
    (primitive : ℕ → ℕ) (c K : ℕ) (outerBits scalarBits : Fin K → Bool)
    (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) : ℕ :=
  let packed := RationalTerminalPacking.prepare i
  match h : i.pivot with
  | none => 0
  | some pivot => (packed.mixedSpec pivot (i.pivot_some h)).runtimeConstructionMetadataWork
      i.groups_count primitive c K outerBits scalarBits N bits pos hpos

theorem OnLattice.runtimeConstructionMetadataWork_bound {n : ℕ} {i : RationalTerminalLotto n} {D : ℕ}
    (h : i.OnLattice D) (hD : 0 < D) (hB : i.B ≤ 1) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.B s) (hWidth : binaryWordWidth D ≤ s)
    (primitive : ℕ → ℕ) (c : ℕ) (hPrimitive : ∀ w, primitive w ≤ c * w)
    (K : ℕ) (outerBits scalarBits : Fin K → Bool) (N : ℕ) (bits : Fin N → Bool) (pos : ℕ) (hpos : pos ≤ N) :
    i.runtimeConstructionMetadataWork primitive c K outerBits scalarBits N bits pos hpos ≤
      2592 * RationalTerminalResources.profileConstructionMetadataBound c
        (expressionHeightBudget (max s (K + 2)) 22) K := by
  let w := max s (K + 2)
  have hm := expressionHeightBudget_ge_input w 1
  have hw := hs.trans (le_max_left s (K + 2))
  unfold runtimeConstructionMetadataWork
  dsimp only
  split
  · exact Nat.zero_le _
  · rename_i pivot hSome
    rw [RationalTerminalPacking.mixedSpec_eq]
    have hp := (h.mixedSpec hD hB w (hBudget.mono (le_max_left _ _))
      (hWidth.trans (le_max_left _ _)) pivot (i.pivot_some hSome)).runtimeConstructionMetadataWork_bound
      (hw.trans hm) i.groups_count primitive c hPrimitive K outerBits scalarBits N bits pos hpos
    rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hp
    exact hp

end Blotto.RationalTerminalLotto
