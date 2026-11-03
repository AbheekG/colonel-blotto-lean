import Blotto.BinaryCarryCounter

/-! The Boolean counter stays canonical and occupies logarithmically many
cells. Its final natural decoder sees only this counter, never the input word. -/

namespace Blotto.BinaryCarryCounter

def Canonical : List Bool → Prop
  | [] => True
  | b :: rest => Canonical rest ∧ (rest = [] → b = true)

theorem increment_ne_nil (bits : List Bool) : increment bits ≠ [] := by
  cases bits with
  | nil => simp [increment]
  | cons b rest => cases b <;> simp [increment]

theorem increment_canonical (bits : List Bool) (h : Canonical bits) : Canonical (increment bits) := by
  induction bits with
  | nil => exact ⟨trivial, fun _ => rfl⟩
  | cons b rest ih =>
    cases b
    · exact ⟨h.1, fun _ => rfl⟩
    · exact ⟨ih h.1, fun hn => False.elim (increment_ne_nil rest hn)⟩

theorem count_canonical {α : Type*} (items : List α) (counter : List Bool) (h : Canonical counter) :
    Canonical (count items counter) := by
  induction items generalizing counter with
  | nil => exact h
  | cons item rest ih => exact ih (increment counter) (increment_canonical counter h)

theorem value_lower (bits : List Bool) (h : Canonical bits) (hne : bits ≠ []) :
    2 ^ (bits.length - 1) ≤ value bits := by
  induction bits with
  | nil => exact False.elim (hne rfl)
  | cons b rest ih =>
    cases rest with
    | nil =>
      have hb : b = true := h.2 rfl
      subst b
      exact Nat.le_refl 1
    | cons c rest =>
      have ht := ih h.1 (by simp)
      change 2 ^ (rest.length + 1) ≤ 2 * value (c :: rest) + if b then 1 else 0
      simp only [List.length_cons, Nat.add_sub_cancel] at ht
      rw [pow_succ]
      omega

theorem canonical_length_bound (bits : List Bool) (h : Canonical bits) : bits.length ≤ binaryWordWidth (value bits) := by
  by_cases hn : bits = []
  · subst bits
    exact Nat.zero_le _
  · have hLow := value_lower bits h hn
    have hPos : 0 < value bits := lt_of_lt_of_le (Nat.two_pow_pos _) hLow
    have hLog := (Nat.le_log2 (ne_of_gt hPos)).mpr hLow
    have hLen : 0 < bits.length := List.length_pos_iff.mpr hn
    unfold binaryWordWidth
    omega

theorem countFromOne_length {α : Type*} (items : List α) :
    (count items [true]).length ≤ binaryWordWidth (items.length + 1) := by
  have h := canonical_length_bound (count items [true]) (count_canonical items [true] ⟨trivial, fun _ => rfl⟩)
  rw [count_value] at h
  change (count items [true]).length ≤ binaryWordWidth (1 + items.length) at h
  simpa only [Nat.add_comm] using h

end Blotto.BinaryCarryCounter
