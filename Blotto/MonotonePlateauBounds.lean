import Blotto.MonotoneResourceCuts

/-! Computed cuts identify an entire decoded-resource plateau, retaining all
duplicate labels. Plateau endpoints and cumulative crossings support the actual
implicit upper-guide builder; the specific Farey decoder is still separate. -/

namespace Blotto.MonotoneResourceCuts

def plateauFirst (C : ℕ) (decode : ℕ → ℚ) (code : ℕ) : ℕ := (weak C decode (decode code)).1
def plateauEnd (C : ℕ) (decode : ℕ → ℚ) (code : ℕ) : ℕ := (strict C decode (decode code)).1 - 1

theorem plateauFirst_le (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code : ℕ) (hc : code ≤ C) : plateauFirst C decode code ≤ code :=
  ((weak_contract C decode hm (decode code)).2 code hc).mp le_rfl

theorem code_lt_strict_self (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code : ℕ) (hc : code ≤ C) : code < (strict C decode (decode code)).1 := by
  have hs := (strict_contract C decode hm (decode code)).2 code hc
  by_contra hn
  exact (lt_irrefl _ ((hs.mpr (by omega))))

theorem plateauEnd_bounds (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code : ℕ) (hc : code ≤ C) : code ≤ plateauEnd C decode code ∧ plateauEnd C decode code ≤ C := by
  have hp := code_lt_strict_self C decode hm code hc
  have hu := (strict_contract C decode hm (decode code)).1
  unfold plateauEnd
  omega

theorem plateau_membership (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code label : ℕ) (hc : code ≤ C) (hl : label ≤ C) :
    decode label = decode code ↔ plateauFirst C decode code ≤ label ∧ label ≤ plateauEnd C decode code := by
  have hw := (weak_contract C decode hm (decode code)).2 label hl
  have hs := (strict_contract C decode hm (decode code)).2 label hl
  have hp := code_lt_strict_self C decode hm code hc
  unfold plateauFirst plateauEnd
  constructor
  · intro he
    constructor
    · exact hw.mp (by rw [he])
    · have hn : ¬(strict C decode (decode code)).1 ≤ label := by
        intro hn
        have ht := hs.mpr hn
        rw [he] at ht
        exact lt_irrefl _ ht
      omega
  · intro he
    have hlo := hw.mpr he.1
    have hhi : decode label ≤ decode code := by
      by_contra hn
      have hc' := hs.mp (lt_of_not_ge hn)
      omega
    exact le_antisymm hhi hlo

theorem plateauFirst_value (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code : ℕ) (hc : code ≤ C) : decode (plateauFirst C decode code) = decode code := by
  have hf := plateauFirst_le C decode hm code hc
  apply (plateau_membership C decode hm code _ hc (hf.trans hc)).mpr
  exact ⟨le_rfl, hf.trans (plateauEnd_bounds C decode hm code hc).1⟩

theorem plateauEnd_value (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code : ℕ) (hc : code ≤ C) : decode (plateauEnd C decode code) = decode code := by
  have hb := plateauEnd_bounds C decode hm code hc
  apply (plateau_membership C decode hm code _ hc hb.2).mpr
  exact ⟨(plateauFirst_le C decode hm code hc).trans hb.1, le_rfl⟩

theorem after_plateau_strict (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code label : ℕ) (hc : code ≤ C) (hl : label ≤ C)
    (ha : plateauEnd C decode code < label) : decode code < decode label := by
  apply ((strict_contract C decode hm (decode code)).2 label hl).mpr
  have hp := code_lt_strict_self C decode hm code hc
  unfold plateauEnd at ha
  omega

theorem before_plateau_strict (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (code label : ℕ) (hl : label ≤ C) (ha : label < plateauFirst C decode code) :
    decode label < decode code := by
  have hw := (weak_contract C decode hm (decode code)).2 label hl
  apply lt_of_not_ge
  intro he
  have ht := hw.mp he
  exact Nat.not_le_of_lt ha ht

theorem separated_plateau_progress (C : ℕ) (decode : ℕ → ℚ) (hm : MonotoneDecode C decode)
    (start cross : ℕ) (hStart : start ≤ C) (hCross : cross ≤ C)
    (hAfter : plateauEnd C decode start < cross) :
    start < plateauFirst C decode cross ∧ decode start < decode (plateauFirst C decode cross) := by
  have hResource := after_plateau_strict C decode hm start cross hStart hCross hAfter
  have hValue := plateauFirst_value C decode hm cross hCross
  have hBound := (plateauFirst_le C decode hm cross hCross).trans hCross
  have hFirst : start < plateauFirst C decode cross := by
    by_contra hn
    have he := hm (plateauFirst C decode cross) start (by omega) hStart
    rw [hValue] at he
    exact not_lt_of_ge he hResource
  exact ⟨hFirst, by rw [hValue]; exact hResource⟩

end Blotto.MonotoneResourceCuts
