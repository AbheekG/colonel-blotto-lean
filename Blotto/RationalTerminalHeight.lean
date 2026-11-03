import Blotto.RationalTerminalResources
import Blotto.RationalNestedSpecHeight
import Blotto.RationalHeightBudget

/-! Terminal resource decoding, its native coordinate permutation and every
nested output slot preserve fixed-depth word-height bounds. -/

namespace Blotto

namespace RationalAffineAllocation

theorem permutation_value {n : ℕ} (π : Equiv.Perm (Fin n)) (x : Fin n → ℚ) (j : Fin n) :
    (permutation π).value x j = x (π j) := by simp [permutation, value]

end RationalAffineAllocation

namespace RationalSegmentLottery

theorem HeightAt.mapped_permutation {n k : ℕ} {l : RationalSegmentLottery n k} {s : ℕ}
    (h : l.HeightAt s) (π : Equiv.Perm (Fin n)) : (l.mapped (RationalAffineAllocation.permutation π)).HeightAt s := by
  constructor
  · exact h.1
  · intro slot j
    simpa only [mapped, RationalAffineAllocation.permutation_value] using h.2 slot (π j)

end RationalSegmentLottery

namespace RationalTerminalResources

def FieldsHeight (i : RationalTerminalResources) (s : ℕ) : Prop :=
  RationalHeight i.M s ∧ (∀ j, RationalHeight (i.long j) s) ∧
    (∀ j, RationalHeight (i.short j) s) ∧ ∀ j, RationalHeight (i.resource j) s

theorem FieldsHeight.mono {i : RationalTerminalResources} {s t : ℕ} (h : i.FieldsHeight s) (hst : s ≤ t) :
    i.FieldsHeight t := ⟨h.1.mono hst, fun j => (h.2.1 j).mono hst,
      fun j => (h.2.2.1 j).mono hst, fun j => (h.2.2.2 j).mono hst⟩

theorem FieldsHeight.endpoint {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s) (j : Fin 3) :
    RationalHeight (i.endpoint j) s := by
  unfold RationalTerminalResources.endpoint
  split
  · exact h.2.1 j
  · exact h.2.2.1 j

theorem FieldsHeight.input {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s) :
    i.input.FieldsHeight (expressionHeightBudget s 2) := by
  have hLong : RationalHeight (i.long i.focus) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using h.2.1 i.focus
  have hShort : RationalHeight (i.short i.focus) (expressionHeightBudget s 0) := by
    simpa only [expressionHeightBudget_zero] using h.2.2.1 i.focus
  have hCapacity := hLong.sub_level hShort
  have hResource := (h.2.2.2 i.focus).mono (expressionHeightBudget_ge_input s 1)
  have hWeight := hResource.div_level hCapacity
  have hm := expressionHeightBudget_ge_input s 2
  exact ⟨h.1.mono hm, (h.endpoint _).mono hm, (h.endpoint _).mono hm,
    (h.2.1 _).mono hm, (h.2.2.1 _).mono hm, hWeight⟩

theorem FieldsHeight.profile {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin K → Bool) :
    (i.profile K bits).HeightAt (expressionHeightBudget (max s (K + 2)) 47) := by
  let w := max s (K + 2)
  have hInput := (h.mono (le_max_left s (K + 2))).input
  have hm := expressionHeightBudget_ge_input w 2
  have hTable := hInput.profile (hs.trans ((le_max_left s (K + 2)).trans hm)) K bits
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hTable
  exact hTable.mapped_permutation i.permutation

theorem FieldsHeight.point {i : RationalTerminalResources} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (slot : Fin 18) (j : Fin 3) :
    RationalHeight ((i.profile K outerBits).point K slot scalarBits j)
      (expressionHeightBudget (max s (K + 2)) 50) := by
  have hm := expressionHeightBudget_ge_input (max s (K + 2)) 47
  have hPoint := (h.profile hs K outerBits).point (hs.trans ((le_max_left s (K + 2)).trans hm)) K slot scalarBits j
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hPoint
  exact hPoint

end RationalTerminalResources
end Blotto
