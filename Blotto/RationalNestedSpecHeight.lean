import Blotto.RationalNestedProfileHeight
import Blotto.RationalNestedSpec
import Blotto.RationalThreeSpecHeight

/-! Every finite nested slot and dyadic point has a linear word-size bound.
Ordering and q=0/1 are included. The maintained positive-length scope remains
unchanged; this file establishes size, not a complete runtime/space contract. -/

namespace Blotto

namespace RationalThreeSpecCode

theorem descriptor_height (i : RationalThreeSpec) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    i.segmentLottery.HeightAt (expressionHeightBudget s 18) := by
  constructor
  · intro slot; exact weight_height i slot s hs hEnv
  · intro slot j
    have h := endpoint_heights i slot j s hs hEnv
    have hm := expressionHeightBudget_mono s (by decide : 4 ≤ 18)
    exact ⟨h.1.mono hm, h.2.mono hm⟩

end RationalThreeSpecCode

namespace RationalNestedSpec

def FieldsHeight (i : RationalNestedSpec) (s : ℕ) : Prop :=
  RationalHeight i.M s ∧ RationalHeight i.a s ∧ RationalHeight i.d s ∧
    RationalHeight i.c s ∧ RationalHeight i.t s ∧ RationalHeight i.q s

theorem FieldsHeight.mono {i : RationalNestedSpec} {s t : ℕ} (h : i.FieldsHeight s)
    (hst : s ≤ t) : i.FieldsHeight t :=
  ⟨h.1.mono hst, h.2.1.mono hst, h.2.2.1.mono hst,
    h.2.2.2.1.mono hst, h.2.2.2.2.1.mono hst, h.2.2.2.2.2.mono hst⟩

theorem FieldsHeight.interiorInput {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hq0 : 0 < i.q) (hq1 : i.q < 1) : (i.interiorInput hq0 hq1).FieldsHeight s :=
  ⟨h.1, h.2.1.min h.2.2.1, h.2.1.max h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2⟩

theorem FieldsHeight.longInput {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hq : i.q = 0) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment (i.longInput hq)).read j) s := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.longInput] using h.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.longInput] using h.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.longInput] using h.2.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.longInput] using h.2.2.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.longInput] using hOne

theorem FieldsHeight.shortInput {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hq : i.q = 1) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment (i.shortInput hq)).read j) s := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.shortInput] using h.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.shortInput] using h.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.shortInput] using h.2.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.shortInput] using h.2.2.2.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, RationalNestedSpec.shortInput] using hOne

theorem FieldsHeight.profile {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (bits : Fin K → Bool) :
    (i.profile K bits).HeightAt (expressionHeightBudget (max s (K + 2)) 45) := by
  let w := max s (K + 2)
  have hFields := h.mono (le_max_left s (K + 2))
  have hw : 2 ≤ w := hs.trans (le_max_left _ _)
  have hK : K + 2 ≤ w := le_max_right _ _
  have hm := expressionHeightBudget_mono w (by decide : 18 ≤ 45)
  unfold RationalNestedSpec.profile
  dsimp only
  split
  · rename_i hq0
    have hTable := RationalThreeSpecCode.descriptor_height (i.longInput hq0) w hw (hFields.longInput hw hq0)
    exact (hTable.padRight (hw.trans (expressionHeightBudget_ge_input w 18)) 9 0).mono hm
  · split
    · rename_i hq1
      have hTable := RationalThreeSpecCode.descriptor_height (i.shortInput hq1) w hw (hFields.shortInput hw hq1)
      exact (hTable.padRight (hw.trans (expressionHeightBudget_ge_input w 18)) 9 0).mono hm
    · rename_i hq0 hq1
      have hTable := (hFields.interiorInput (lt_of_le_of_ne i.q_nonneg (Ne.symm hq0))
        (lt_of_le_of_ne i.q_le hq1)).profile hw K bits
      rw [max_eq_left hK] at hTable
      split
      · exact hTable
      · exact hTable.swapFirst

theorem FieldsHeight.point {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (slot : Fin 18) (j : Fin 3) :
    RationalHeight ((i.profile K outerBits).point K slot scalarBits j)
      (expressionHeightBudget (max s (K + 2)) 48) := by
  have hTable := h.profile hs K outerBits
  have hm := expressionHeightBudget_ge_input (max s (K + 2)) 45
  have hK := (le_max_right s (K + 2)).trans hm
  have hPoint := hTable.point (hs.trans ((le_max_left _ _).trans hm)) K slot scalarBits j
  rw [max_eq_left hK, expressionHeightBudget_comp] at hPoint
  exact hPoint

theorem FieldsHeight.point_wordWidth {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (slot : Fin 18) (j : Fin 3) :
    rationalWordWidth ((i.profile K outerBits).point K slot scalarBits j) ≤
      1 + 2 * expressionHeightBudget (max s (K + 2)) 48 :=
  rationalWordWidth_of_height (h.point hs K outerBits scalarBits slot j)

theorem FieldsHeight.point_wordWidth_linear {i : RationalNestedSpec} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (K : ℕ) (outerBits scalarBits : Fin K → Bool) (slot : Fin 18) (j : Fin 3) :
    rationalWordWidth ((i.profile K outerBits).point K slot scalarBits j) ≤ 2 ^ 49 * (s + K + 3) := by
  have hWord := h.point_wordWidth hs K outerBits scalarBits slot j
  norm_num [expressionHeightBudget] at hWord ⊢
  omega

end RationalNestedSpec
end Blotto
