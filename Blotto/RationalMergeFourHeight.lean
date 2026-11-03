import Blotto.RationalMergeFour
import Blotto.RationalAffineHeight
import Blotto.RationalFourGluingHeight

/-! Heights for native four-uniform merge/split descriptors and the scaled
uniform continuation in the atom-conditioning case. -/

namespace Blotto

namespace RationalMergeFourInput

def FieldsHeight (i : RationalMergeFourInput) (s : ℕ) : Prop :=
  RationalHeight i.B s ∧ RationalHeight i.l0 s ∧ RationalHeight i.l1 s ∧ RationalHeight i.l2 s ∧ RationalHeight i.l3 s

theorem FieldsHeight.child_environment {i : RationalMergeFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment i.childSpec).read j) (expressionHeightBudget s 1) := by
  have hm := expressionHeightBudget_ge_input s 1
  have hL0 : RationalHeight i.l0 (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.1
  have hL1 : RationalHeight i.l1 (expressionHeightBudget s 0) := by simpa only [expressionHeightBudget_zero] using h.2.2.1
  have hPair := hL0.add_level hL1
  have hOne : RationalHeight (1 : ℚ) (expressionHeightBudget s 1) :=
    (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm)
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, childSpec] using h.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, childSpec] using hPair
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, childSpec] using h.2.2.2.1.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, childSpec] using h.2.2.2.2.mono hm
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, childSpec] using hOne

theorem FieldsHeight.segmentLottery {i : RationalMergeFourInput} {s : ℕ} (h : i.FieldsHeight s) (hs : 2 ≤ s) :
    i.segmentLottery.HeightAt (expressionHeightBudget s 22) := by
  have hChild := RationalThreeSpecCode.descriptor_height i.childSpec _
    (hs.trans (expressionHeightBudget_ge_input s 1)) (h.child_environment hs)
  rw [expressionHeightBudget_comp] at hChild
  have hm := expressionHeightBudget_ge_input s 19
  have hMapped := hChild.mapped_split i.l0 i.l1 (h.2.1.mono hm) (h.2.2.1.mono hm)
  rw [expressionHeightBudget_comp] at hMapped
  exact hMapped

end RationalMergeFourInput

namespace RationalFourInput

theorem FieldsHeight.smallUniformInput {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.smallUniformInput hcase).FieldsHeight (expressionHeightBudget s 13) := by
  rw [i.smallUniformInput_refines]
  have hScale : RationalHeight i.scaleFraction (expressionHeightBudget s 12) := h.scalar hs 5
  have hm12 := expressionHeightBudget_ge_input s 12
  have hm13 := expressionHeightBudget_ge_input s 13
  exact ⟨h.1.mono hm13, hScale.mul_level (h.2.1.mono hm12),
    hScale.mul_level (h.2.2.1.mono hm12), hScale.mul_level (h.2.2.2.1.mono hm12), h.2.2.2.2.1.mono hm13⟩

theorem FieldsHeight.smallUniformLottery {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) :
    (i.smallUniformLottery hcase).HeightAt (expressionHeightBudget s 35) := by
  have hTable := (h.smallUniformInput hs hcase).segmentLottery (hs.trans (expressionHeightBudget_ge_input s 13))
  rw [expressionHeightBudget_comp] at hTable
  exact hTable

theorem FieldsHeight.smallUniformPoint {i : RationalFourInput} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hcase : i.w < (1 - i.p) * i.ell) (K : ℕ) (bits : Fin K → Bool) (slot : Fin 9) (j : Fin 4) :
    RationalHeight ((i.smallUniformLottery hcase).point K slot bits j) (expressionHeightBudget (max s (K + 2)) 38) := by
  have hm := expressionHeightBudget_ge_input (max s (K + 2)) 35
  have hTable := (h.mono (le_max_left s (K + 2))).smallUniformLottery (hs.trans (le_max_left _ _)) hcase
  have hPoint := hTable.point (hs.trans ((le_max_left s (K + 2)).trans hm)) K slot bits j
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm), expressionHeightBudget_comp] at hPoint
  exact hPoint

end RationalFourInput
end Blotto
