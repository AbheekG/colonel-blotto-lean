import Blotto.RationalGroupPrograms
import Blotto.RationalFourSpecHeight
import Blotto.RationalNestedSpecHeight

/-! Both native terminal group programs expose bounded rational coordinates
on all specification leaves. These are output-size certificates, independent
of the original field count. -/

namespace Blotto

namespace RationalUniformGroupSpec

def FieldsHeight {m : ℕ} (i : RationalUniformGroupSpec m) (s : ℕ) : Prop :=
  RationalHeight i.B s ∧ ∀ j, RationalHeight (i.length j) s

theorem FieldsHeight.mono {m : ℕ} {i : RationalUniformGroupSpec m} {s t : ℕ} (h : i.FieldsHeight s)
    (hst : s ≤ t) : i.FieldsHeight t := ⟨h.1.mono hst, fun j => (h.2 j).mono hst⟩

theorem FieldsHeight.three_environment {i : RationalUniformGroupSpec 3} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) : ∀ j, RationalHeight ((RationalThreeSpecCode.environment i.threeInput).read j) s := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2 0
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2 1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2 2
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using hOne

theorem FieldsHeight.lottery {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) : (i.lottery hm).HeightAt (expressionHeightBudget s 18) := by
  rcases hm with rfl | rfl
  · have hZero : RationalHeight (0 : ℚ) s := (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hs
    have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
    have hPair : (rationalComplementaryPair i.B).HeightAt s := by
      constructor
      · intro slot; exact hOne
      · intro slot j
        fin_cases j
        · exact ⟨hZero, h.1⟩
        · exact ⟨h.1, hZero⟩
    exact (hPair.padRight hs 8 0).mono (expressionHeightBudget_ge_input s 18)
  · exact RationalThreeSpecCode.descriptor_height _ s hs (h.three_environment hs)

theorem FieldsHeight.program_leaves {m : ℕ} {i : RationalUniformGroupSpec m} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (K : ℕ) (bits : Fin K → Bool) :
    ((i.program hm K bits).machine.specification (i.program hm K bits).start).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 21)) := by
  have hW := h.mono (le_max_left s (K + 2))
  have hsW := hs.trans (le_max_left s (K + 2))
  apply RationalSegmentLottery.machine_forLeaves
  intro slot j
  have hm18 := expressionHeightBudget_ge_input (max s (K + 2)) 18
  have hPoint := (hW.lottery hsW hm).point (hsW.trans hm18) K slot bits j
  rw [max_eq_left ((le_max_right s (K + 2)).trans hm18), expressionHeightBudget_comp] at hPoint
  exact hPoint

end RationalUniformGroupSpec

namespace RationalMixedGroupSpec

def FieldsHeight {m : ℕ} (i : RationalMixedGroupSpec m) (s : ℕ) : Prop :=
  RationalHeight i.B s ∧ (∀ j, RationalHeight (i.length j) s) ∧ RationalHeight i.ell s ∧ RationalHeight i.p s

theorem FieldsHeight.mono {m : ℕ} {i : RationalMixedGroupSpec m} {s t : ℕ} (h : i.FieldsHeight s)
    (hst : s ≤ t) : i.FieldsHeight t :=
  ⟨h.1.mono hst, fun j => (h.2.1 j).mono hst, h.2.2.1.mono hst, h.2.2.2.mono hst⟩

theorem FieldsHeight.three_environment {i : RationalMixedGroupSpec 2} {s : ℕ} (h : i.FieldsHeight s) :
    ∀ j, RationalHeight ((RationalThreeSpecCode.environment i.threeInput).read j) s := by
  intro j
  fin_cases j
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2.1 0
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2.1 1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2.2.1
  · simpa [RationalThreeSpecCode.environment, FixedArrayTable.read_ofFn, threeInput] using h.2.2.2

theorem FieldsHeight.fourInput {i : RationalMixedGroupSpec 3} {s : ℕ} (h : i.FieldsHeight s) :
    i.fourInput.FieldsHeight s := h

theorem FieldsHeight.program_leaves {m : ℕ} {i : RationalMixedGroupSpec m} {s : ℕ} (h : i.FieldsHeight s)
    (hs : 2 ≤ s) (hm : m = 2 ∨ m = 3) (K : ℕ) (outerBits scalarBits : Fin K → Bool) :
    ((i.program hm K outerBits scalarBits).machine.specification (i.program hm K outerBits scalarBits).start).decode.ForLeaves
      (fun x => ∀ j, RationalHeight (x j) (expressionHeightBudget (max s (K + 2)) 72)) := by
  rcases hm with rfl | rfl
  · apply RationalSegmentLottery.machine_forLeaves
    intro slot j
    have hW := h.mono (le_max_left s (K + 2))
    have hw := hs.trans (le_max_left s (K + 2))
    have hPoint := (RationalThreeSpecCode.descriptor_height _ _ hw hW.three_environment).point
      (hw.trans (expressionHeightBudget_ge_input _ 18)) K slot scalarBits j
    rw [max_eq_left ((le_max_right s (K + 2)).trans (expressionHeightBudget_ge_input _ 18)), expressionHeightBudget_comp] at hPoint
    exact hPoint.mono (expressionHeightBudget_mono _ (by decide : 21 ≤ 72))
  · exact h.fourInput.machine_leaves hs K outerBits scalarBits

end RationalMixedGroupSpec
end Blotto
