import Blotto.RationalThreeInputCode

/-! Complete ordered three-variable descriptor height, including E=0.
The original input word-height certificate is preserved in the exceptional
branch and propagated through the compiled regular branch. -/

namespace Blotto

theorem expressionHeightBudget_ge_input (s d : ℕ) : s ≤ expressionHeightBudget s d := by
  have hp : 1 ≤ (2 : ℕ) ^ d := Nat.one_le_pow d 2 (by decide)
  have hm := Nat.mul_le_mul_left (s + 1) hp
  unfold expressionHeightBudget
  omega

theorem expressionHeightBudget_comp (s a b : ℕ) :
    expressionHeightBudget (expressionHeightBudget s a) b = expressionHeightBudget s (a + b) := by
  have hp : 0 < (s + 1) * 2 ^ a := Nat.mul_pos (by omega) (Nat.two_pow_pos a)
  have he : (s + 1) * 2 ^ a - 1 + 1 = (s + 1) * 2 ^ a := by omega
  unfold expressionHeightBudget
  rw [he, Nat.mul_assoc, ← pow_add]

namespace RationalThreeInputCode

theorem environment_field_heights (i : RationalThreeInput) (s : ℕ)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight i.B s ∧ RationalHeight i.a s ∧ RationalHeight i.d s ∧ RationalHeight i.c s ∧ RationalHeight i.p s := by
  have hB := hEnv 0
  have hA := hEnv 1
  have hD := hEnv 2
  have hC := hEnv 3
  have hP := hEnv 4
  simpa [environment, FixedArrayTable.read_ofFn] using And.intro hB ⟨hA, hD, hC, hP⟩

theorem segment_weight_height (i : RationalThreeInput) (slot : Fin 9) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.segmentLottery.weight slot) (expressionHeightBudget s 18) := by
  unfold RationalThreeInput.segmentLottery
  split
  · rename_i hE
    rw [RationalThreeGeometryCode.compiledLottery_eq]
    have h := chosen_height i hE slot s hs hEnv
    rw [expressionHeightBudget_comp] at h
    exact h
  · change RationalHeight (if slot = 0 then (1 : ℚ) else 0) (expressionHeightBudget s 18)
    have hB : 2 ≤ expressionHeightBudget s 18 := hs.trans (expressionHeightBudget_ge_input s 18)
    by_cases hz : slot = 0
    · rw [ite_eq_left hz]
      exact (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hB
    · rw [ite_eq_right hz]
      exact (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono hB

theorem segment_endpoint_heights (i : RationalThreeInput) (slot : Fin 9) (j : Fin 3) (s : ℕ) (hs : 2 ≤ s)
    (hEnv : ∀ j, RationalHeight ((environment i).read j) s) :
    RationalHeight (i.segmentLottery.P slot j) (expressionHeightBudget s 4) ∧
      RationalHeight (i.segmentLottery.Q slot j) (expressionHeightBudget s 4) := by
  unfold RationalThreeInput.segmentLottery
  split
  · rename_i hE
    rw [RationalThreeGeometryCode.compiledLottery_eq]
    have hp : 2 ≤ expressionHeightBudget s 2 := hs.trans (expressionHeightBudget_ge_input s 2)
    have hE := geometry_environment_height i hE s hs hEnv
    have hP := RationalThreeGeometryCode.vertex_height (i.geometry ‹0 < i.a + i.d - i.B›)
      (RationalThreeGeometry.edges slot).1 j _ hp hE
    have hQ := RationalThreeGeometryCode.vertex_height (i.geometry ‹0 < i.a + i.d - i.B›)
      (RationalThreeGeometry.edges slot).2 j _ hp hE
    rw [expressionHeightBudget_comp] at hP hQ
    exact ⟨hP, hQ⟩
  · have hf := environment_field_heights i s hEnv
    have hm := expressionHeightBudget_ge_input s 4
    have h0 : RationalHeight (0 : ℚ) (expressionHeightBudget s 4) :=
      (show RationalHeight (0 : ℚ) 2 by norm_num [RationalHeight]).mono (hs.trans hm)
    fin_cases j
    · exact ⟨h0, hf.2.1.mono hm⟩
    · exact ⟨h0, hf.2.2.1.mono hm⟩
    · exact ⟨hf.1.mono hm, h0⟩

end RationalThreeInputCode
end Blotto
