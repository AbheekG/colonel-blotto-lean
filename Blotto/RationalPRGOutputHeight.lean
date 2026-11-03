import Blotto.RationalLottoOutputHeight
import Blotto.RationalPRGOriginalLattice
import Blotto.RationalPRGOriginalSampler

/-! Full native PRG output words are charged to normalized or original game
input words plus precision. Both players and every cap/fallback path are
included. The resulting bounds are independent of resource-rounding depth. -/

namespace Blotto

namespace RationalPRGInput

theorem richNativeSystem_on_lattice {n : ℕ} (i : RationalPRGInput n) :
    i.richNativeSystem.OnLattice i.latticeDenominator := ⟨i.lengths_on_lattice, i.richInitial_on_lattice⟩

theorem poorNativeSystem_on_lattice {n : ℕ} (i : RationalPRGInput n) :
    i.poorNativeSystem.OnLattice i.latticeDenominator := ⟨i.lengths_on_lattice, i.poorInitial_on_lattice⟩

theorem richSample_height_with_width {n : ℕ} (i : RationalPRGInput n) (s : ℕ) (hs : 2 ≤ s)
    (hWidth : binaryWordWidth i.latticeDenominator ≤ s) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.richSample K bits j) (expressionHeightBudget (max s (K + 2)) 75) := by
  have hOne : RationalHeight (1 : ℚ) s := (show RationalHeight (1 : ℚ) 2 by norm_num [RationalHeight]).mono hs
  exact i.richNativeSystem_on_lattice.paperSample i.latticeDenominator_pos le_rfl s hs hOne hWidth K bits j

theorem poorSample_height_with_width {n : ℕ} (i : RationalPRGInput n) (s : ℕ) (hs : 2 ≤ s)
    (hBudget : RationalHeight i.b s) (hWidth : binaryWordWidth i.latticeDenominator ≤ s) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.poorSample K bits j) (expressionHeightBudget (max s (K + 2)) 75) :=
  i.poorNativeSystem_on_lattice.paperSample i.latticeDenominator_pos i.b_le s hs hBudget hWidth K bits j

theorem sample_heights {n : ℕ} (i : RationalPRGInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.richSample K bits j) (expressionHeightBudget (max (3 + i.inputWordWidth) (K + 2)) 75) ∧
      RationalHeight (i.poorSample K bits j) (expressionHeightBudget (max (3 + i.inputWordWidth) (K + 2)) 75) := by
  have hs : 2 ≤ 3 + i.inputWordWidth := by omega
  have hWidth : binaryWordWidth i.latticeDenominator ≤ 3 + i.inputWordWidth := i.latticeDenominator_wordWidth.trans (by omega)
  have hB : rationalWordWidth i.b ≤ 3 + i.inputWordWidth := by unfold inputWordWidth; omega
  exact ⟨i.richSample_height_with_width _ hs hWidth K bits j,
    i.poorSample_height_with_width _ hs ((rationalHeight_of_wordWidth i.b).mono hB) hWidth K bits j⟩

end RationalPRGInput

namespace RationalPRGOriginalInput

theorem normalized_budget_height {n : ℕ} (i : RationalPRGOriginalInput n) :
    RationalHeight i.normalizedInput.b (3 + i.originalInputWordWidth) := by
  have h := (rationalHeight_of_wordWidth i.b).div (rationalHeight_of_wordWidth i.a)
  exact h.mono (by unfold originalInputWordWidth; omega)

theorem scale_height {n : ℕ} (i : RationalPRGOriginalInput n) : RationalHeight i.a (3 + i.originalInputWordWidth) :=
  (rationalHeight_of_wordWidth i.a).mono (by unfold originalInputWordWidth; omega)

theorem normalized_sample_heights {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.normalizedInput.richSample K bits j)
        (expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 75) ∧
      RationalHeight (i.normalizedInput.poorSample K bits j)
        (expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 75) := by
  have hs : 2 ≤ 3 + i.originalInputWordWidth := by omega
  have hWidth : binaryWordWidth i.normalizedInput.latticeDenominator ≤ 3 + i.originalInputWordWidth :=
    i.normalized_lattice_wordWidth_original.trans (by omega)
  exact ⟨i.normalizedInput.richSample_height_with_width _ hs hWidth K bits j,
    i.normalizedInput.poorSample_height_with_width _ hs i.normalized_budget_height hWidth K bits j⟩

theorem sample_heights {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    RationalHeight (i.richSample K bits j) (expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 76) ∧
      RationalHeight (i.poorSample K bits j) (expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 76) := by
  have h := i.normalized_sample_heights K bits j
  have hm : 3 + i.originalInputWordWidth ≤ expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 75 :=
    (le_max_left _ _).trans (expressionHeightBudget_ge_input _ _)
  have hA := i.scale_height.mono hm
  have hRich := hA.mul_level h.1
  have hPoor := hA.mul_level h.2
  rw [i.richSample_apply, i.poorSample_apply]
  exact ⟨hRich, hPoor⟩

theorem sample_wordWidths {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    rationalWordWidth (i.richSample K bits j) ≤ 1 + 2 * expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 76 ∧
      rationalWordWidth (i.poorSample K bits j) ≤ 1 + 2 * expressionHeightBudget (max (3 + i.originalInputWordWidth) (K + 2)) 76 :=
  ⟨rationalWordWidth_of_height (i.sample_heights K bits j).1, rationalWordWidth_of_height (i.sample_heights K bits j).2⟩

theorem sample_wordWidths_linear {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) (j : Fin n) :
    rationalWordWidth (i.richSample K bits j) ≤ 2 ^ 77 * (i.originalInputWordWidth + K + 6) ∧
      rationalWordWidth (i.poorSample K bits j) ≤ 2 ^ 77 * (i.originalInputWordWidth + K + 6) := by
  have h := i.sample_wordWidths K bits j
  norm_num [expressionHeightBudget] at h ⊢
  constructor <;> omega

theorem sample_total_wordWidths {n : ℕ} (i : RationalPRGOriginalInput n) (K : ℕ)
    (bits : Fin (RationalLottoResourceSystem.sampleBitBudget n K) → Bool) :
    (∑ j, rationalWordWidth (i.richSample K bits j)) ≤ n * (2 ^ 77 * (i.originalInputWordWidth + K + 6)) ∧
      (∑ j, rationalWordWidth (i.poorSample K bits j)) ≤ n * (2 ^ 77 * (i.originalInputWordWidth + K + 6)) := by
  have hRich := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (i.sample_wordWidths_linear K bits j).1)
  have hPoor := Finset.sum_le_sum (s := Finset.univ) (fun j _ => (i.sample_wordWidths_linear K bits j).2)
  simpa using And.intro hRich hPoor

end RationalPRGOriginalInput
end Blotto
