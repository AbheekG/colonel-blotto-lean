import Blotto.WordMachineLaw
import Blotto.AffineMixture
import Blotto.AllocationCDFDistance

/-! Whole-allocation law semantics for finite word-choice continuations.
These folds are used in proofs; state-machine execution does not build trees. -/

namespace Blotto.WordChoiceTree
open MeasureTheory

theorem binaryLaw_ae {n : ℕ} (p : ℝ) (hp : 0 ≤ p ∧ p ≤ 1) (a b : Mixed n) (P : Allocation n → Prop)
    (ha : ∀ᵐ y ∂(a : Measure (Allocation n)), P y) (hb : ∀ᵐ y ∂(b : Measure (Allocation n)), P y) :
    ∀ᵐ y ∂(binaryLaw p hp a b : Measure (Allocation n)), P y := by
  unfold binaryLaw
  exact probabilityMixture_ae _ _ _ _ (by
    intro flag
    fin_cases flag
    · exact ha
    · exact hb)

noncomputable def evalLaw {α : Type*} {n : ℕ} (f : α → Mixed n) : WordChoiceTree α → Mixed n
  | .leaf x => f x
  | .fork a b hb hab upper lower =>
    binaryLaw (((a : ℚ) / b : ℚ) : ℝ) (by
      have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
      have hpQ : 0 ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ 1 :=
        ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩
      exact_mod_cast hpQ) (upper.evalLaw f) (lower.evalLaw f)

theorem evalLaw_ae {α : Type*} {n : ℕ} (T : WordChoiceTree α) (f : α → Mixed n) (P : Allocation n → Prop)
    (h : ∀ x, ∀ᵐ y ∂(f x : Measure (Allocation n)), P y) :
    ∀ᵐ y ∂(T.evalLaw f : Measure (Allocation n)), P y := by
  induction T with
  | leaf x => exact h x
  | fork a b hb hab upper lower hu hl =>
    exact binaryLaw_ae _ _ _ _ _ hu hl

theorem evalLaw_fullBudget {α : Type*} {n : ℕ} (T : WordChoiceTree α) (f : α → Mixed n) {B : ℝ}
    (h : ∀ x, ∀ᵐ y ∂(f x : Measure (Allocation n)), FullBudget B y) :
    ∀ᵐ y ∂(T.evalLaw f : Measure (Allocation n)), FullBudget B y := by
  induction T with
  | leaf x => exact h x
  | fork a b hb hab upper lower hu hl => exact binaryLaw_fullBudget _ _ _ _ hu hl

theorem evalLaw_CDFClose {α : Type*} {n : ℕ} (T : WordChoiceTree α) (f g : α → Mixed n) {δ : ℝ}
    (h : ∀ x, CDFClose (f x) (g x) δ) : CDFClose (T.evalLaw f) (T.evalLaw g) δ := by
  induction T with
  | leaf x => exact h x
  | fork a b hb hab upper lower hu hl => exact binaryLaw_CDFClose _ _ hu hl

theorem evalLaw_affine_marginal {α : Type*} {n : ℕ} (T : WordChoiceTree α) (f : α → Mixed n)
    (weight : α → ℝ) (hw : ∀ x, 0 ≤ weight x ∧ weight x ≤ 1) (j : Fin n) (A D : Measure ℝ)
    (hm : ∀ x, (marginal (f x) j : Measure ℝ) = affineMeasure (weight x) A D) :
    (marginal (T.evalLaw f) j : Measure ℝ) = affineMeasure (T.decode.mean weight) A D := by
  have hmean : ∀ U : WordChoiceTree α, 0 ≤ U.decode.mean weight ∧ U.decode.mean weight ≤ 1 := by
    intro U
    induction U with
    | leaf x => exact hw x
    | fork a b hb hab upper lower hu hl =>
      have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
      have hpQ : 0 ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ 1 :=
        ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩
      have hp : (0 : ℝ) ≤ ((a : ℚ) / b : ℚ) ∧ (((a : ℚ) / b : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hpQ
      simp only [decode, AdaptiveChoiceTree.mean]
      constructor
      · exact add_nonneg (mul_nonneg hp.1 hu.1) (mul_nonneg (sub_nonneg.mpr hp.2) hl.1)
      · nlinarith [mul_le_mul_of_nonneg_left hu.2 hp.1,
          mul_le_mul_of_nonneg_left hl.2 (sub_nonneg.mpr hp.2)]
  induction T with
  | leaf x => exact hm x
  | fork a b hb hab upper lower hu hl =>
    have hbQ : (0 : ℚ) < b := by exact_mod_cast hb
    have hpQ : 0 ≤ (a : ℚ) / b ∧ (a : ℚ) / b ≤ 1 :=
      ⟨by positivity, (div_le_one hbQ).mpr (by exact_mod_cast hab)⟩
    have hp : (0 : ℝ) ≤ ((a : ℚ) / b : ℚ) ∧ (((a : ℚ) / b : ℚ) : ℝ) ≤ 1 := by exact_mod_cast hpQ
    rw [evalLaw, binaryLaw_marginal, hu, hl, binary_affineMeasure _ _ _ hp (hmean upper) (hmean lower)]
    rfl

theorem mean_div_const {α : Type*} (T : WordChoiceTree α) (f : α → ℝ) (c : ℝ) :
    T.decode.mean (fun x => f x / c) = T.decode.mean f / c := by
  induction T with
  | leaf x => rfl
  | fork a b hb hab upper lower hu hl =>
    simp only [decode, AdaptiveChoiceTree.mean, hu, hl]
    ring

end Blotto.WordChoiceTree
