import Blotto.GeneralPaperUniformLinearReference

/-! Actual normalized rational inputs for the grouped equal-budget branch.
The precision exponent is already constructed; accuracy parsing and the
other branches are joined separately. Source prices and references do not
change the rounded selector or the returned cache's numerical data. -/
namespace Blotto.GeneralPaperEqualResourceDomain
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

theorem rounded_reference {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    GeneralPaperEqualNativeSampler.rounded true model W k values v hv =
      GeneralPaperEqualNativeSampler.rounded true model 1 k values v hv := by
  have h := (GeneralPaperValueRoundingPaperContract.models_data model W 128 k values v hv).trans
    (GeneralPaperValueRoundingPaperContract.models_data model 1 128 k values v hv).symm
  simp only [GeneralPaperEqualNativeSampler.rounded, h]

theorem denominator_reference {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) :
    GeneralPaperEqualNativeSampler.roundDen true model W k values =
      GeneralPaperEqualNativeSampler.roundDen true model 1 k values := by
  exact congrArg Prod.snd ((GeneralPaperValueRoundingPaperContract.models_data model W 128 k values v hv).trans
    (GeneralPaperValueRoundingPaperContract.models_data model 1 128 k values v hv).symm)

structure Problem (model : RationalCostModel) where
  n : ℕ
  values : FixedArrayTable n ℚ
  selector : RationalFieldSelector n
  correct : ∀ j, values.read j = selector.weight j
  k : ℕ
  words : BinaryAccuracyWords
  exponent_correct : k = (GeneralPaperBinaryAccuracy.prepare id 1 words).1
  budget : ℚ
  small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 k values selector correct).weight j ≤ 1

def originalSize {model : RationalCostModel} (p : Problem model) : ℕ := GeneralPaperValueRoundingInputPrice.inputSize p.values

def budgetSize {model : RationalCostModel} (p : Problem model) : ℕ := rationalWordWidth p.budget

def accuracySize {model : RationalCostModel} (p : Problem model) : ℕ := GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words

def ledger {model : RationalCostModel} (p : Problem model) : ℕ := originalSize p + budgetSize p + p.n + accuracySize p + 1

def logarithm {model : RationalCostModel} (p : Problem model) : ℕ := 128 + p.k + binaryWordWidth (ledger p)

theorem logarithm_positive {model : RationalCostModel} (p : Problem model) : 1 ≤ logarithm p := by unfold logarithm; omega

@[fun_prop]
theorem exponent_tight (model : RationalCostModel) : Tight (fun p : Problem model => p.k) logarithm :=
  ⟨1, fun p => by dsimp only [logarithm]; omega⟩

theorem below_ledger_small {model : RationalCostModel} (f : Problem model → ℕ) (h : ∀ p, f p ≤ ledger p) :
    Small f logarithm := by
  refine ⟨1, fun p => ?_⟩
  have hw := binaryWordWidth_mono (h p)
  unfold logarithm
  omega

@[fun_prop]
theorem original_small (model : RationalCostModel) : Small (originalSize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)

@[fun_prop]
theorem budget_small (model : RationalCostModel) : Small (budgetSize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)

@[fun_prop]
theorem accuracy_small (model : RationalCostModel) : Small (accuracySize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)

@[fun_prop]
theorem count_small (model : RationalCostModel) : Small (fun p : Problem model => p.n) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)

theorem small_at_reference {model : RationalCostModel} (p : Problem model) (W : ℕ) :
    ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model W p.k p.values p.selector p.correct).weight j ≤ 1 := by
  rw [rounded_reference]
  exact p.small

def rounded {model : RationalCostModel} (p : Problem model) := GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct

def groups {model : RationalCostModel} (p : Problem model) : ℕ := (GeneralPaperEqualFiniteKernel.terminal (rounded p) p.small).groups.length

def segments {model : RationalCostModel} (p : Problem model) : ℕ := GeneralPaperPositiveSegmentCompaction.count (GeneralPaperEqualFiniteKernel.lottery (rounded p) p.small)

def width {model : RationalCostModel} (p : Problem model) : ℕ := (GeneralPaperEqualNativeCache.prepare true model 1 p.k p.values p.selector p.correct p.small p.budget).rangeBits

@[fun_prop]
theorem groups_small (model : RationalCostModel) : Small (groups (model := model)) logarithm :=
  small_mono (small_constant 3 _ logarithm_positive) (fun p => GeneralPaperEqualNativeCache.group_count (rounded p) p.small)

@[fun_prop]
theorem segments_small (model : RationalCostModel) : Small (segments (model := model)) logarithm :=
  small_mono (small_constant 7 _ logarithm_positive) (fun p => (GeneralPaperEqualNativeCache.compact_count (rounded p) p.small).2)

@[fun_prop]
theorem width_small (model : RationalCostModel) : Small (width (model := model)) logarithm := by
  have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
  have hn := count_small model
  have hk := small_of_tight (exponent_tight model) hL
  apply small_mono (g := fun p => 3670016 * (binaryWordWidth p.n + p.k + 10) + 1) (by fun_prop)
  intro p
  exact GeneralPaperEqualNativeCache.rangeBits true model 1 p.k p.values p.selector p.correct p.small p.budget

@[fun_prop]
theorem denominator_small (model : RationalCostModel) :
    Small (fun p : Problem model => GeneralPaperEqualNativeSampler.roundDen true model 1 p.k p.values) logarithm := by
  have hShort : Tight (fun p : Problem model => binaryWordWidth p.n + p.k + 9) logarithm := by
    have hL : ∀ p : Problem model, 1 ≤ logarithm p := logarithm_positive
    have hn := count_small model
    have hk := exponent_tight model
    fun_prop
  obtain ⟨C, hC⟩ := hShort
  exact ⟨C, fun p => (GeneralPaperEqualNativeSampler.roundDen_word true model 1 p.k p.values p.selector p.correct).trans (hC p)⟩

end Blotto.GeneralPaperEqualResourceDomain
