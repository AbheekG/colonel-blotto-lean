import Blotto.GeneralPaperEqualBitBranchDraw

/-! Actual normalized equal-budget inputs before any branch is selected.
The exponent retains its binary-accuracy provenance. There is no small-field
or heavy-field certificate in this domain or in its sizing parameters. -/
namespace Blotto.GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2000000

structure Input (model : RationalCostModel) where
  n : ℕ
  values : FixedArrayTable n ℚ
  selector : RationalFieldSelector n
  correct : ∀ j, values.read j = selector.weight j
  k : ℕ
  words : BinaryAccuracyWords
  exponent_correct : k = (GeneralPaperBinaryAccuracy.prepare id 1 words).1
  budget : ℚ

def originalSize {model : RationalCostModel} (p : Input model) : ℕ := GeneralPaperValueRoundingInputPrice.inputSize p.values
def budgetSize {model : RationalCostModel} (p : Input model) : ℕ := rationalWordWidth p.budget
def accuracySize {model : RationalCostModel} (p : Input model) : ℕ := GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words
def ledger {model : RationalCostModel} (p : Input model) : ℕ := originalSize p + budgetSize p + p.n + accuracySize p + 1
def logarithm {model : RationalCostModel} (p : Input model) : ℕ := 128 + p.k + binaryWordWidth (ledger p)
def word (K : ℕ) {model : RationalCostModel} (p : Input model) : ℕ := K * logarithm p

theorem logarithm_positive {model : RationalCostModel} (p : Input model) : 1 ≤ logarithm p := by unfold logarithm; omega
theorem ledger_positive {model : RationalCostModel} (p : Input model) : 1 ≤ ledger p := by unfold ledger; omega

@[fun_prop] theorem exponent_tight (model : RationalCostModel) : Tight (fun p : Input model => p.k) logarithm :=
  ⟨1, fun p => by dsimp only [logarithm]; omega⟩

theorem below_ledger_small {model : RationalCostModel} (f : Input model → ℕ) (h : ∀ p, f p ≤ ledger p) : Small f logarithm := by
  refine ⟨1, fun p => ?_⟩
  have hw := binaryWordWidth_mono (h p)
  unfold logarithm
  omega

@[fun_prop] theorem original_small (model : RationalCostModel) : Small (originalSize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)
@[fun_prop] theorem budget_small (model : RationalCostModel) : Small (budgetSize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)
@[fun_prop] theorem accuracy_small (model : RationalCostModel) : Small (accuracySize (model := model)) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)
@[fun_prop] theorem count_small (model : RationalCostModel) : Small (fun p : Input model => p.n) logarithm :=
  below_ledger_small _ (fun p => by unfold ledger; omega)
@[fun_prop] theorem word_tight (K : ℕ) (model : RationalCostModel) : Tight (word K (model := model)) logarithm := ⟨K, fun _ => le_rfl⟩

def forget {model : RationalCostModel} (p : GeneralPaperEqualResourceDomain.Problem model) : Input model :=
  ⟨p.n, p.values, p.selector, p.correct, p.k, p.words, p.exponent_correct, p.budget⟩

def grouped {model : RationalCostModel} (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1) :
    GeneralPaperEqualResourceDomain.Problem model :=
  ⟨p.n, p.values, p.selector, p.correct, p.k, p.words, p.exponent_correct, p.budget, small⟩

theorem forget_grouped {model : RationalCostModel} (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1) :
    forget (grouped p small) = p := rfl

theorem grouped_word {model : RationalCostModel} (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1) (K : ℕ) :
    GeneralPaperEqualCommonReference.word K (grouped p small) = word K p := rfl

end Blotto.GeneralPaperEqualInputDomain
