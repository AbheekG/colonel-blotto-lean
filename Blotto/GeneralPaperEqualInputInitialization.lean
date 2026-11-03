import Blotto.GeneralPaperEqualInputDomain

/-! Measured reference construction is independent of the eventual branch.
Execution reads binary accuracy, measures original lengths and constructs a
fixed model coefficient times their short logarithmic measure. -/
namespace Blotto.GeneralPaperEqualInputInitialization
open GeneralPaperEqualInputDomain
set_option autoImplicit false
set_option maxHeartbeats 2200000

def prepareReference (model : RationalCostModel) (A K : ℕ) (p : Input model) : (ℕ × ℕ) × ℕ :=
  let precision := GeneralPaperBinaryAccuracy.prepare id A p.words
  let reference := GeneralPaperEqualReferenceConstruction.measured model A K precision.1 p.values p.budget p.words
  ((precision.1, reference.1), precision.2 + reference.2 + 64 * A + 64)

theorem measured_word_eq (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (GeneralPaperEqualReferenceConstruction.measured model A K p.k p.values p.budget p.words).1 = word K p := by
  simp only [GeneralPaperEqualReferenceConstruction.measured_data, word, logarithm, ledger, originalSize,
    budgetSize, accuracySize, GeneralPaperEqualReferenceConstruction.log]

theorem initialized_exponent (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (prepareReference model A K p).1.1 = p.k := by
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k
  rw [GeneralPaperBinaryAccuracy.prepare_data]
  have h := p.exponent_correct
  rw [GeneralPaperBinaryAccuracy.prepare_data] at h
  exact h.symm

theorem initialized_word (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (prepareReference model A K p).1.2 = word K p := by
  have hk := initialized_exponent model A K p
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k at hk
  change (GeneralPaperEqualReferenceConstruction.measured model A K
    (GeneralPaperBinaryAccuracy.prepare id A p.words).1 p.values p.budget p.words).1 = _
  rw [hk, GeneralPaperEqualReferenceConstruction.measured_data]
  rfl

def initializationPrice (model : RationalCostModel) (A K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperBinaryAccuracyConstructionStorage.price A (accuracySize p) +
    GeneralPaperEqualReferenceConstruction.measuredProfile model A K p.n p.k (originalSize p) (budgetSize p) (accuracySize p) + 64 * A + 64

theorem initialization_work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (prepareReference model A K p).2 ≤ initializationPrice model A K p := by
  have ha := GeneralPaperBinaryAccuracyConstructionStorage.work A p.words
  have hr := GeneralPaperEqualReferenceConstruction.measured_work model A K p.k p.values p.budget p.words
  have hk := initialized_exponent model A K p
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).1 = p.k at hk
  unfold prepareReference
  change (GeneralPaperBinaryAccuracy.prepare id A p.words).2 +
    (GeneralPaperEqualReferenceConstruction.measured model A K
      (GeneralPaperBinaryAccuracy.prepare id A p.words).1 p.values p.budget p.words).2 + 64 * A + 64 ≤ _
  rw [hk]
  exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add ha hr) _) _

theorem grouped_data (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (small : ∀ j, 2 * (GeneralPaperEqualNativeSampler.rounded true model 1 p.k p.values p.selector p.correct).weight j ≤ 1) :
    prepareReference model A K p = GeneralPaperEqualCommonReference.prepareReference model A K (grouped p small) := rfl

end Blotto.GeneralPaperEqualInputInitialization
