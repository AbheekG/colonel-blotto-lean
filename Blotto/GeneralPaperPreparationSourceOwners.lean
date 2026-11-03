import Blotto.GeneralPaperResultAttachmentLifetime
import Blotto.GeneralPaperEqualSelectedCopyLifetimeRates

/-! Literal caller data retained across selected preparation: original
input, pre-copy selected source and copied source. Every branch's actual
typed payload is owned at the caller width. Primitive proof fields erase. -/
namespace Blotto.GeneralPaperPreparationSourceOwners
open GeneralPaperEqualSelectedSampler (Sampler)
open GeneralPaperEqualInputDomain
open GeneralPaperUniformResourceGrowth GeneralPaperEqualUniformRateAlgebra
set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 8192

def owner {n : ℕ} {v : RationalFieldSelector n} {k : ℕ} {budget : ℚ} (S : ℕ) (source : Sampler v k budget) : ℕ :=
  GeneralPaperEqualSelectedBranchOwner.footprint S source.branch + GeneralPaperEqualSelectedCopyLifetime.sourceHeader S source.address

theorem native_bound {n : ℕ} (model : RationalCostModel) (W S k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ)
    (source : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    owner S source ≤ GeneralPaperEqualSelectedCopyLifetime.profile S n k (rationalWordWidth budget) := by
  have hBranch := GeneralPaperEqualSelectedBranchOwner.bounded model W S k values v hv budget source.branch
  have hHeader := GeneralPaperEqualSelectedCopyLifetime.header_bound S source.address _
    (GeneralPaperEqualSelectedSampler.address_bound source)
  unfold owner GeneralPaperEqualSelectedCopyLifetime.profile
  omega

def window (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.inputOwner model (word K p) p +
    owner (word K p) (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1 +
    owner (word K p) (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1

def profile (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitializerLifetime.inputProfile model (word K p) p +
    2 * GeneralPaperEqualSelectedCopyLifetime.profile (word K p) p.n p.k (rationalWordWidth p.budget)

theorem window_bound (model : RationalCostModel) (K : ℕ) (p : Input model) : window model K p ≤ profile model K p := by
  have hInput := GeneralPaperEqualInputInitializerLifetime.input_bound model (word K p) p
  have hOriginal := native_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1
  have hCopied := native_bound model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualCopiedPipeline.run model (word K p) K p).1
  unfold window profile
  omega

theorem profile_rate (model : RationalCostModel) (K : ℕ) : Bound (profile model K) ledger logarithm := by
  have hL : ∀ p : Input model,1 ≤ logarithm p := logarithm_positive
  have hr : ∀ p : Input model,1 ≤ ledger p := ledger_positive
  have hOriginal : Bound (originalSize (model := model)) ledger logarithm := GeneralPaperEqualInputRates.value_bound model
  have hBudget : Bound (budgetSize (model := model)) ledger logarithm := GeneralPaperEqualInputRates.budget_bound model
  have hAccuracy := GeneralPaperEqualInputRates.accuracy_bound model
  have hN := GeneralPaperEqualInputRates.count_bound model
  have hWord := polylog_of_tight (word_tight K model)
  have hCopy := GeneralPaperEqualSelectedCopyLifetimeRates.profile_rate model K
  unfold profile GeneralPaperEqualInputInitializerLifetime.inputProfile
  fun_prop

end Blotto.GeneralPaperPreparationSourceOwners
