import Blotto.GeneralPaperEqualCopyRates

/-! The actual measured initializer feeds one selected preparation and one
retained-data copy. Its returned word is passed directly to the copy; no
original-size/accuracy/reference construction runs again. Erased transport
identifies exact data and complete measured source prices. -/
namespace Blotto.GeneralPaperEqualCopiedPipeline
open GeneralPaperEqualInputDomain
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 8192

def dispatchCloseCopy {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j) (budget : ℚ) :=
  let prepared := GeneralPaperEqualSelectedPipeline.dispatchClose model W k values v hv budget
  let copied := GeneralPaperEqualSelectedCopy.run W prepared.1
  (copied.1,prepared.2 + copied.2)

theorem transport_data {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    GeneralPaperEqualSelectedPipeline.transport model W k W' k' values v hv budget hW hk
      (dispatchCloseCopy model W k values v hv budget).1 = (dispatchCloseCopy model W' k' values v hv budget).1 := by
  subst W'; subst k'; rfl

theorem price_congr {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    (dispatchCloseCopy model W k values v hv budget).2 = (dispatchCloseCopy model W' k' values v hv budget).2 := by
  subst W'; subst k'; rfl

def run (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    Sampler (GeneralPaperEqualNativeSampler.rounded true model (word K p) p.k p.values p.selector p.correct) p.k p.budget × ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let actual := dispatchCloseCopy model initial.1.2 initial.1.1 p.values p.selector p.correct p.budget
  let a := GeneralPaperEqualSelectedPipeline.transport model initial.1.2 initial.1.1 (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p) actual.1
  (a,initial.2 + actual.2)

theorem data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1 = (dispatchCloseCopy model (word K p) p.k p.values p.selector p.correct p.budget).1 :=
  transport_data model _ _ _ _ p.values p.selector p.correct p.budget _ _

theorem selected_data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1 = (GeneralPaperEqualSelectedPipeline.run model A K p).1 := by
  rw [data,GeneralPaperEqualSelectedPipeline.data]
  exact GeneralPaperEqualSelectedCopy.data _ _

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).2 = (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 +
      (dispatchCloseCopy model (word K p) p.k p.values p.selector p.correct p.budget).2 := by
  have h := price_congr model
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.1
    (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p)
  exact congrArg (fun x => (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 + x) h

theorem copy_work_exact (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).2 = (GeneralPaperEqualSelectedPipeline.run model A K p).2 +
      (GeneralPaperEqualSelectedCopy.run (word K p) (GeneralPaperEqualSelectedPipeline.run model A K p).1).2 := by
  rw [work,GeneralPaperEqualSelectedPipeline.work,GeneralPaperEqualSelectedPipeline.data]
  dsimp only [dispatchCloseCopy]
  omega

theorem previous (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    run model A K p = GeneralPaperEqualReferenceCopyContract.finish (word K p)
      (GeneralPaperEqualSelectedPipeline.run model A K p) := by
  apply Prod.ext
  · exact (selected_data model A K p).trans (GeneralPaperEqualReferenceCopyContract.data _ _).symm
  · exact copy_work_exact model A K p

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualSelectedPipeline.price model K p +
    GeneralPaperEqualSelectedCopyWork.profile (word K p) p.n p.k (rationalWordWidth p.budget)

theorem work_bound (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (run model (word K p) K p).2 ≤ price model K p := by
  have ho := GeneralPaperEqualSelectedPipeline.work_bound model K p
  have hc := GeneralPaperEqualSelectedCopyWork.work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualSelectedPipeline.run model (word K p) K p).1
  rw [copy_work_exact]
  unfold price
  omega

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    GeneralPaperUniformResourceGrowth.Bound (price model K) ledger logarithm := by
  have hOld : GeneralPaperUniformResourceGrowth.Bound (GeneralPaperEqualSelectedPipeline.price model K) ledger logarithm :=
    GeneralPaperUniformResourceGrowth.bound_add _ _ ledger logarithm logarithm_positive
      (GeneralPaperEqualInputRates.total_price_rate model hFast K) (GeneralPaperEqualSelectedClosureWork.paper_rate model hFast K)
  exact GeneralPaperUniformResourceGrowth.bound_add _ _ ledger logarithm logarithm_positive hOld (GeneralPaperEqualCopyRates.profile_rate model K)

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ At et : ℕ, ∀ p : Input model,(run model (word K p) K p).2 ≤
      At * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ et :=
  GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperUniformResourceGrowth.dominated (price_rate model hFast K) (work_bound model K))

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hB : 0 < p.budget) :
    Supported (p.budget : ℝ) (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1) ∧
      regret p.selector.values (p.budget : ℝ) (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1)
        (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1) ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  rw [selected_data]
  exact GeneralPaperEqualSelectedPipeline.epsilon model A K p hOne hB

end Blotto.GeneralPaperEqualCopiedPipeline
