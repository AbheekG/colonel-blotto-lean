import Blotto.GeneralPaperEqualSelectedClosureWork

/-! The actual initializer outputs drive one dispatch and one local closure.
All transports are erased equalities; accuracy and rounding execute once.
The new closure is included in complete preparation time. -/
namespace Blotto.GeneralPaperEqualSelectedPipeline
open GeneralPaperEqualInputDomain
open GeneralPaperEqualSelectedSampler (Sampler)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def dispatchClose {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j) (budget : ℚ) :=
  let actual := GeneralPaperEqualBitDispatch.run model W W k values v hv budget
  let closed := GeneralPaperEqualSelectedSampler.close model W k budget actual.1
  (closed.1,actual.2 + closed.2)

def transport {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k')
    (a : Sampler (GeneralPaperEqualNativeSampler.rounded true model W k values v hv) k budget) :
    Sampler (GeneralPaperEqualNativeSampler.rounded true model W' k' values v hv) k' budget := by
  subst W'; subst k'; exact a

theorem transport_data {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    transport model W k W' k' values v hv budget hW hk (dispatchClose model W k values v hv budget).1 =
      (dispatchClose model W' k' values v hv budget).1 := by
  subst W'; subst k'; rfl

theorem price_congr {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    (dispatchClose model W k values v hv budget).2 = (dispatchClose model W' k' values v hv budget).2 := by
  subst W'; subst k'; rfl

def run (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    Sampler (GeneralPaperEqualNativeSampler.rounded true model (word K p) p.k p.values p.selector p.correct) p.k p.budget × ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let actual := dispatchClose model initial.1.2 initial.1.1 p.values p.selector p.correct p.budget
  let a := transport model initial.1.2 initial.1.1 (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p) actual.1
  (a,initial.2 + actual.2)

theorem data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1 = (dispatchClose model (word K p) p.k p.values p.selector p.correct p.budget).1 :=
  transport_data model _ _ _ _ p.values p.selector p.correct p.budget _ _

theorem branch_data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1.branch = (GeneralPaperEqualInputPipeline.run model A K p).1 := by
  rw [data,GeneralPaperEqualInputPipeline.data]
  exact GeneralPaperEqualSelectedSampler.close_branch model _ p.k p.budget _

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).2 = (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 +
      (dispatchClose model (word K p) p.k p.values p.selector p.correct p.budget).2 := by
  have h := price_congr model
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.1
    (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p)
  exact congrArg (fun x => (GeneralPaperEqualInputInitialization.prepareReference model A K p).2 + x) h

def price (model : RationalCostModel) (K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputRates.totalPrice model K p +
    GeneralPaperEqualSelectedClosureWork.price model (word K p) p.n p.k (rationalWordWidth p.budget)

theorem work_bound (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (run model (word K p) K p).2 ≤ price model K p := by
  have hi := GeneralPaperEqualInputInitialization.initialization_work model (word K p) K p
  have hd := GeneralPaperEqualBitDispatch.work model (word K p) (word K p) p.k p.values p.selector p.correct p.budget
  have hc := GeneralPaperEqualSelectedClosureWork.work model (word K p) p.k p.budget
    (GeneralPaperEqualBitDispatch.run model (word K p) (word K p) p.k p.values p.selector p.correct p.budget).1
  rw [work]
  dsimp only [dispatchClose,price,GeneralPaperEqualInputRates.totalPrice,GeneralPaperEqualInputRates.bitPrice]
  omega

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ At et : ℕ, ∀ p : Input model, (run model (word K p) K p).2 ≤
      At * GeneralPaperEqualInputHeadline.inputSize p * (GeneralPaperEqualInputHeadline.paperLog p) ^ et := by
  have hp : GeneralPaperUniformResourceGrowth.Bound (price model K) ledger logarithm :=
    GeneralPaperUniformResourceGrowth.bound_add _ _ ledger logarithm logarithm_positive
      (GeneralPaperEqualInputRates.total_price_rate model hFast K) (GeneralPaperEqualSelectedClosureWork.paper_rate model hFast K)
  exact GeneralPaperEqualInputHeadline.transfer_rate (GeneralPaperUniformResourceGrowth.dominated hp (work_bound model K))

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hB : 0 < p.budget) :
    Supported (p.budget : ℝ) (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1) ∧
      regret p.selector.values (p.budget : ℝ) (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1)
        (GeneralPaperEqualSelectedSampler.outputLaw model (run model A K p).1) ≤
          (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  unfold GeneralPaperEqualSelectedSampler.outputLaw
  rw [branch_data]
  exact GeneralPaperEqualInputPipeline.epsilon model A K p hOne hB

end Blotto.GeneralPaperEqualSelectedPipeline
