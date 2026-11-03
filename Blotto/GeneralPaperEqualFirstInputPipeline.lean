import Blotto.GeneralPaperEqualFirstSelectedRates

/-! Once-built original accuracy/reference drives the corrected selected
preparation. Equality transports erase; no accuracy, source or cost profile
is evaluated again. -/
namespace Blotto.GeneralPaperEqualFirstInputPipeline
open GeneralPaperEqualInputDomain
open GeneralPaperEqualSelectedSampler (Sampler outputLaw)
open GeneralPaperEqualFirstNativeFacts (rounded)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 8192

def transport {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k')
    (a : Sampler (rounded true model W k values v hv) k budget) :
    Sampler (rounded true model W' k' values v hv) k' budget := by
  subst W'; subst k'; exact a

theorem transport_data {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    transport model W k W' k' values v hv budget hW hk
      (GeneralPaperEqualFirstSelectedPreparation.run model W W k values v hv budget).1 =
      (GeneralPaperEqualFirstSelectedPreparation.run model W' W' k' values v hv budget).1 := by
  subst W'; subst k'; rfl

theorem price_congr {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j = v.weight j)
    (budget : ℚ) (hW : W = W') (hk : k = k') :
    (GeneralPaperEqualFirstSelectedPreparation.run model W W k values v hv budget).2 =
      (GeneralPaperEqualFirstSelectedPreparation.run model W' W' k' values v hv budget).2 := by
  subst W'; subst k'; rfl

def run (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    Sampler (rounded true model (word K p) p.k p.values p.selector p.correct) p.k p.budget × ℕ :=
  let initial := GeneralPaperEqualInputInitialization.prepareReference model A K p
  let actual := GeneralPaperEqualFirstSelectedPreparation.run model initial.1.2 initial.1.2 initial.1.1
    p.values p.selector p.correct p.budget
  let output := transport model initial.1.2 initial.1.1 (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p) actual.1
  (output,initial.2+actual.2)

theorem data (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).1 =
      (GeneralPaperEqualFirstSelectedPreparation.run model (word K p) (word K p) p.k p.values p.selector p.correct p.budget).1 :=
  transport_data model _ _ _ _ p.values p.selector p.correct p.budget _ _

theorem work (model : RationalCostModel) (A K : ℕ) (p : Input model) :
    (run model A K p).2 = (GeneralPaperEqualInputInitialization.prepareReference model A K p).2+
      (GeneralPaperEqualFirstSelectedPreparation.run model (word K p) (word K p) p.k p.values p.selector p.correct p.budget).2 := by
  have h := price_congr model
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.2
    (GeneralPaperEqualInputInitialization.prepareReference model A K p).1.1
    (word K p) p.k p.values p.selector p.correct p.budget
    (GeneralPaperEqualInputInitialization.initialized_word model A K p)
    (GeneralPaperEqualInputInitialization.initialized_exponent model A K p)
  exact congrArg (fun t => (GeneralPaperEqualInputInitialization.prepareReference model A K p).2+t) h

def price (model : RationalCostModel) (W K : ℕ) (p : Input model) : ℕ :=
  GeneralPaperEqualInputInitialization.initializationPrice model W K p+
    GeneralPaperEqualFirstSelectedPreparation.bound model W W p.k p.values p.budget

theorem work_bound (model : RationalCostModel) (K : ℕ) (p : Input model) :
    (run model (word K p) K p).2 ≤ price model (word K p) K p := by
  rw [work]
  exact Nat.add_le_add (GeneralPaperEqualInputInitialization.initialization_work model _ K p)
    (GeneralPaperEqualFirstSelectedPreparation.work model _ _ p.k p.values p.selector p.correct p.budget)

theorem price_rate (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    GeneralPaperUniformResourceGrowth.Bound (fun p : Input model => price model (word K p) K p) ledger logarithm :=
  GeneralPaperUniformResourceGrowth.bound_add _ _ ledger logarithm logarithm_positive
    (GeneralPaperEqualInputRates.initialization_price_rate model hFast K)
    (GeneralPaperEqualFirstSelectedRates.preparation_rate model hFast K)

theorem paper_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ C d : ℕ, ∀ p : Input model,(run model (word K p) K p).2 ≤
      C*GeneralPaperEqualInputHeadline.inputSize p*(GeneralPaperEqualInputHeadline.paperLog p)^d :=
  GeneralPaperEqualInputHeadline.transfer_rate
    (GeneralPaperUniformResourceGrowth.dominated (price_rate model hFast K) (work_bound model K))

theorem original_regret (model : RationalCostModel) (A K : ℕ) (p : Input model) (hB : 0 < p.budget) :
    Supported (p.budget : ℝ) (outputLaw model (run model A K p).1) ∧
      regret p.selector.values (p.budget : ℝ) (outputLaw model (run model A K p).1)
        (outputLaw model (run model A K p).1) ≤ 3*(1/(2 : ℝ)^p.k)/64 := by
  rw [data]
  exact GeneralPaperEqualFirstSelectedPreparation.original_regret model _ _ p.k p.values p.selector p.correct p.budget hB

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Input model)
    (hOne : GeneralPaperEqualInputHeadline.epsilon p < 1) (hB : 0 < p.budget) :
    Supported (p.budget : ℝ) (outputLaw model (run model A K p).1) ∧
      regret p.selector.values (p.budget : ℝ) (outputLaw model (run model A K p).1)
        (outputLaw model (run model A K p).1) ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
  obtain ⟨hSupport,hRegret⟩ := original_regret model A K p hB
  refine ⟨hSupport,hRegret.trans ?_⟩
  have h := (GeneralPaperDyadicAccuracy.accuracy_bounds (GeneralPaperEqualInputHeadline.epsilon p)
    (GeneralPaperEqualInputHeadline.epsilon_positive p) hOne).2
  rw [GeneralPaperDyadicAccuracy.accuracy_power,← GeneralPaperEqualInputHeadline.exponent_exact p] at h
  have hReal : (1/(2 : ℝ)^p.k) ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by
    have hc : (((1/(2 : ℚ)^p.k : ℚ) : ℝ)) ≤ (GeneralPaperEqualInputHeadline.epsilon p : ℝ) := by exact_mod_cast h
    simpa only [Rat.cast_div,Rat.cast_one,Rat.cast_pow,Rat.cast_ofNat] using hc
  have hp : 0 < 1/(2 : ℝ)^p.k := by positivity
  linarith only [hReal,hp]

end Blotto.GeneralPaperEqualFirstInputPipeline
