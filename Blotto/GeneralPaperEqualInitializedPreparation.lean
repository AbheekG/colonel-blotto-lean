import Blotto.GeneralPaperEqualNativeDrawRepresentation

/-! The actual original-input grouped-equal pipeline consumes the measured
initializer's exponent and word. Equality transport is erased; it neither
replays preparation nor evaluates an input-size or cost oracle. -/
namespace Blotto.GeneralPaperEqualInitializedPreparation
open GeneralPaperEqualResourceDomain
open GeneralPaperEqualFiniteKernel (terminal lottery)
open GeneralPaperEqualStoredBitSampler (Sampler native)
open GeneralPaperEqualNativeSampler (rounded)
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def transport {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1)
    (small' : ∀ j, 2 * (rounded true model W' k' values v hv).weight j ≤ 1)
    (hW : W = W') (hk : k = k')
    (a : Sampler (terminal (rounded true model W k values v hv) small).partition
      (lottery (rounded true model W k values v hv) small)) :
    Sampler (terminal (rounded true model W' k' values v hv) small').partition
      (lottery (rounded true model W' k' values v hv) small') := by
  subst W'
  subst k'
  exact a

theorem transport_native {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1)
    (small' : ∀ j, 2 * (rounded true model W' k' values v hv).weight j ≤ 1)
    (hW : W = W') (hk : k = k') (budget : ℚ) :
    transport model W k W' k' values v hv small small' hW hk (native true model W k values v hv small budget) =
      native true model W' k' values v hv small' budget := by
  subst W'
  subst k'
  rfl

def sourcePrice {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) : ℕ :=
  let result := (GeneralPaperEqualAddressedPreparation.run true model W W k values v hv small budget).2
  GeneralPaperEqualBitPreparationLedger.total result.1.1 result.1.2.1 result.1.2.2 result.2.1 result.2.2.1 result.2.2.2

theorem price_congr {n : ℕ} (model : RationalCostModel) (W k W' k' : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1)
    (small' : ∀ j, 2 * (rounded true model W' k' values v hv).weight j ≤ 1)
    (hW : W = W') (hk : k = k') (budget : ℚ) :
    sourcePrice model W k values v hv small budget = sourcePrice model W' k' values v hv small' budget := by
  subst W'
  subst k'
  rfl

theorem actualSmall (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    ∀ j, 2 * (rounded true model
      (GeneralPaperEqualCommonReference.prepareReference model A K p).1.2
      (GeneralPaperEqualCommonReference.prepareReference model A K p).1.1 p.values p.selector p.correct).weight j ≤ 1 := by
  rw [GeneralPaperEqualCommonReference.initialized_exponent]
  exact small_at_reference p _

def run (model : RationalCostModel) (A K : ℕ) (p : Problem model) :=
  let initial := GeneralPaperEqualCommonReference.prepareReference model A K p
  let source := GeneralPaperEqualAddressedPreparation.run true model initial.1.2 initial.1.2 initial.1.1
    p.values p.selector p.correct (actualSmall model A K p) p.budget
  let sampler := transport model initial.1.2 initial.1.1 (GeneralPaperEqualCommonReference.word K p) p.k
    p.values p.selector p.correct (actualSmall model A K p) (small_at_reference p _)
    (GeneralPaperEqualCommonReference.initialized_word model A K p)
    (GeneralPaperEqualCommonReference.initialized_exponent model A K p) source.1
  let work := source.2
  (sampler, initial.2 + GeneralPaperEqualBitPreparationLedger.total work.1.1 work.1.2.1 work.1.2.2 work.2.1 work.2.2.1 work.2.2.2)

theorem data (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (run model A K p).1 = native true model (GeneralPaperEqualCommonReference.word K p) p.k
      p.values p.selector p.correct (small_at_reference p _) p.budget := by
  simp only [run, GeneralPaperEqualAddressedPreparation.data]
  exact transport_native model _ _ _ _ p.values p.selector p.correct _ _ _ _ p.budget

theorem work (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    (run model A K p).2 = (GeneralPaperEqualCommonReference.prepareReference model A K p).2 +
      GeneralPaperEqualOriginalInputRates.sourceWork model K p := by
  have h := price_congr model
    (GeneralPaperEqualCommonReference.prepareReference model A K p).1.2
    (GeneralPaperEqualCommonReference.prepareReference model A K p).1.1
    (GeneralPaperEqualCommonReference.word K p) p.k p.values p.selector p.correct
    (actualSmall model A K p) (small_at_reference p _)
    (GeneralPaperEqualCommonReference.initialized_word model A K p)
    (GeneralPaperEqualCommonReference.initialized_exponent model A K p) p.budget
  exact congrArg (fun x => (GeneralPaperEqualCommonReference.prepareReference model A K p).2 + x) h

theorem calibrated_work (model : RationalCostModel) (K : ℕ) (p : Problem model) :
    (run model (GeneralPaperEqualCommonReference.word K p) K p).2 = GeneralPaperEqualOriginalInputRates.totalWork model K p :=
  work model _ K p

theorem returned_capacity (model : RationalCostModel) (A K : ℕ) (p : Problem model) :
    let sampler := (run model A K p).1
    GeneralPaperEqualRetainedStorage.footprint sampler.address sampler < 2 ^ sampler.address := by
  dsimp only
  rw [data]
  exact GeneralPaperEqualNativeDrawRepresentation.native_capacity true model _ p.k p.values p.selector p.correct (small_at_reference p _) p.budget

theorem native_epsilon_of_exponent {n : ℕ} (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (eps : ℚ) (hp : 0 < eps) (hOne : eps < 1) (hk : k = (GeneralPaperDyadicAccuracy.prepare eps).exponent)
    (small : ∀ j, 2 * (rounded true model W k values v hv).weight j ≤ 1) (budget : ℚ) (hB : 0 < budget) :
    Supported (budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw (native true model W k values v hv small budget) model) ∧
      regret v.values (budget : ℝ)
        (GeneralPaperEqualStoredBitSampler.outputLaw (native true model W k values v hv small budget) model)
        (GeneralPaperEqualStoredBitSampler.outputLaw (native true model W k values v hv small budget) model) ≤ (eps : ℝ) := by
  subst k
  exact GeneralPaperEqualStoredBitSampler.native_epsilon true model W values v hv eps hp hOne small budget hB

theorem epsilon (model : RationalCostModel) (A K : ℕ) (p : Problem model)
    (hOne : GeneralPaperEqualResourceHeadline.epsilon p < 1) (hB : 0 < p.budget) :
    let sampler := (run model A K p).1
    Supported (p.budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ∧
      regret p.selector.values (p.budget : ℝ) (GeneralPaperEqualStoredBitSampler.outputLaw sampler model)
        (GeneralPaperEqualStoredBitSampler.outputLaw sampler model) ≤ (GeneralPaperEqualResourceHeadline.epsilon p : ℝ) := by
  dsimp only
  rw [data]
  exact native_epsilon_of_exponent model _ p.k p.values p.selector p.correct
    (GeneralPaperEqualResourceHeadline.epsilon p) (GeneralPaperEqualResourceHeadline.epsilon_positive p) hOne
    (GeneralPaperEqualResourceHeadline.exponent_exact p) (small_at_reference p _) p.budget hB

end Blotto.GeneralPaperEqualInitializedPreparation
