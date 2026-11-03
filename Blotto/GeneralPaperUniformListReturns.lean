import Blotto.GeneralPaperUniformListCounts

/-! The uniform-list interpretation and sharp count bounds on the actual
bit and numeric-real unequal preparation returns. -/
namespace Blotto.GeneralPaperUniformListReturns
open GeneralPaperStoredStrategySampler (Sampler)
open GeneralPaperUniformListSampler
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

def Interface {n T K : ℕ} (sampler : Sampler n T K) : Prop :=
  ∀ (bitModel : Bool) (primitive : ℕ → ℕ) (A : ℕ) (model : RationalCostModel) (poor : Bool),
    GeneralPaperExactStoredSampler.law bitModel primitive A model sampler poor =
      GeneralPaperUniformRowLaw.law (length_positive sampler)
        (fun i j => ((entry bitModel primitive A model sampler poor i).read j : ℝ)) ∧
    ∀ fresh : Fin (GeneralPaperExactStoredSampler.bits sampler) → Bool,
      (GeneralPaperExactStoredSampler.run bitModel primitive A model sampler poor fresh).output =
        entry bitModel primitive A model sampler poor
          (bitIndex (GeneralPaperExactStoredSampler.bits sampler) fresh) ∧
      (GeneralPaperExactStoredSampler.run bitModel primitive A model sampler poor fresh).freshReads =
        Nat.log2 (length sampler)

theorem interface {n T K : ℕ} (sampler : Sampler n T K) : Interface sampler :=
  fun bitModel primitive A model poor => ⟨uniform_law bitModel primitive A model sampler poor,
    fun fresh => ⟨actual_entry bitModel primitive A model sampler poor fresh,
      exact_random_bits bitModel primitive A model sampler poor fresh⟩⟩

def Contract {n : ℕ} (epsilon : ℚ) (actual : GeneralPaperClosedStrategyDriver.Prepared n) : Prop :=
  let o := actual.raw.strategies.original.reduced
  let k := actual.raw.exponent
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  ∃ sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
    actual.sampler = some sampler ∧
    (length sampler : ℚ) ≤ ((2^78*37 : ℕ) : ℚ) *
      GeneralPaperRealHeadlineParameters.nStar n epsilon / epsilon^4 * (binaryWordWidth (n+4) : ℚ) ∧
    Nat.log2 (length sampler) ≤ 4*binaryWordWidth ⌈epsilon⁻¹⌉₊ + 2*binaryWordWidth (n+4) + 87 ∧
    Interface sampler

theorem at_word (model : RationalCostModel) (W : ℕ) (p : GeneralPaperNativeResourceDomain.Problem)
    (hOne : GeneralPaperNativeWorkingSpaceHeadline.epsilon p < 1) :
    Contract (GeneralPaperNativeWorkingSpaceHeadline.epsilon p)
      (GeneralPaperArbitraryPreparationDraw.returned model W p) := by
  obtain ⟨sampler, hSampler, _⟩ := GeneralPaperClosedStrategyEquilibrium.bit_epsilon model W W W p.words
    (GeneralPaperNativeWorkingSpaceHeadline.epsilon p) (GeneralPaperNativeWorkingSpaceHeadline.epsilon_positive p)
    hOne rfl p.values p.selector p.correct p.budget p.budget_valid model.rat
  have h := GeneralPaperUniformListCounts.at_word_headlines model W p hOne sampler hSampler
  exact ⟨sampler, hSampler, h.1, h.2, interface sampler⟩

theorem numeric_headlines {n : ℕ} (model : RationalCostModel) (epsilon : ℚ)
    (hE : 0 < epsilon) (hOne : epsilon < 1)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j, values.read j = v.weight j)
    (b : ℚ) (hb : 0 < b ∧ b < 1) :
    let actual := (GeneralPaperClosedStrategyDriver.arithmetic model epsilon values v hv b).1
    let o := actual.raw.strategies.original.reduced
    let k := actual.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    ∀ sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      actual.sampler = some sampler →
      (length sampler : ℚ) ≤ ((2^78*37 : ℕ) : ℚ) *
        GeneralPaperRealHeadlineParameters.nStar n epsilon / epsilon^4 * (binaryWordWidth (n+4) : ℚ) ∧
      Nat.log2 (length sampler) ≤ 4*binaryWordWidth ⌈epsilon⁻¹⌉₊ + 2*binaryWordWidth (n+4) + 87 := by
  dsimp only
  intro sampler hSampler
  let k := (GeneralPaperDyadicAccuracy.prepare epsilon).exponent
  let o := (GeneralPaperOriginalValueReduction.run false model 1 k values).1
  have hm : o.m ≤ n :=
    (GeneralPaperOriginalValueReduction.count_bounds false model 1 k values v hv).2.1
  have hM : (o.m : ℚ) ≤ 36*GeneralPaperRealHeadlineParameters.nStar n epsilon :=
    GeneralPaperOriginalSourceValueContract.dyadic_field_count false model 1 epsilon hE hOne values v hv
  have hc := GeneralPaperExactRealSampler.native_controls model epsilon values v hv b hb sampler hSampler
  have hRows : sampler.controls.rows =
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rows := hc.1
  have hBits : sampler.controls.rowBits =
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k).rowBits := hc.2.1
  have hShifts : sampler.controls.shifts = GeneralPaperNativeSelectedSecurity.count k := hc.2.2.1
  have hLength := GeneralPaperUniformListCounts.native_length sampler epsilon hE hOne v.fields_positive hm hM
    (GeneralPaperRealHeadlineParameters.power_bound epsilon hE hOne) hRows hShifts
  have hReads := random_bits_bound sampler hm hBits hShifts
  have hk := GeneralPaperRealHeadlineParameters.exponent_bound epsilon
  exact ⟨hLength, hReads.trans (by dsimp only [k] at *; omega)⟩

theorem numeric (model : RationalCostModel) (p : GeneralPaperOriginalRealInput.Input)
    (hB : p.budget < 1) :
    Contract p.epsilon
      (GeneralPaperClosedStrategyDriver.arithmetic model p.epsilon p.values p.selector p.correct p.budget).1 := by
  obtain ⟨sampler, hSampler, _⟩ := GeneralPaperClosedStrategyEquilibrium.arithmetic_epsilon model
    p.epsilon p.epsilon_valid.1 p.epsilon_valid.2 p.values p.selector p.correct p.budget
    ⟨p.budget_valid.1, hB⟩ (fun _ => 1)
  have h := numeric_headlines model p.epsilon p.epsilon_valid.1 p.epsilon_valid.2
    p.values p.selector p.correct p.budget ⟨p.budget_valid.1, hB⟩ sampler hSampler
  exact ⟨sampler, hSampler, h.1, h.2, interface sampler⟩

def Bit (p : GeneralPaperOriginalGameInput.Input) : GeneralPaperAllBranchBitDispatch.Prepared p.n → Prop
  | .oneField _ _ _ => True
  | .equal _ _ => True
  | .unequal output => Contract (GeneralPaperOriginalGameInput.epsilon p) output

theorem bit_of_sampling {model : RationalCostModel} {C d K : ℕ}
    (p : GeneralPaperOriginalGameInput.Input) (hOne : GeneralPaperOriginalGameInput.epsilon p < 1)
    (output : GeneralPaperAllBranchBitDispatch.Prepared p.n)
    (hReturn : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some output)
    (hSampling : GeneralPaperOriginalSamplingContract.Contract model C d K p output) : Bit p output := by
  cases hSampling with
  | oneField _ _ _ => trivial
  | equal _ _ _ _ _ => trivial
  | unequal hN hStrict output _ _ =>
    let q := GeneralPaperOriginalGameInput.unequalInput p hStrict
    let actual := GeneralPaperMeasuredUnequalSampling.actual model K q
    have hr : (GeneralPaperMeasuredBitDispatch.run model K p).1 = some (.unequal actual) := by
      rw [GeneralPaperMeasuredBitDispatch.on_unequal model K p hN (ne_of_lt hStrict)]
      rfl
    have he : output = actual := GeneralPaperAllBranchBitDispatch.Prepared.unequal.inj
      (Option.some.inj (hReturn.symm.trans hr))
    subst output
    change Contract _ (GeneralPaperMeasuredUnequalSampling.actual model K q)
    rw [GeneralPaperMeasuredUnequalSampling.data]
    exact at_word model _ q hOne

def Real (model : RationalCostModel) (p : GeneralPaperOriginalRealInput.Input) :
    GeneralPaperAllBranchRealDispatch.Prepared model p → Prop
  | .oneField _ _ _ => True
  | .equal _ _ => True
  | .unequal output => Contract p.epsilon output

theorem real_actual (model : RationalCostModel) (p : GeneralPaperOriginalRealInput.Input) :
    Real model p (GeneralPaperAllBranchRealDispatch.run model p).1 := by
  by_cases hN : p.n = 1
  · rw [GeneralPaperAllBranchRealDispatch.on_one model p hN]
    trivial
  · by_cases hB : p.budget = 1
    · rw [GeneralPaperAllBranchRealDispatch.on_equal model p hN hB]
      trivial
    · rw [GeneralPaperAllBranchRealDispatch.on_unequal model p hN hB]
      exact numeric model p (GeneralPaperOriginalRealInput.strict_of_ne p hB)

end Blotto.GeneralPaperUniformListReturns
