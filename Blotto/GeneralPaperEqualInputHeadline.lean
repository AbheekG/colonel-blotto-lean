import Blotto.GeneralPaperEqualInputInitializerCapacity

/-! Paper input/epsilon forms for branch-unrestricted measured equal bit
preparation. Every initializer phase shares one uniform constructed word;
new dispatch/native phase joins remain distinct obligations. -/
namespace Blotto.GeneralPaperEqualInputHeadline
open GeneralPaperEqualInputDomain GeneralPaperEqualInputRates GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000

def epsilon {model : RationalCostModel} (p : Input model) : ℚ :=
  (p.words.numerator.value : ℚ) / p.words.denominator.value

theorem epsilon_positive {model : RationalCostModel} (p : Input model) : 0 < epsilon p :=
  div_pos (by exact_mod_cast p.words.numerator.value_pos) (by exact_mod_cast p.words.denominator.value_pos)

theorem exponent_exact {model : RationalCostModel} (p : Input model) :
    p.k = (GeneralPaperDyadicAccuracy.prepare (epsilon p)).exponent :=
  p.exponent_correct.trans (GeneralPaperBinaryAccuracy.exact_exponent id 1 p.words (epsilon p) rfl)

def inputSize {model : RationalCostModel} (p : Input model) : ℕ := originalSize p + budgetSize p + accuracySize p + 1

theorem ledger_bound {model : RationalCostModel} (p : Input model) : ledger p ≤ 2 * inputSize p := by
  have hn := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  change p.n ≤ originalSize p at hn
  unfold ledger inputSize
  omega

def paperLog {model : RationalCostModel} (p : Input model) : ℕ :=
  129 + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + binaryWordWidth (inputSize p + 1)

theorem log_comparison {model : RationalCostModel} (p : Input model) : logarithm p ≤ 2 * paperLog p := by
  have hk := GeneralPaperRealHeadlineParameters.exponent_bound (epsilon p)
  rw [← exponent_exact p] at hk
  have h0 := binaryWordWidth_mono (ledger_bound p)
  have h1 := binaryWordWidth_mul 2 (inputSize p)
  have h2 : binaryWordWidth 2 = 2 := by decide
  have hi := binaryWordWidth_mono (show inputSize p ≤ inputSize p + 1 by omega)
  unfold logarithm paperLog
  omega

theorem word_tight (model : RationalCostModel) (K : ℕ) :
    Tight (GeneralPaperEqualInputDomain.word K (model := model)) paperLog := by
  refine ⟨2 * K, fun p => ?_⟩
  exact (Nat.mul_le_mul_left K (log_comparison p)).trans_eq (by ring)

theorem transfer_rate {model : RationalCostModel} {f : Input model → ℕ} (hf : Bound f ledger logarithm) :
    ∃ A e : ℕ, ∀ p, f p ≤ A * inputSize p * (paperLog p) ^ e := by
  obtain ⟨A, e, hA⟩ := hf
  refine ⟨2 * A * 2 ^ e, e, fun p => ?_⟩
  have h := (hA p).trans (Nat.mul_le_mul (Nat.mul_le_mul_left A (ledger_bound p))
    (Nat.pow_le_pow_left (log_comparison p) e))
  exact h.trans_eq (by rw [mul_pow]; ring)

theorem bit_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ A e : ℕ, ∀ p : Input model, totalWork model K p ≤ A * inputSize p * (paperLog p) ^ e :=
  transfer_rate (total_work_rate model hFast K)

theorem measured_time_initializer_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Input model,
      let W := word K p
      let initial := GeneralPaperEqualInputInitialization.prepareReference model W K p
      initial.1.1 = p.k ∧ initial.1.2 = W ∧ totalWork model K p ≤ At * inputSize p * (paperLog p) ^ et ∧
      ∀ phase : GeneralPaperEqualInputInitializerLifetime.Phase p.n,
        GeneralPaperEqualInputInitializerLifetime.window model W K p phase ≤ As * inputSize p * (paperLog p) ^ es ∧
        GeneralPaperEqualInputInitializerLifetime.window model W K p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperEqualInputInitializerCapacity.uniform_capacity model hFast
  obtain ⟨At, et, hTime⟩ := bit_time model hFast K
  obtain ⟨As, es, hSpace⟩ := transfer_rate (GeneralPaperEqualInputInitializerCapacity.profile_rate model hFast K)
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  refine ⟨GeneralPaperEqualInputInitialization.initialized_exponent model _ K p,
    GeneralPaperEqualInputInitialization.initialized_word model _ K p, hTime p, fun phase => ?_⟩
  have h := GeneralPaperEqualInputInitializerLifetime.all_phases model (word K p) K p phase
  exact ⟨h.trans (hSpace p), h.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualInputHeadline
