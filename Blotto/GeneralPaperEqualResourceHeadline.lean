import Blotto.GeneralPaperEqualOriginalInputRates

/-! Paper epsilon/input-length forms of the measured grouped-equal bit
preparation bounds. Native phase space/capacity is simultaneous at the same
constructed word. Initializer cursor space and representation joins remain open. -/
namespace Blotto.GeneralPaperEqualResourceHeadline
open GeneralPaperEqualResourceDomain GeneralPaperEqualOriginalInputRates GeneralPaperUniformResourceGrowth
set_option autoImplicit false
set_option maxHeartbeats 2400000
set_option maxRecDepth 4096

def epsilon {model : RationalCostModel} (p : Problem model) : ℚ :=
  (p.words.numerator.value : ℚ) / p.words.denominator.value

theorem epsilon_positive {model : RationalCostModel} (p : Problem model) : 0 < epsilon p :=
  div_pos (by exact_mod_cast p.words.numerator.value_pos) (by exact_mod_cast p.words.denominator.value_pos)

theorem exponent_exact {model : RationalCostModel} (p : Problem model) :
    p.k = (GeneralPaperDyadicAccuracy.prepare (epsilon p)).exponent :=
  p.exponent_correct.trans (GeneralPaperBinaryAccuracy.exact_exponent id 1 p.words (epsilon p) rfl)

def inputSize {model : RationalCostModel} (p : Problem model) : ℕ := originalSize p + budgetSize p + accuracySize p + 1

theorem ledger_bound {model : RationalCostModel} (p : Problem model) : ledger p ≤ 2 * inputSize p := by
  have hn := GeneralPaperOriginalValueBitDriverRate.input_fields p.values
  change p.n ≤ originalSize p at hn
  unfold ledger inputSize
  omega

def paperLog {model : RationalCostModel} (p : Problem model) : ℕ :=
  129 + binaryWordWidth ⌈(epsilon p)⁻¹⌉₊ + binaryWordWidth (inputSize p + 1)

theorem log_comparison {model : RationalCostModel} (p : Problem model) : logarithm p ≤ 2 * paperLog p := by
  have hk := GeneralPaperRealHeadlineParameters.exponent_bound (epsilon p)
  rw [← exponent_exact p] at hk
  have h0 := binaryWordWidth_mono (ledger_bound p)
  have h1 := binaryWordWidth_mul 2 (inputSize p)
  have h2 : binaryWordWidth 2 = 2 := by decide
  have hi := binaryWordWidth_mono (show inputSize p ≤ inputSize p + 1 by omega)
  unfold logarithm paperLog
  omega

theorem word_tight (model : RationalCostModel) (K : ℕ) :
    Tight (GeneralPaperEqualCommonReference.word K (model := model)) paperLog := by
  refine ⟨2 * K, fun p => ?_⟩
  exact (Nat.mul_le_mul_left K (log_comparison p)).trans_eq (by ring)

theorem transfer_rate {model : RationalCostModel} {f : Problem model → ℕ} (hf : Bound f ledger logarithm) :
    ∃ A e : ℕ, ∀ p, f p ≤ A * inputSize p * (paperLog p) ^ e := by
  obtain ⟨A, e, hA⟩ := hf
  refine ⟨2 * A * 2 ^ e, e, fun p => ?_⟩
  have h := (hA p).trans (Nat.mul_le_mul (Nat.mul_le_mul_left A (ledger_bound p))
    (Nat.pow_le_pow_left (log_comparison p) e))
  exact h.trans_eq (by rw [mul_pow]; ring)

theorem bit_time (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) (K : ℕ) :
    ∃ A e : ℕ, ∀ p : Problem model, totalWork model K p ≤ A * inputSize p * (paperLog p) ^ e :=
  transfer_rate (total_work_rate model hFast K)

/-- Complete measured initialization and native source time, with sharp native
post-initializer phase space and capacity; all use one computed common word. -/
theorem measured_time_native_space (model : RationalCostModel) (hFast : GeneralPaperFastRationalModel.IsFast model) :
    ∃ K At et As es : ℕ, 1 ≤ K ∧ ∀ p : Problem model,
      let W := GeneralPaperEqualCommonReference.word K p
      let initial := GeneralPaperEqualCommonReference.prepareReference model W K p
      initial.1.1 = p.k ∧ initial.1.2 = W ∧ totalWork model K p ≤ At * inputSize p * (paperLog p) ^ et ∧
      ∀ phase : GeneralPaperEqualCommonReference.Phase model W p,
        GeneralPaperEqualCommonReference.window model W p phase ≤ As * inputSize p * (paperLog p) ^ es ∧
        GeneralPaperEqualCommonReference.window model W p phase < 2 ^ W := by
  obtain ⟨K, hK, hSafe⟩ := GeneralPaperEqualCommonReference.uniform_capacity model hFast
  obtain ⟨At, et, hTime⟩ := bit_time model hFast K
  obtain ⟨As, es, hSpace⟩ := transfer_rate (reserve_rate model hFast K hK)
  refine ⟨K, At, et, As, es, hK, fun p => ?_⟩
  refine ⟨GeneralPaperEqualCommonReference.initialized_exponent model _ K p,
    GeneralPaperEqualCommonReference.initialized_word model _ K p, hTime p, fun phase => ?_⟩
  have h := GeneralPaperEqualCommonReference.native_window_bound model (GeneralPaperEqualCommonReference.word K p) p phase
  exact ⟨h.trans (hSpace p), h.trans_lt (hSafe p)⟩

end Blotto.GeneralPaperEqualResourceHeadline
