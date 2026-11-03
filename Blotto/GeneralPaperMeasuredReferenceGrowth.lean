import Blotto.GeneralPaperOriginalMeasuredReference

/-! The computed original-input word is logarithmic on the unequal domain.
The full preparation reserve retains the same sharp working-space power
when repriced at this word instead of the erased analysis calibration. -/
namespace Blotto.GeneralPaperMeasuredReferenceGrowth
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters
open GeneralPaperUniformResourceGrowth
open GeneralPaperNativeWorkingSpaceHeadline GeneralPaperNativeWorkingResourceRates
open GeneralPaperNativeResourceReferenceGrowth (reserve)
set_option autoImplicit false
set_option maxHeartbeats 3000000
set_option maxRecDepth 16384

def original (p : Problem) : GeneralPaperOriginalGameInput.Input :=
  ⟨p.n, p.values, p.selector, p.correct, p.words, p.budget, ⟨p.budget_valid.1, p.budget_valid.2.le⟩⟩

def word (model : RationalCostModel) (K : ℕ) (p : Problem) : ℕ :=
  K * GeneralPaperOriginalReferenceComparison.logarithm model (original p)

theorem positive (model : RationalCostModel) (K : ℕ) (hK : 1 ≤ K) (p : Problem) : 1 ≤ word model K p := by
  exact Nat.mul_le_mul hK (GeneralPaperEqualInputDomain.logarithm_positive
    (GeneralPaperOriginalGameInput.equalInput model (original p)))

theorem word_tight (model : RationalCostModel) (K : ℕ) : Tight (word model K) (logarithm model) := by
  refine ⟨2 * K, fun p => ?_⟩
  have h : GeneralPaperOriginalReferenceComparison.logarithm model (original p) ≤ 2 * logarithm model p :=
    GeneralPaperOriginalReferenceComparison.measured_log_le model (original p) p.budget_valid.2
  exact (Nat.mul_le_mul_left K h).trans_eq (by ring)

theorem reserve_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (K : ℕ) (hK : 1 ≤ K) :
    Bound (fun p => GeneralPaperNativeResourceReferenceGrowth.reserve model C d (word model K p) p)
      (GeneralPaperNativeWorkingResourceRates.rate model) (logarithm model) :=
  profile_at_word (GeneralPaperNativeResourceReferenceGrowth.reserve model C d)
    (word model K) (GeneralPaperNativeWorkingResourceRates.rate model) (logarithm model)
    (fun p => GeneralPaperFullPreparationReference.scaling model C d (accuracySize p) (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (GeneralPaperNativeResourceReferenceGrowth.height model p)
      (reduced model p) (source model p)) (positive model K hK) (word_tight model K)
    (GeneralPaperNativeWorkingPreparationRates.reserve_at_one_rate hg)

theorem complete_reserve_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (K : ℕ) (hK : 1 ≤ K) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (reserve model C d (word model K p) p:ℚ)≤(A:ℚ)*spaceScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := reserve_rate hg K hK
  refine ⟨A*810448*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (reserve model C d (word model K p) p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(810448*spaceScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring

end Blotto.GeneralPaperMeasuredReferenceGrowth
