import Blotto.GeneralPaperMeasuredUnequalInitializationRates

/-! Complete time of the one-pass measured unequal producer, including the
executed initializer and wrapper. The reference bundle is erased analysis. -/
namespace Blotto.GeneralPaperMeasuredUnequalTime
open GeneralPaperNativeResourceDomain GeneralPaperUniformResourceGrowth
open GeneralPaperEnlargedReferenceSourceTime (Reference)
open GeneralPaperNativeSourceTimeRates (rate rate_positive)
open GeneralPaperNativeSourceTimeHeadline (timeScale structural_scale)
open GeneralPaperNativeWorkingSpaceHeadline (epsilon paperLog log_comparison)
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

noncomputable def price (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (K : ℕ) (p : Problem) : ℕ :=
  GeneralPaperMeasuredUnequalInitializationRates.work model K p +
    GeneralPaperEnlargedReferencePreparationTime.bitPrice model C d cal p + 64 * (1 + cal.word p + 1)

theorem price_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K) :
    Bound (price model C d cal K) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hInit := rate_mono (GeneralPaperMeasuredUnequalInitializationRates.rate model ⟨C, d, hg⟩ K hK)
    (fun p => show ledger p + 1 ≤ rate model p by unfold rate; omega)
  have hBit := GeneralPaperEnlargedReferencePreparationTime.bit_price_rate hg cal
  have hWord := polylog_of_tight cal.tight
  unfold price
  fun_prop

theorem work_bound {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) (p : Problem) :
    (GeneralPaperMeasuredUnequalPreparation.run model 1 K (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2).2 ≤
      price model C d cal K p := by
  let input := GeneralPaperMeasuredReferenceGrowth.original p
  let initial := GeneralPaperOriginalMeasuredReference.prepare model 1 K input
  have hw : initial.1.2 = cal.word p :=
    (GeneralPaperOriginalMeasuredReference.word model 1 K input).trans (congrFun hWord p).symm
  have hWords : initial.1.1.words = p.words := rfl
  have hc := GeneralPaperClosedParsedPreparation.work_le model initial.1.2 initial.1.2 initial.1.2
    initial.1.1 p.values p.selector p.correct p.budget p.budget_valid
  rw [hw, hWords] at hc
  have hb := GeneralPaperEnlargedReferencePreparationTime.native_bit_work hg cal p
  change initial.2 + (GeneralPaperClosedParsedPreparation.run model initial.1.2 initial.1.2 initial.1.2
    initial.1.1 p.values p.selector p.correct p.budget p.budget_valid).2 + 64 * (1 + initial.1.2 + 1) ≤
    initial.2 + GeneralPaperEnlargedReferencePreparationTime.bitPrice model C d cal p + 64 * (1 + cal.word p + 1)
  rw [hw]
  exact Nat.add_le_add_right (Nat.add_le_add_left (hc.trans hb) initial.2) _

theorem preparation_rate {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    Bound (fun p => (GeneralPaperMeasuredUnequalPreparation.run model 1 K
      (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2).2) (rate model) (logarithm model) :=
  dominated (price_rate hg cal K hK) (work_bound hg cal K hWord)

theorem preparation_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (K : ℕ) (hK : 1 ≤ K)
    (hWord : cal.word = GeneralPaperMeasuredReferenceGrowth.word model K) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      ((GeneralPaperMeasuredUnequalPreparation.run model 1 K (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2).2:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := preparation_rate hg cal K hK hWord
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : ((GeneralPaperMeasuredUnequalPreparation.run model 1 K (GeneralPaperMeasuredReferenceGrowth.original p) p.budget_valid.2).2:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring


end Blotto.GeneralPaperMeasuredUnequalTime
