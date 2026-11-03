import Blotto.GeneralPaperNativeSourceTimeRates

/-! The actual original-value/source phase at the common native word has
the paper nStar^3/epsilon^6 bit-time rate with additive input lengths. This
phase excludes later strategy description, accuracy and closure work. -/
namespace Blotto.GeneralPaperNativeSourceTimeHeadline
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeSourceTimeRates
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive exponent_exact paperLog log_comparison)
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

def timeScale (p : Problem) : ℚ :=
  ((ledger p+1:ℕ):ℚ)+(GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p))^3/(epsilon p)^6

theorem structural_scale (model : RationalCostModel) (p : Problem) (hOne : epsilon p<1) :
    (rate model p:ℚ)≤3241792*timeScale p := by
  let N := GeneralPaperRealHeadlineParameters.nStar p.n (epsilon p)
  have hStar : 1≤N := GeneralPaperRealHeadlineParameters.nstar_positive p.n p.selector.fields_positive
    (epsilon p) (epsilon_positive p) hOne
  have hM : ((reduced model p).m:ℚ)≤36*N := by
    have h := GeneralPaperOriginalSourceValueContract.dyadic_field_count false model 1 (epsilon p) (epsilon_positive p) hOne
      p.values p.selector p.correct
    rw [←exponent_exact p] at h
    exact h
  have hPower : (2:ℚ)^(exponent p)≤2/epsilon p := by
    rw [exponent_exact p]
    exact GeneralPaperRealHeadlineParameters.power_bound (epsilon p) (epsilon_positive p) hOne
  have hM' : ((reduced model p).m:ℚ)+1≤37*N := by linarith only [hM,hStar]
  have hM3 : (((reduced model p).m:ℚ)+1)^3≤(37*N)^3 := by gcongr
  have hP6 : ((2:ℚ)^(exponent p))^6≤(2/epsilon p)^6 := by gcongr
  have hProduct := mul_le_mul hM3 hP6 (by positivity) (by positivity)
  have hProduct' : (((reduced model p).m:ℚ)+1)^3*((2:ℚ)^(exponent p))^6≤3241792*(N^3/(epsilon p)^6) :=
    hProduct.trans_eq (by ring)
  have hBase : ((ledger p+1:ℕ):ℚ)≤3241792*((ledger p+1:ℕ):ℚ) := by nlinarith only [Nat.cast_nonneg (α:=ℚ) (ledger p+1)]
  have hTotal := add_le_add hBase hProduct'
  calc
    (rate model p:ℚ)=((ledger p+1:ℕ):ℚ)+(((reduced model p).m:ℚ)+1)^3*((2:ℚ)^(exponent p))^6 := by
      simp only [rate,GeneralPaperSourceRateAlgebra.monomial,GeneralPaperNativeSourceRates.fields,
        GeneralPaperNativeSourceRates.accuracy,pow_zero,Nat.mul_one,source_count,source_exponent,prepared,reduced,
        Nat.cast_add,Nat.cast_one,Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat]
    _≤3241792*((ledger p+1:ℕ):ℚ)+3241792*(N^3/(epsilon p)^6) := hTotal
    _=3241792*timeScale p := by unfold timeScale;dsimp only [N];ring

theorem source_price_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (price model C d p:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := price_rate hg
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (price model C d p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring

theorem native_source_time_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      let W := word model C d p
      ((GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
        (A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := source_price_headline hg
  exact ⟨A,e,fun p hOne => (Nat.cast_le.mpr (native_source_work hg p)).trans (hA p hOne)⟩

end Blotto.GeneralPaperNativeSourceTimeHeadline
