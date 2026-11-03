import Blotto.GeneralPaperNativeWorkingSpaceHeadline

/-! Original-length fast bit time for the actual native source caller at
its internally calibrated common word. Value and source work keep original
precision additive. No prior source-word restriction is imposed on the caller. -/
namespace Blotto.GeneralPaperNativeSourceTimeRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384

def rate (model : RationalCostModel) (p : Problem) : ℕ :=
  ledger p+1+GeneralPaperSourceRateAlgebra.monomial 3 0 6 (source model p)

theorem rate_positive (model : RationalCostModel) : ∀ p,1≤rate model p := by intro p;unfold rate;omega

theorem working_rate_le (model : RationalCostModel) (p : Problem) : GeneralPaperNativeWorkingResourceRates.rate model p≤rate model p := by
  have h := GeneralPaperSourceRateAlgebra.monomial_mono (a:=3) (b:=0) (c:=4) (a':=3) (b':=0) (c':=6) (by omega) (by omega) (by omega) (source model p)
  unfold rate GeneralPaperNativeWorkingResourceRates.rate
  omega

def originalLog (p : Problem) : ℕ :=
  GeneralPaperOriginalValueBitDriverRate.originalLog p.n (exponent p) (ledger p) (originalSize p)

theorem original_log_tight (model : RationalCostModel) : Tight originalLog (logarithm model) := by
  have hL := logarithm_positive model
  unfold originalLog GeneralPaperOriginalValueBitDriverRate.originalLog GeneralPaperOriginalSourceValueContract.inputLog
  fun_prop

theorem native_log_le_original (model : RationalCostModel) (p : Problem) : logarithm model p≤4*originalLog p := by
  have h := (GeneralPaperOriginalSourceValueContract.original_log_bound false model 1 (exponent p) (ledger p)
    p.values p.selector p.correct p.budget p.budget_valid (source model p).hB).1
  change logarithm model p≤4*GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) (ledger p) at h
  have hInput : GeneralPaperOriginalSourceValueContract.inputLog p.n (exponent p) (ledger p)≤originalLog p := by
    unfold originalLog GeneralPaperOriginalValueBitDriverRate.originalLog
    omega
  exact h.trans (Nat.mul_le_mul_left 4 hInput)

theorem common_word_original_log {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Tight (word model C d) originalLog := by
  obtain ⟨K,hK⟩ := GeneralPaperNativeResourceReferenceGrowth.word_tight hg
  refine ⟨K*4,?_⟩
  intro p
  exact (hK p).trans ((Nat.mul_le_mul_left K (native_log_le_original model p)).trans_eq (by ring))

theorem value_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperOriginalSourceValuePrice.bitPrice model (word model C d p) (exponent p) p.values)
      (fun p => ledger p+1) (logarithm model) := by
  obtain ⟨K,hK⟩ := common_word_original_log hg
  have hL := logarithm_positive model
  have hR : ∀ p : Problem,1≤ledger p+1 := by intro p;omega
  have hLog := polylog_of_tight (original_log_tight model)
  have hInput : Bound (fun p => originalSize p+p.n+1) (fun p => ledger p+1) (logarithm model) :=
    pointwise _ _ _ 2 (fun p => by
      have hn := GeneralPaperNativeWorkingResourceRates.count_ledger p
      have hs : originalSize p≤ledger p := by unfold ledger originalInputSize;omega
      omega)
  apply dominated (g:=fun p =>
    (C*2^28*(2*binaryWordWidth (K+1)+40)^d*(1+(K+1)^2))*(originalSize p+p.n+1)*(originalLog p)^(d+2)) (by fun_prop)
  intro p
  exact GeneralPaperOriginalValueBitDriverRate.value_price hg K (word model C d p) (exponent p) (ledger p)
    p.values p.selector p.correct (hK p)

theorem whole_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperFastWholeDriverStorage.price model C d 1 (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (rate model) (logarithm model) := by
  have h := pullback_source_bound (GeneralPaperFastDriverSharpWork.actual_price_rate hg (fun _ => 1)
    (GeneralPaperSourceWordGrowth.tight_constant 1)) (source model)
  apply rate_comparison h ((18+1)^2+18+3)
  intro p
  apply GeneralPaperFastDriverSharpWork.input_collapse (source model p) 18
  have hm := (GeneralPaperOriginalSourceValuePreparation.count_bounds false model 1 (exponent p) p.values p.selector p.correct).2.2
  exact hm.le

theorem whole_at_common_word_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperFastWholeDriverStorage.price model C d (word model C d p) (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (rate model) (logarithm model) :=
  profile_at_word (fun W p => GeneralPaperFastWholeDriverStorage.price model C d W (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (word model C d) (rate model) (logarithm model)
    (fun p => whole_price_scaling model C d (reduced model p).m (exponent p) (prepared model p).Qv (ledger p))
    (word_positive model C d) (GeneralPaperNativeResourceReferenceGrowth.word_tight hg) (whole_at_one_rate hg)


def initialCursor (m k Qv : ℕ) : SourceCursor m k Qv where
  exponent := 0
  target := m
  hExponent := by omega
  hTarget := Or.inl rfl
  material := ⟨0,0,0,0,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  cursor := 0
  hCursor := Nat.zero_le _
  outer := 0
  hOuter := Nat.zero_le _
  inner := 0
  hInner := Nat.zero_le _

noncomputable def price (model : RationalCostModel) (C d : ℕ) (p : Problem) : ℕ :=
  GeneralPaperOriginalSourceValuePrice.bitPrice model (word model C d p) (exponent p) p.values+
    GeneralPaperFastWholeDriverStorage.price model C d (word model C d p) (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)+128*word model C d p

theorem price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (price model C d) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hValue := rate_mono (value_price_rate hg) (fun p => show ledger p+1≤rate model p by unfold rate;omega)
  have hWhole := whole_at_common_word_rate hg
  have hWord := polylog_of_tight (GeneralPaperNativeResourceReferenceGrowth.word_tight hg)
  unfold price
  fun_prop

theorem native_source_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (p : Problem) :
    let W := word model C d p
    (GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid).2≤price model C d p := by
  let W := word model C d p
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W (exponent p) p.values p.selector p.correct).1
  let x := GeneralPaperOriginalSourceValuePreparation.input actual (exponent p) (ledger p) p.budget p.budget_valid (source model p).hB
  have hm : 0<x.m := (GeneralPaperOriginalSourceValuePreparation.count_bounds true model W (exponent p) p.values p.selector p.correct).1
  have hFloor : GeneralPaperFastDriverReference.width C d x≤W := (GeneralPaperNativeResourceWordContract.native_floors model C d p).2.1
  have hPair := (enlarged_source_bound hg W x hm actual.Qv_positive actual.weights_positive hFloor (initialCursor x.m x.k x.Qv)).2
  have hPrep := GeneralPaperOriginalSourceValuePrice.bit_work model W (exponent p) p.values p.selector p.correct
  have hData := GeneralPaperOriginalSourceDataCalibration.reduced_models model W (exponent p) p.values p.selector p.correct
  have hQ := GeneralPaperOriginalSourceDataCalibration.denominator_models model W (exponent p) p.values p.selector p.correct
  have hPairPrice : GeneralPaperFastWholeDriverStorage.price model C d W x.m x.k x.Qv x.B=
      GeneralPaperFastWholeDriverStorage.price model C d W (reduced model p).m (exponent p) (prepared model p).Qv (ledger p) := by
    change GeneralPaperFastWholeDriverStorage.price model C d W actual.reduced.m (exponent p) actual.Qv (ledger p)=_
    dsimp only [actual]
    rw [hData,hQ]
    rfl
  rw [hPairPrice] at hPair
  change _≤GeneralPaperOriginalSourceValuePrice.bitPrice model W (exponent p) p.values+
    GeneralPaperFastWholeDriverStorage.price model C d W (reduced model p).m (exponent p) (prepared model p).Qv (ledger p)+128*W
  exact Nat.add_le_add_right (Nat.add_le_add hPrep hPair) _

theorem native_source_time {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,
      let W := word model C d p
      (GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid).2≤
        A*rate model p*(logarithm model p)^e := by
  obtain ⟨A,e,hA⟩ := price_rate hg
  exact ⟨A,e,fun p => (native_source_work hg p).trans (hA p)⟩

end Blotto.GeneralPaperNativeSourceTimeRates
