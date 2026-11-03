import Blotto.GeneralPaperMeasuredDispatchResources

/-! Sharp source time at any positive logarithmic reference above the
native analysis calibration. This is a proof parameter, not a capacity
oracle or an additional executed preparation pass. -/
namespace Blotto.GeneralPaperEnlargedReferenceSourceTime
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperOriginalSourceDriverConstructionStorage
open GeneralPaperNativeSourceTimeRates (rate rate_positive originalLog original_log_tight native_log_le_original whole_at_one_rate initialCursor)
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

structure Reference (model : RationalCostModel) (C d : ℕ) where
  word : Problem → ℕ
  positive : ∀ p, 1 ≤ word p
  tight : Tight word (logarithm model)
  above : ∀ p, GeneralPaperNativeResourceReferenceGrowth.word model C d p ≤ word p

theorem word_original_log {model : RationalCostModel} {C d : ℕ} (cal : Reference model C d) :
    Tight (cal.word) originalLog := by
  obtain ⟨K,hK⟩ := cal.tight
  refine ⟨K*4,?_⟩
  intro p
  exact (hK p).trans ((Nat.mul_le_mul_left K (native_log_le_original model p)).trans_eq (by ring))

theorem value_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (fun p => GeneralPaperOriginalSourceValuePrice.bitPrice model (cal.word p) (exponent p) p.values)
      (fun p => ledger p+1) (logarithm model) := by
  obtain ⟨K,hK⟩ := word_original_log cal
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
  exact GeneralPaperOriginalValueBitDriverRate.value_price hg K (cal.word p) (exponent p) (ledger p)
    p.values p.selector p.correct (hK p)

theorem whole_at_reference_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (fun p => GeneralPaperFastWholeDriverStorage.price model C d (cal.word p) (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (rate model) (logarithm model) :=
  profile_at_word (fun W p => GeneralPaperFastWholeDriverStorage.price model C d W (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)) (cal.word) (rate model) (logarithm model)
    (fun p => whole_price_scaling model C d (reduced model p).m (exponent p) (prepared model p).Qv (ledger p))
    (cal.positive) (cal.tight) (whole_at_one_rate hg)
noncomputable def price (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (p : Problem) : ℕ :=
  GeneralPaperOriginalSourceValuePrice.bitPrice model (cal.word p) (exponent p) p.values+
    GeneralPaperFastWholeDriverStorage.price model C d (cal.word p) (reduced model p).m (exponent p)
      (prepared model p).Qv (ledger p)+128*cal.word p

theorem price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (price model C d cal) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hValue := rate_mono (value_price_rate hg cal) (fun p => show ledger p+1≤rate model p by unfold rate;omega)
  have hWhole := whole_at_reference_rate hg cal
  have hWord := polylog_of_tight (cal.tight)
  unfold price
  fun_prop

theorem native_source_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    let W := cal.word p
    (GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid).2≤price model C d cal p := by
  let W := cal.word p
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W (exponent p) p.values p.selector p.correct).1
  let x := GeneralPaperOriginalSourceValuePreparation.input actual (exponent p) (ledger p) p.budget p.budget_valid (source model p).hB
  have hm : 0<x.m := (GeneralPaperOriginalSourceValuePreparation.count_bounds true model W (exponent p) p.values p.selector p.correct).1
  have hFloor : GeneralPaperFastDriverReference.width C d x≤W := (GeneralPaperNativeReferenceEnlargement.floors_above model C d p W (cal.above p)).2.1
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

end Blotto.GeneralPaperEnlargedReferenceSourceTime
