import Blotto.GeneralPaperNativeWorkingStrategyRates

/-! All outer parsing/closure profiles and the summed native reserve at
the sharp working-space rate, including the actual constructed word. -/
namespace Blotto.GeneralPaperNativeWorkingPreparationRates
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperNativeWorkingResourceRates GeneralPaperNativeWorkingDescriptionRates
open GeneralPaperNativeWorkingStrategyRates GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384

theorem accuracy_rate (model : RationalCostModel) :
    Bound (fun p => GeneralPaperBinaryAccuracyConstructionStorage.profile 1 (accuracySize p)) (rate model) (logarithm model) := by
  have h := pullback_source_bound (GeneralPaperBinaryAccuracyConstructionStorage.profile_rate (fun _ => 1)
    GeneralPaperSourceWordGrowth.Input.B (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.B_small) (source model)
  have hRate := rate_mono h (fun p => show ledger p+1≤rate model p by unfold rate;omega)
  apply dominated hRate
  intro p
  exact GeneralPaperFramedAccuracyConstructionStorage.word_profile_mono 1 (accuracySize p) (ledger p) (by unfold ledger;omega)

theorem positive_read_rate (model : RationalCostModel) :
    Bound (fun p => GeneralPaperPositiveWordReadConstructionStorage.profile 1 (accuracySize p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  unfold GeneralPaperPositiveWordReadConstructionStorage.profile GeneralPaperPositiveWordReadConstructionStorage.inputProfile
    GeneralPaperPositiveWordReadConstructionStorage.returnProfile GeneralPaperAccuracyReadMetadataStorage.stepsProfile
    GeneralPaperAccuracyReadMetadataStorage.lengthProfile GeneralPaperBooleanRulerWorkStorage.budget
  fun_prop (config := {maxSteps := 4000})

theorem reader_rate (model : RationalCostModel) :
    Bound (fun p => GeneralPaperFramedAccuracyConstructionStorage.profile 1 (accuracySize p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hPositive := positive_read_rate model
  have hAccuracy := accuracy_rate model
  have hPrice := reader_price_small model
  unfold GeneralPaperFramedAccuracyConstructionStorage.profile GeneralPaperFramedAccuracyConstructionStorage.returnProfile
    GeneralPaperFramedAccuracyConstructionStorage.cap
  fun_prop

theorem close_extra_polylog (model : RationalCostModel) :
    Polylog (fun p => GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 p.n (rows model p) (labels model p)
      (exponent p) (reduced model p).m) (logarithm model) := by
  have hExtra := GeneralPaperClosedSamplerConstructionStorage.extra_poly (fun _ => 1) GeneralPaperSourceWordGrowth.Input.B
    (fun x => (GeneralPaperTrajectoryParameters.prepare (GeneralPaperSourceWordGrowth.alphabet x).lambda x.k).rows)
    (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).K) GeneralPaperSourceWordGrowth.Input.m
    (GeneralPaperSourceWordGrowth.tight_constant 1) GeneralPaperSourceWordGrowth.B_small
    GeneralPaperNativeSourceWordGrowth.rows_small GeneralPaperCompilerReferenceGrowth.labels_small GeneralPaperSourceWordGrowth.m_small
  have hNative := pullback_source_bound hExtra (source model)
  apply dominated hNative
  intro p
  have hLedger := count_ledger p
  change GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 p.n (rows model p) (labels model p) (exponent p) (reduced model p).m≤
    GeneralPaperClosedSamplerConstructionStorage.extraProfile 1 (ledger p) (rows model p) (labels model p) (exponent p) (reduced model p).m
  unfold GeneralPaperClosedSamplerConstructionStorage.extraProfile GeneralPaperClosedSamplerConstructionStorage.cap
    GeneralPaperSamplerControlsConstructionStorage.extraProfile GeneralPaperSamplerControlsConstructionStorage.cap natBits
  gcongr

theorem raw_profiles_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => GeneralPaperAccuracyStrategyConstructionStorage.profile model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (rate model) (logarithm model) ∧
    Bound (fun p => GeneralPaperFramedStrategyConstructionStorage.profile model C d 1 (accuracySize p) (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (rate model) (logarithm model) ∧
    Bound (fun p => GeneralPaperFramedStrategyConstructionStorage.rejectedProfile 1 (accuracySize p) p.n (originalSize p) (ledger p)) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hRoot := strategy_rate hg
  have hRootPrice := strategy_price_small hg
  have hAccuracy := accuracy_rate model
  have hReader := reader_rate model
  obtain ⟨hBitPrice,hFramePrice,hRejectPrice⟩ := raw_prices_small hg
  have hExp : Bound (fun p => GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile model C d 1 (exponent p)
      (originalSize p) (prepared model p).Qv (ledger p) (height model p) (reduced model p)) (rate model) (logarithm model) := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile GeneralPaperAccuracyStrategyConstructionStorage.ownerTail
      GeneralPaperAccuracyStrategyConstructionStorage.exponentCap GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice
    fun_prop (config := {maxSteps := 4000})
  refine ⟨?_,?_,?_⟩
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.profile GeneralPaperAccuracyStrategyConstructionStorage.cap
    fun_prop (config := {maxSteps := 4000})
  · unfold GeneralPaperFramedStrategyConstructionStorage.profile GeneralPaperFramedStrategyConstructionStorage.cap
    fun_prop (config := {maxSteps := 4000})
  · unfold GeneralPaperFramedStrategyConstructionStorage.rejectedProfile GeneralPaperFramedStrategyConstructionStorage.rejectedCap
    fun_prop (config := {maxSteps := 4000})


theorem denominator_rate (model : RationalCostModel) :
    Bound (fun p => (prepared model p).Qv) (rate model) (logarithm model) := by
  apply pointwise _ _ _ 513
  intro p
  have hQ := GeneralPaperOriginalSourceValuePreparation.denominator false model 1 (exponent p) p.values p.selector p.correct
  change (prepared model p).Qv≤513*(reduced model p).m*2^(exponent p) at hQ
  have hMono : ((reduced model p).m+1)*2^(exponent p)≤GeneralPaperSourceRateAlgebra.monomial 3 0 4 (source model p) := by
    have h := GeneralPaperSourceRateAlgebra.monomial_mono (a:=1) (b:=0) (c:=1) (a':=3) (b':=0) (c':=4) (by omega) (by omega) (by omega) (source model p)
    simpa only [GeneralPaperSourceRateAlgebra.monomial,pow_one,pow_zero,Nat.mul_one,
      GeneralPaperNativeSourceRates.fields,GeneralPaperNativeSourceRates.accuracy,source_count,source_exponent,prepared,reduced] using h
  unfold rate
  nlinarith only [hQ,hMono]

theorem reserve_at_one_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (reserve model C d 1) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  obtain ⟨hBitPrice,hFramePrice,hRejectPrice⟩ := raw_prices_small hg
  obtain ⟨hBit,hFrame,hReject⟩ := raw_profiles_rate hg
  have hClose := close_price_small model
  have hExtra := at_positive_rate (close_extra_polylog model) hR
  have hQ := denominator_rate model
  have hK := polylog_of_tight (exponent_tight model)
  have hSource : Bound (fun p => GeneralPaperFastDriverReference.profile C d 1 (source model p)) (rate model) (logarithm model) :=
    pullback_source_bound (GeneralPaperFastDriverReference.profile_soft C d (fun _ => 1) (GeneralPaperSourceWordGrowth.tight_constant 1)) (source model)
  unfold reserve GeneralPaperFullPreparationReference.reserve GeneralPaperFullPreparationReference.bitProfile
    GeneralPaperFullPreparationReference.frameProfile GeneralPaperFullPreparationReference.rejectedProfile
    GeneralPaperFullPreparationReference.indexSize GeneralPaperClosedStrategyConstructionStorage.frameProfile
    GeneralPaperClosedStrategyConstructionStorage.profile GeneralPaperClosedStrategyConstructionStorage.rejectedProfile
    GeneralPaperClosedStrategyConstructionStorage.cap GeneralPaperClosedStrategyConstructionStorage.price
    GeneralPaperClosedStrategyConstructionStorage.rejectedCap GeneralPaperClosedStrategyConstructionStorage.rejectedPrice
  fun_prop (config := {maxSteps := 4000})

theorem reserve_at_common_word_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (fun p => reserve model C d (word model C d p) p) (rate model) (logarithm model) :=
  profile_at_word (reserve model C d) (word model C d) (rate model) (logarithm model)
    (fun p => GeneralPaperFullPreparationReference.scaling model C d (accuracySize p) (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p))
    (word_positive model C d) (GeneralPaperNativeResourceReferenceGrowth.word_tight hg) (reserve_at_one_rate hg)

theorem native_bit_window_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,
    let W := word model C d p
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
    ∀ (cS : SourceCursor actual.reduced.m k actual.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows k actual.reduced)),
      let observed := GeneralPaperClosedStrategyConstructionStorage.window W
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct p.budget p.budget_valid cS cD)
      observed≤A*rate model p*(logarithm model p)^e ∧ observed<2^W ∧
        GeneralPaperClosedDescriptionStorage.preparedFoot W
          (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1<2^W := by
  obtain ⟨A,e,hA⟩ := reserve_at_common_word_rate hg
  refine ⟨A,e,?_⟩
  intro p
  dsimp only
  intro cS cD
  have h := GeneralPaperNativeResourceWordContract.bit_contract hg p cS cD
  exact ⟨h.1.trans (hA p),h.2⟩

end Blotto.GeneralPaperNativeWorkingPreparationRates
