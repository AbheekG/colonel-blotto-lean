import Blotto.GeneralPaperEnlargedReferenceSourceTime

/-! Complete unequal bit preparation time at an arbitrary larger logarithmic
word. Every actual phase is bounded at that same word; source, accuracy and
closure work retain the established sharp original-input time scale. -/
namespace Blotto.GeneralPaperEnlargedReferencePreparationTime
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth
open GeneralPaperNativeSourceTimeRates (rate rate_positive working_rate_le)
open GeneralPaperNativeDescriptionTimeRates (attach_at_one_rate)
open GeneralPaperEnlargedReferenceSourceTime (Reference native_source_work)
open GeneralPaperNativePreparationTimeRates (initialDescriptionCursor close_at_one_polylog)
open GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

theorem native_attach_work (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (p : Problem) :
    let W := cal.word p
    let core := GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid
    (GeneralPaperOriginalStrategyDriver.attach model.rat (fun w => w) W core.1
      (GeneralPaperNativeReductionShape.original_shape true model W (exponent p) p.values)
      (GeneralPaperUnreplacedShape.original_shape true model W (exponent p) p.values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive true model W (exponent p) p.values)).2≤
      GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) (height model p) (reduced model p) := by
  let W := cal.word p
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W (exponent p) p.values p.selector p.correct).1
  let core := GeneralPaperOriginalSourceValueDriver.bit model W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid
  let red := actual.reduced
  let H := GeneralPaperSourcePairAnchorHeights.width red.m (exponent p)
  let x := GeneralPaperOriginalSourceValuePreparation.input actual (exponent p) (ledger p) p.budget p.budget_valid (source model p).hB
  let hRep := GeneralPaperNativeReductionShape.original_shape true model W (exponent p) p.values
  let hNo := GeneralPaperUnreplacedShape.original_shape true model W (exponent p) p.values
  let hR := GeneralPaperNativeCircleLoss.original_representatives_positive true model W (exponent p) p.values
  have hFloor := GeneralPaperNativeReferenceEnlargement.floors_above model C d p W (cal.above p)
  have hReference : GeneralPaperFastDriverReference.width C d x≤W := hFloor.2.1
  have hW := cal.positive p
  have hFields := (GeneralPaperFastDriverReference.local_words C d x).2.2.1.trans hReference
  have hRows := (GeneralPaperFastDriverReference.row_words C d x).1.trans hReference
  have hLight : binaryWordWidth (red.classified.light.size+1)≤W := by
    have h := GeneralPaperStrategyPreparationWork.light_size true model W (exponent p) p.values
    exact (binaryWordWidth_mono (Nat.add_le_add_right h 1)).trans hFloor.1
  obtain ⟨physical,hPhysical,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model W W (exponent p)
    p.values p.selector p.correct p.budget p.budget_valid
  have hHeights : ∀ columns,core.1.physical=some columns →
      (∀ j l,RationalHeight ((columns.rich.read j).anchors.read l) H) ∧
      (∀ j l,RationalHeight ((columns.poor.read j).anchors.read l) H) := by
    intro columns hColumns
    have he : columns=physical := Option.some.inj (hColumns.symm.trans hPhysical)
    subst columns
    exact ⟨hRich,hPoor⟩
  have hAttach := (GeneralPaperOriginalStrategyConstructionStorage.attach_bounded model W H core.1 hRep hNo hR
    (GeneralPaperCircleActualWeights.original_sum true model W (exponent p) p.values) hHeights hW hFields hLight hRows
    (initialDescriptionCursor red (GeneralPaperOriginalStrategyConstructionStorage.rows (exponent p) red))).2
  have hData := GeneralPaperOriginalSourceDataCalibration.reduced_models model W (exponent p) p.values p.selector p.correct
  have hPrice : GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) H red=
      GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) (height model p) (reduced model p) := by
    dsimp only [H,red,actual]
    rw [hData]
    rfl
  change _≤GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) H red at hAttach
  rw [hPrice] at hAttach
  exact hAttach

theorem attach_at_reference_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (fun p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model (cal.word p) (exponent p)
      (height model p) (reduced model p)) (rate model) (logarithm model) :=
  profile_at_word (fun W p => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model W (exponent p) (height model p) (reduced model p))
    (cal.word) (rate model) (logarithm model)
    (fun p => GeneralPaperOriginalStrategyConstructionStorage.attach_price_scaling model (exponent p) (height model p) (reduced model p))
    (cal.positive) (cal.tight) (attach_at_one_rate hg)

noncomputable def strategyPrice (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (p : Problem) : ℕ :=
  GeneralPaperEnlargedReferenceSourceTime.price model C d cal p+
    GeneralPaperOriginalStrategyConstructionStorage.attachPrice model (cal.word p) (exponent p) (height model p) (reduced model p)+
    128*cal.word p

theorem strategy_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (strategyPrice model C d cal) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hSource := GeneralPaperEnlargedReferenceSourceTime.price_rate hg cal
  have hAttach := attach_at_reference_rate hg cal
  have hWord := polylog_of_tight (cal.tight)
  unfold strategyPrice
  fun_prop

theorem native_strategy_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    let W := cal.word p
    (GeneralPaperOriginalStrategyDriver.bit model W W W (exponent p) p.values p.selector p.correct p.budget p.budget_valid).2≤
      strategyPrice model C d cal p := by
  have hSource := native_source_work hg cal p
  have hAttach := native_attach_work model C d cal p
  exact Nat.add_le_add_right (Nat.add_le_add hSource hAttach) _


noncomputable def accuracyPrice (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (p : Problem) : ℕ :=
  128*(GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words+1)*cal.word p+
    strategyPrice model C d cal p+128*cal.word p

theorem accuracy_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (accuracyPrice model C d cal) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hStrategy := strategy_price_rate hg cal
  have hWord := polylog_of_tight (cal.tight)
  have hEncoding : Bound (fun p => GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words) (rate model) (logarithm model) :=
    dominated (rate_mono (GeneralPaperNativeWorkingResourceRates.accuracy_bound model) (working_rate_le model))
      (GeneralPaperNativeResourceWordContract.encoding_bound)
  unfold accuracyPrice
  fun_prop

theorem native_accuracy_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    let W := cal.word p
    (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2≤
      accuracyPrice model C d cal p := by
  let W := cal.word p
  have hCap : 1+binaryWordWidth (p.words.numerator.width+p.words.denominator.width+1)≤W := by
    simpa only [GeneralPaperBinaryAccuracyConstructionStorage.inputSize,Nat.add_comm p.words.denominator.width p.words.numerator.width]
      using (GeneralPaperNativeResourceWordContract.accuracy_floor model C d p).trans (cal.above p)
  have h := GeneralPaperAccuracyStrategyDriver.bit_work model W W W p.words p.values p.selector p.correct p.budget p.budget_valid hCap
  have hSize : p.words.numerator.width+p.words.denominator.width=GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words := by
    unfold GeneralPaperBinaryAccuracyConstructionStorage.inputSize
    omega
  rw [hSize] at h
  rw [native_exponent W p] at h
  have hStrategy := native_strategy_work hg cal p
  change _≤128*(GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words+1)*W+strategyPrice model C d cal p+128*W
  exact h.trans (Nat.add_le_add_right (Nat.add_le_add_left hStrategy _) _)

theorem close_at_common_word_rate {model : RationalCostModel} {C d : ℕ} (_hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (fun p => GeneralPaperClosedStrategyConstructionStorage.closePrice (cal.word p) (rows model p) (exponent p))
      (rate model) (logarithm model) :=
  profile_at_word (fun W p => GeneralPaperClosedStrategyConstructionStorage.closePrice W (rows model p) (exponent p))
    (cal.word) (rate model) (logarithm model)
    (fun p => GeneralPaperClosedStrategyConstructionStorage.close_price_scaling (rows model p) (exponent p))
    (cal.positive) (cal.tight)
    (at_positive_rate (close_at_one_polylog model) (rate_positive model))

noncomputable def bitPrice (model : RationalCostModel) (C d : ℕ) (cal : Reference model C d) (p : Problem) : ℕ :=
  accuracyPrice model C d cal p+GeneralPaperClosedStrategyConstructionStorage.closePrice (cal.word p) (rows model p) (exponent p)+
    128*cal.word p

theorem bit_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) :
    Bound (bitPrice model C d cal) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hAccuracy := accuracy_price_rate hg cal
  have hClose := close_at_common_word_rate hg cal
  have hWord := polylog_of_tight (cal.tight)
  unfold bitPrice
  fun_prop

theorem native_bit_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cal : Reference model C d) (p : Problem) :
    let W := cal.word p
    (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2≤
      bitPrice model C d cal p := by
  let W := cal.word p
  let raw := GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid
  have hAccuracy := native_accuracy_work hg cal p
  have hk : raw.1.exponent=exponent p := native_exponent W p
  have hData : raw.1.strategies.original.reduced=reduced model p := by
    change (GeneralPaperOriginalStrategyDriver.bit model W W W (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
      p.values p.selector p.correct p.budget p.budget_valid).1.original.reduced=reduced model p
    rw [GeneralPaperOriginalStrategyDriver.bit_original,native_exponent W p,GeneralPaperOriginalSourceDataCalibration.reduced_models]
    rfl
  have hClose := GeneralPaperClosedStrategyConstructionStorage.close_work W raw.1
  unfold GeneralPaperClosedSamplerConstructionStorage.rows at hClose
  conv at hClose =>
    rhs
    rw [hData,hk]
  change _≤GeneralPaperClosedStrategyConstructionStorage.closePrice W (rows model p) (exponent p) at hClose
  change _≤accuracyPrice model C d cal p+GeneralPaperClosedStrategyConstructionStorage.closePrice W (rows model p) (exponent p)+128*W
  exact Nat.add_le_add_right (Nat.add_le_add hAccuracy hClose) _

end Blotto.GeneralPaperEnlargedReferencePreparationTime
