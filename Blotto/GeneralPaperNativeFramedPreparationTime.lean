import Blotto.GeneralPaperNativePreparationTimeHeadline

/-! The encoded accuracy-frame interface at the same actual-input word.
Parsing success and exponent/length calibration are proved for the canonical
encoding. Frame work adds only its linear input term and the closed core. -/
namespace Blotto.GeneralPaperNativeFramedPreparationTime
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperUniformResourceGrowth GeneralPaperNativeSourceTimeRates GeneralPaperNativePreparationTimeRates
open GeneralPaperNativeWorkingSpaceHeadline (epsilon epsilon_positive exponent_exact paperLog log_comparison)
open GeneralPaperNativeSourceTimeHeadline (timeScale structural_scale)
open GeneralPaperOriginalSourceDriverConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option maxRecDepth 16384

def frame (p : Problem) : List Bool := BinaryAccuracyFrame.encode p.words.numeric

theorem frame_length (p : Problem) : (frame p).length=accuracySize p := by
  unfold frame accuracySize GeneralPaperBinaryAccuracyConstructionStorage.inputSize
  rw [BinaryAccuracyFrame.encode_length]
  change 2*(binaryWordWidth p.words.numerator.value+binaryWordWidth p.words.denominator.value)+2=_
  rw [←p.words.numerator.width_eq,←p.words.denominator.width_eq]
  omega

theorem canonical_reader (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) (word model C d p) (frame p)).1=some (parsed,[]) ∧
      parsed.exponent=exponent p := by
  obtain ⟨parsed,hr,hn⟩ := GeneralPaperBinaryAccuracy.read_complete (fun w => w) (word model C d p) p.words.numeric []
  have hNum := congrArg BinaryAccuracyInput.numerator hn
  have hDen := congrArg BinaryAccuracyInput.denominator hn
  change parsed.words.numerator.value=p.words.numerator.value at hNum
  change parsed.words.denominator.value=p.words.denominator.value at hDen
  have hk := parsed.correct
  rw [hDen,hNum] at hk
  have hBase := GeneralPaperBinaryAccuracy.prepare_data (fun w => w) 1 p.words
  exact ⟨parsed,by simpa only [frame,List.append_nil] using hr,hk.trans hBase.symm⟩

theorem frame_accuracy_floor (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    1+binaryWordWidth (accuracySize p+1)≤word model C d p :=
  GeneralPaperFullPreparationReference.accuracy_floor model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)

noncomputable def framePrice (model : RationalCostModel) (C d : ℕ) (p : Problem) : ℕ :=
  256*(accuracySize p+1)*word model C d p+strategyPrice model C d p+128*word model C d p+
    GeneralPaperClosedStrategyConstructionStorage.closePrice (word model C d p) (rows model p) (exponent p)+128*word model C d p

theorem frame_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    Bound (framePrice model C d) (rate model) (logarithm model) := by
  have hL := logarithm_positive model
  have hR := rate_positive model
  have hStrategy := strategy_price_rate hg
  have hClose := close_at_common_word_rate hg
  have hWord := polylog_of_tight (GeneralPaperNativeResourceReferenceGrowth.word_tight hg)
  have hEncoding := rate_mono (GeneralPaperNativeWorkingResourceRates.accuracy_bound model) (working_rate_le model)
  unfold framePrice
  fun_prop

theorem native_frame_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (p : Problem) (input : List Bool) (hc : input.length≤accuracySize p) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hr : (GeneralPaperBinaryAccuracy.read (fun w => w) (word model C d p) input).1=some parsed)
    (hk : parsed.1.exponent=exponent p) :
    let W := word model C d p
    (GeneralPaperClosedStrategyDriver.frame model W W W input p.values p.selector p.correct p.budget p.budget_valid).2≤framePrice model C d p := by
  let W := word model C d p
  let raw := GeneralPaperAccuracyStrategyDriver.frame model W W W input p.values p.selector p.correct p.budget p.budget_valid
  let made := (GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.1.exponent p.values p.selector p.correct p.budget p.budget_valid).1
  have hCap : 1+binaryWordWidth (input.length+1)≤W :=
    (Nat.add_le_add_left (binaryWordWidth_mono (Nat.add_le_add_right hc 1)) 1).trans (frame_accuracy_floor model C d p)
  have hAccuracy := GeneralPaperAccuracyStrategyDriver.frame_work model W W W input p.values p.selector p.correct p.budget p.budget_valid parsed hr hCap
  have hCore := native_strategy_work hg p
  rw [hk] at hAccuracy
  have hRaw : raw.1=some (made,parsed.2) := (GeneralPaperAccuracyStrategyDriver.frame_some model W W W input
    p.values p.selector p.correct p.budget p.budget_valid parsed hr).1
  have hData : made.strategies.original.reduced=reduced model p := by
    change (GeneralPaperOriginalStrategyDriver.bit model W W W parsed.1.exponent p.values p.selector p.correct p.budget p.budget_valid).1.original.reduced=_
    rw [GeneralPaperOriginalStrategyDriver.bit_original,hk,GeneralPaperOriginalSourceDataCalibration.reduced_models]
    rfl
  have hClose := GeneralPaperClosedStrategyConstructionStorage.close_work W made
  unfold GeneralPaperClosedSamplerConstructionStorage.rows at hClose
  conv at hClose =>
    rhs
    rw [hData]
    change GeneralPaperClosedStrategyConstructionStorage.closePrice W
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet (reduced model p).m parsed.1.exponent).lambda parsed.1.exponent).rows parsed.1.exponent
    rw [hk]
  have hInput := Nat.mul_le_mul_right W (Nat.mul_le_mul_left 256 (Nat.add_le_add_right hc 1))
  have hRaw' : (GeneralPaperAccuracyStrategyDriver.frame model W W W input p.values p.selector p.correct p.budget p.budget_valid).1=some (made,parsed.2) := hRaw
  have hShape : (GeneralPaperClosedStrategyDriver.frame model W W W input p.values p.selector p.correct p.budget p.budget_valid).2=
      raw.2+(GeneralPaperClosedStrategyDriver.close (fun w => w) W made).2+128*W := by
    simp only [GeneralPaperClosedStrategyDriver.frame,hRaw']
    rfl
  change _≤256*(accuracySize p+1)*W+strategyPrice model C d p+128*W+
    GeneralPaperClosedStrategyConstructionStorage.closePrice W (rows model p) (exponent p)+128*W
  rw [hShape]
  exact Nat.add_le_add_right (Nat.add_le_add (hAccuracy.trans (Nat.add_le_add_right (Nat.add_le_add hInput hCore) _)) hClose) _


theorem frame_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (p : Problem) (input : List Bool) (hc : input.length≤accuracySize p) (parsed : GeneralPaperBinaryAccuracy.Parsed×List Bool)
    (hk : parsed.1.exponent=exponent p) :
    let W := word model C d p
    ∀ (_hr : (GeneralPaperBinaryAccuracy.read (fun w => w) W input).1=some parsed),
      let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.1.exponent p.values p.selector p.correct).1
      ∀ (cS : SourceCursor actual.reduced.m parsed.1.exponent actual.Qv)
        (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows parsed.1.exponent actual.reduced)),
        let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.1.exponent p.values p.selector p.correct p.budget p.budget_valid).1,parsed.2)
        let observed := GeneralPaperClosedStrategyConstructionStorage.frameWindow model W input p.values p.selector p.correct p.budget p.budget_valid raw
          (GeneralPaperFramedStrategyConstructionStorage.window model W input parsed p.values p.selector p.correct p.budget p.budget_valid cS cD)
        observed≤reserve model C d W p ∧ observed<2^W ∧
          GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W input p.values p.selector p.correct p.budget p.budget_valid<2^W := by
  dsimp only
  intro hr cS cD
  let W := word model C d p
  have h := GeneralPaperNativePreparationReferenceContract.frame_contract hg (accuracySize p) (ledger p) input hc parsed
    p.values p.selector p.correct p.budget p.budget_valid (source model p).hB
  have hWord : GeneralPaperNativePreparationReferenceContract.width model C d (accuracySize p) parsed.1.exponent (ledger p)
      p.values p.selector p.correct p.budget p.budget_valid (source model p).hB=W := by
    rw [hk]
    rfl
  dsimp only at h
  rw [hWord] at h
  have hActual := h hr cS cD
  have hReserve : GeneralPaperNativePreparationReferenceContract.reserve model C d W (accuracySize p) parsed.1.exponent (ledger p)
      p.values p.selector p.correct p.budget p.budget_valid (source model p).hB=reserve model C d W p := by
    rw [hk]
    rfl
  exact ⟨hActual.1.trans_eq hReserve,hActual.2⟩

theorem frame_price_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      (framePrice model C d p:ℚ)≤(A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := frame_price_rate hg
  refine ⟨A*3241792*4^e,e,?_⟩
  intro p hOne
  have hRate := structural_scale model p hOne
  have hLog := log_comparison model p
  have hNat := (hA p).trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hLog e))
  have hCast : (framePrice model C d p:ℚ)≤
      (A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := by exact_mod_cast hNat
  calc
    _≤(A:ℚ)*(rate model p:ℚ)*((4:ℚ)*(paperLog p:ℚ))^e := hCast
    _≤(A:ℚ)*(3241792*timeScale p)*((4:ℚ)*(paperLog p:ℚ))^e := by gcongr
    _= _ := by push_cast;rw [mul_pow];ring


theorem canonical_frame_time_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      let W := word model C d p
      ((GeneralPaperClosedStrategyDriver.frame model W W W (frame p) p.values p.selector p.correct p.budget p.budget_valid).2:ℚ)≤
        (A:ℚ)*timeScale p*(paperLog p:ℚ)^e := by
  obtain ⟨A,e,hA⟩ := frame_price_headline hg
  refine ⟨A,e,?_⟩
  intro p hOne
  obtain ⟨parsed,hr,hk⟩ := canonical_reader model C d p
  exact (Nat.cast_le.mpr (native_frame_work hg p (frame p) (frame_length p).le (parsed,[]) hr hk)).trans (hA p hOne)

theorem canonical_frame_space_headline {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ p : Problem,epsilon p<1 →
      let W := word model C d p
      ∃ parsed,(GeneralPaperBinaryAccuracy.read (fun w => w) W (frame p)).1=some (parsed,[]) ∧ parsed.exponent=exponent p ∧
        let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W parsed.exponent p.values p.selector p.correct).1
        ∀ (cS : SourceCursor actual.reduced.m parsed.exponent actual.Qv)
          (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows parsed.exponent actual.reduced)),
          let raw := ((GeneralPaperAccuracyStrategyDriver.bitFromExponent model W W W parsed.exponent p.values p.selector p.correct p.budget p.budget_valid).1,([]:List Bool))
          let observed := GeneralPaperClosedStrategyConstructionStorage.frameWindow model W (frame p) p.values p.selector p.correct p.budget p.budget_valid raw
            (GeneralPaperFramedStrategyConstructionStorage.window model W (frame p) (parsed,[]) p.values p.selector p.correct p.budget p.budget_valid cS cD)
          (observed:ℚ)≤(A:ℚ)*GeneralPaperNativeWorkingSpaceHeadline.spaceScale p*(paperLog p:ℚ)^e ∧ observed<2^W ∧
            GeneralPaperClosedStrategyConstructionStorage.frameReturnedFoot model W (frame p) p.values p.selector p.correct p.budget p.budget_valid<2^W := by
  obtain ⟨A,e,hA⟩ := GeneralPaperNativeWorkingSpaceHeadline.complete_reserve_headline hg
  refine ⟨A,e,?_⟩
  intro p hOne
  obtain ⟨parsed,hr,hk⟩ := canonical_reader model C d p
  refine ⟨parsed,hr,hk,?_⟩
  dsimp only
  intro cS cD
  have h := frame_contract hg p (frame p) (frame_length p).le (parsed,[]) hk hr cS cD
  exact ⟨(Nat.cast_le.mpr h.1).trans (hA p hOne),h.2⟩

end Blotto.GeneralPaperNativeFramedPreparationTime
