import Blotto.GeneralPaperOriginalStrategyProfileGrowth

/-! Sum complete actual preparation profile growth before calibrating its
one common reference. Original and accuracy encoding lengths stay additive;
coarse work prices are used only for their encoded metadata. The complete
family theorem is conditional algebra: no_global_native_denominator_match
proves that its universal native matching premise is not instantiable.
Actual uniform native bounds must use the problem domain, not that premise. -/
namespace Blotto.GeneralPaperFullPreparationProfileGrowth
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperEncodedScalarStorage GeneralPaperOriginalStrategyProfileGrowth
open GeneralPaperNativePreparationReferenceContract (data)
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem accuracy_price_small (W E : Input → ℕ) (hW : Small W) (hE : Small E) :
    Small (fun x => GeneralPaperBinaryAccuracyConstructionStorage.price (W x) (E x)) := by
  unfold GeneralPaperBinaryAccuracyConstructionStorage.price GeneralPaperAccuracyCountConstructionStorage.price
    GeneralPaperAccuracyCountConstructionStorage.step GeneralPaperAccuracyCountConstructionStorage.width
  fun_prop

theorem reader_price_small (W E : Input → ℕ) (hW : Small W) (hE : Small E) :
    Small (fun x => GeneralPaperFramedAccuracyConstructionStorage.price (W x) (E x)) := by
  have h := accuracy_price_small W E hW hE
  unfold GeneralPaperFramedAccuracyConstructionStorage.price
  fun_prop

theorem raw_prices {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) (hE : Small E) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    Small (fun x => GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) ∧
    Small (fun x => GeneralPaperAccuracyStrategyConstructionStorage.price model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) ∧
    Small (fun x => GeneralPaperFramedStrategyConstructionStorage.price model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  let S := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  have hw := of_tight hW
  have hRoot := strategy_price_small hg W n values v hv hW hn hS hM hQv
  have hAccuracy := accuracy_price_small W E hw hE
  have hReader := reader_price_small W E hw hE
  have hExp : Small (fun x => GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.exponentPrice
    fun_prop
  refine ⟨hExp,?_,?_⟩
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.price
    fun_prop
  · unfold GeneralPaperFramedStrategyConstructionStorage.price
    fun_prop

theorem raw_rates {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) (hE : Small E) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    AtRate (fun x => GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E ∧
    AtRate (fun x => GeneralPaperAccuracyStrategyConstructionStorage.profile model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E ∧
    AtRate (fun x => GeneralPaperFramedStrategyConstructionStorage.profile model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  let S := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hEncoding : AtRate E n S E := at_E n S E
  have hBudget : AtRate Input.B n S E := at_B n S E
  have hRoot := strategy_rate hg W n E values v hv hW hn hS hM hQv
  obtain ⟨hExpPrice,hWordPrice,hFramePrice⟩ := raw_prices hg W n E values v hv hW hn hS hE hM hQv
  have hExpCap : Small (fun x => GeneralPaperAccuracyStrategyConstructionStorage.exponentCap model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.exponentCap
    fun_prop
  have hExp : AtRate (fun x => GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.exponentProfile GeneralPaperAccuracyStrategyConstructionStorage.ownerTail
    fun_prop (config := {maxSteps := 4000})
  have hWordCap : Small (fun x => GeneralPaperAccuracyStrategyConstructionStorage.cap model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperAccuracyStrategyConstructionStorage.cap
    fun_prop
  have hFrameCap : Small (fun x => GeneralPaperFramedStrategyConstructionStorage.cap model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperFramedStrategyConstructionStorage.cap
    fun_prop
  have hAccuracy : AtRate (fun x => GeneralPaperBinaryAccuracyConstructionStorage.profile (W x) (E x)) n S E := by
    apply rate_mono (GeneralPaperBinaryAccuracyConstructionStorage.profile_rate W E hW hE)
    intro x
    unfold rate
    omega
  have hReader : AtRate (fun x => GeneralPaperFramedAccuracyConstructionStorage.profile (W x) (E x)) n S E := by
    apply rate_mono (GeneralPaperFramedAccuracyConstructionStorage.profile_rate W E hW hE)
    intro x
    unfold rate
    omega
  refine ⟨hExp,?_,?_⟩
  · unfold GeneralPaperAccuracyStrategyConstructionStorage.profile
    fun_prop (config := {maxSteps := 4000})
  · unfold GeneralPaperFramedStrategyConstructionStorage.profile
    fun_prop (config := {maxSteps := 4000})

theorem closed_rate (W n S E T K m P R : Input → ℕ) (hW : Tight W) (hn : Small n)
    (hT : Small T) (hK : Small K) (hm : Small m) (hP : AtRate P n S E) (hR : Small R) :
    AtRate (fun x => GeneralPaperClosedStrategyConstructionStorage.profile (W x) (n x) (T x) (K x) x.k (m x) (P x) (R x)) n S E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hExtra := GeneralPaperClosedSamplerConstructionStorage.extra_poly W n T K m hW hn hT hK hm
  have hControls := GeneralPaperSamplerControlsConstructionStorage.price_poly GeneralPaperClosedSamplerConstructionStorage.index_growth W T hW hT
  have hClose : Polylog (fun x => GeneralPaperClosedStrategyConstructionStorage.closePrice (W x) (T x) x.k) := by
    unfold GeneralPaperClosedStrategyConstructionStorage.closePrice
    fun_prop
  have hCloseSmall := GeneralPaperCacheConstructionGrowth.small_of_poly hClose
  have hCap : Small (fun x => GeneralPaperClosedStrategyConstructionStorage.cap (W x) (n x) (T x) x.k (m x) (R x)) := by
    unfold GeneralPaperClosedStrategyConstructionStorage.cap GeneralPaperClosedStrategyConstructionStorage.price
    fun_prop
  unfold GeneralPaperClosedStrategyConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

theorem closed_frame_rate (W n S E T K m P R : Input → ℕ) (hW : Tight W) (hn : Small n)
    (hT : Small T) (hK : Small K) (hm : Small m) (hP : AtRate P n S E) (hR : Small R) :
    AtRate (fun x => GeneralPaperClosedStrategyConstructionStorage.frameProfile (W x) (E x) (n x) (T x) (K x) x.k (m x) (P x) (R x)) n S E := by
  have h := closed_rate W n S E T K m P R hW hn hT hK hm hP hR
  have hWP := poly_tight W hW
  have hEncoding : AtRate E n S E := at_E n S E
  unfold GeneralPaperClosedStrategyConstructionStorage.frameProfile
  fun_prop

theorem closed_rejected_rate (W n S E P R : Input → ℕ) (hW : Tight W) (hn : Small n) (hP : AtRate P n S E) (hR : Small R) :
    AtRate (fun x => GeneralPaperClosedStrategyConstructionStorage.rejectedProfile (W x) (n x) (P x) (R x)) n S E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hCap : Small (fun x => GeneralPaperClosedStrategyConstructionStorage.rejectedCap (W x) (n x) (R x)) := by
    unfold GeneralPaperClosedStrategyConstructionStorage.rejectedCap GeneralPaperClosedStrategyConstructionStorage.rejectedPrice
    fun_prop
  unfold GeneralPaperClosedStrategyConstructionStorage.rejectedProfile
  fun_prop

theorem rejected_rates (W n S E : Input → ℕ) (hW : Tight W) (hn : Small n) (hE : Small E) :
    Small (fun x => GeneralPaperFramedStrategyConstructionStorage.rejectedPrice (W x) (E x)) ∧
    AtRate (fun x => GeneralPaperFramedStrategyConstructionStorage.rejectedProfile (W x) (E x) (n x) (S x) x.B) n S E ∧
    AtRate (fun x => GeneralPaperFullPreparationReference.rejectedProfile (W x) (E x) (n x) (S x) x.B) n S E := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hReaderPrice := reader_price_small W E hw hE
  have hPrice : Small (fun x => GeneralPaperFramedStrategyConstructionStorage.rejectedPrice (W x) (E x)) := by
    unfold GeneralPaperFramedStrategyConstructionStorage.rejectedPrice
    fun_prop
  have hCap : Small (fun x => GeneralPaperFramedStrategyConstructionStorage.rejectedCap (W x) (E x) (n x)) := by
    unfold GeneralPaperFramedStrategyConstructionStorage.rejectedCap
    fun_prop
  have hReader : AtRate (fun x => GeneralPaperFramedAccuracyConstructionStorage.profile (W x) (E x)) n S E := by
    apply rate_mono (GeneralPaperFramedAccuracyConstructionStorage.profile_rate W E hW hE)
    intro x
    unfold rate
    omega
  have hInput : AtRate S n S E := at_S n S E
  have hCount : AtRate n n S E := at_n n S E
  have hBudget : AtRate Input.B n S E := at_B n S E
  have hProfile : AtRate (fun x => GeneralPaperFramedStrategyConstructionStorage.rejectedProfile (W x) (E x) (n x) (S x) x.B) n S E := by
    unfold GeneralPaperFramedStrategyConstructionStorage.rejectedProfile
    fun_prop (config := {maxSteps := 4000})
  exact ⟨hPrice,hProfile,closed_rejected_rate W n S E _ _ hW hn hProfile hPrice⟩

theorem conditional_full_reserve_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) (hE : Small E) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    AtRate (fun x => GeneralPaperFullPreparationReference.reserve model C d (W x) (E x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced x) n S E := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  let S := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  let T := fun x : Input => GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced
  let K := fun x : Input => (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K
  let m := fun x : Input => (p x).reduced.m
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hm : Small m := by
    apply GeneralPaperSourceWordGrowth.dominated m_small
    intro x
    unfold m
    rw [hM x]
  have hT : Small T := by
    apply GeneralPaperSourceWordGrowth.dominated GeneralPaperNativeSourceWordGrowth.rows_small
    intro x
    unfold T GeneralPaperOriginalStrategyConstructionStorage.rows
    rw [hM x]
    exact le_rfl
  have hK : Small K := by
    apply GeneralPaperSourceWordGrowth.dominated GeneralPaperCompilerReferenceGrowth.labels_small
    intro x
    unfold K
    rw [hM x]
  obtain ⟨_,hBitPrice,hFramePrice⟩ := raw_prices hg W n E values v hv hW hn hS hE hM hQv
  obtain ⟨_,hBitRaw,hFrameRaw⟩ := raw_rates hg W n E values v hv hW hn hS hE hM hQv
  have hBit := closed_rate W n S E T K m _ _ hW hn hT hK hm hBitRaw hBitPrice
  have hFrame := closed_frame_rate W n S E T K m _ _ hW hn hT hK hm hFrameRaw hFramePrice
  have hReject := (rejected_rates W n S E hW hn hE).2.2
  have hSource : AtRate (fun x => GeneralPaperFastDriverReference.profile C d (W x) x) n S E :=
    at_source (GeneralPaperFastDriverReference.profile_soft C d W hW)
  have hInput : AtRate S n S E := at_S n S E
  have hCount : AtRate n n S E := at_n n S E
  have hEncoding : AtRate E n S E := at_E n S E
  have hQRate : AtRate (fun x => (p x).Qv) n S E := by
    have hQBound : ∀ x,(p x).Qv≤513*x.m*2^x.k := by
      intro x
      have h := GeneralPaperOriginalSourceValuePreparation.denominator false model 1 x.k (values x) (v x) (hv x)
      change (p x).Qv≤513*(p x).reduced.m*2^x.k at h
      rw [hM x] at h
      exact h
    have hPoly : Rated (fun x => 513*x.m*2^x.k) 1 0 1 := by
      change Soft (monomial 1 0 1) (fun x => 513*x.m*2^x.k)
      have hm' : Rated Input.m 1 0 0 := by
        apply bounded 1
        intro x
        simp only [monomial,pow_one,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields]
        omega
      have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
      have hMul := GeneralPaperSourceRateAlgebra.mul Input.m (fun x => 2^x.k) 1 0 0 0 0 1 hm' hAcc
      have hAll := poly_mul_rate (poly_constant 513) hMul
      simpa only [Nat.mul_assoc] using hAll
    apply GeneralPaperSourceSoftBounds.dominated (at_source (rate_mono hPoly (fun x => by
      have h := monomial_mono (by decide : 1≤3) (by decide : 0≤0) (by decide : 1≤4) x
      unfold GeneralPaperFastFrontStorageRates.rate
      omega))) hQBound
  have hIndex : Polylog Input.k := poly_tight _ k_tight
  dsimp only [p,S,T,K,m] at *
  unfold GeneralPaperFullPreparationReference.reserve GeneralPaperFullPreparationReference.bitProfile
    GeneralPaperFullPreparationReference.frameProfile GeneralPaperFullPreparationReference.indexSize
  fun_prop (config := {maxSteps := 4000})

def zeroSource : Input where
  m := 0
  k := 0
  Qv := 0
  B := 3
  b := 1/2
  hb := by norm_num
  hB := by norm_num [RationalHeight]
  reciprocal := false
  weights := FixedArrayTable.ofFn (fun _ : Fin 0 => 0)
  weight_sum := by simp

theorem no_global_native_denominator_match (model : RationalCostModel) (n : Input → ℕ)
    (values : (x : Input) → FixedArrayTable (n x) ℚ) (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j,(values x).read j=(v x).weight j) :
    ¬(∀ x,(data model x.k (values x) (v x) (hv x)).Qv=x.Qv) := by
  intro h
  have hp := (data model zeroSource.k (values zeroSource) (v zeroSource) (hv zeroSource)).Qv_positive
  have hz := h zeroSource
  change (data model zeroSource.k (values zeroSource) (v zeroSource) (hv zeroSource)).Qv=0 at hz
  omega

end Blotto.GeneralPaperFullPreparationProfileGrowth
