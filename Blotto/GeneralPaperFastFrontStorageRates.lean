import Blotto.GeneralPaperFastPreparedFrontStorage

/-! Sharp simultaneous fast-front storage with additive original ratio
height. Complete cache-constructor, quotient/query/classifier/prepared
profiles are composed as a sum; native work fields use their encoded size.
Positive reference scaling and actual-model domination support the next
outer control/materialization/driver reservation join. -/
namespace Blotto.GeneralPaperFastFrontStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 600000
set_option maxRecDepth 16384

@[fun_prop]
theorem score_labels_small : Small (fun x => (GeneralPaperScoreScaleParameters.prepare x.m x.k).K) := by
  have he : (fun x : Input => (GeneralPaperScoreScaleParameters.prepare x.m x.k).K)=(fun x : Input => 2^(7+x.k)) :=
    funext (fun x => GeneralPaperScoreScaleParameters.label_power x.m x.k)
  rw [he]
  fun_prop

@[fun_prop]
theorem score_labels_word : Rated (fun x => binaryWordWidth (GeneralPaperScoreScaleParameters.prepare x.m x.k).K) 0 0 0 :=
  word _ score_labels_small

@[fun_prop]
theorem root_exponent_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).d+2) :=
  GeneralPaperSourceWordGrowth.dominated lambda_small (fun x => GeneralPaperPrecallWordEnvelope.root_exponent x.m x.k)

@[fun_prop]
theorem root_dimension_small : Small (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).d) :=
  GeneralPaperSourceWordGrowth.dominated lambda_small (fun x => by
    have h := GeneralPaperPrecallWordEnvelope.root_exponent x.m x.k
    change (GeneralPaperProxyParameters.prepare x.m x.k).d≤(GeneralPaperProxyParameters.alphabet x.m x.k).lambda
    omega)

@[fun_prop]
theorem comparator_labels_small : Small (fun x =>
    (GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).Kc) := by
  have he : (fun x : Input => (GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).Kc)=
      (fun x : Input => 2^(17+x.k)) := by
    funext x
    rw [(GeneralPaperComparatorParameters.data x.m x.k _).1,GeneralPaperComparatorParameters.count_power]
  rw [he]
  fun_prop

@[fun_prop]
theorem comparator_exponent_small : Small (fun x =>
    (GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).J) :=
  GeneralPaperSourceWordGrowth.dominated lambda_small (fun x => GeneralPaperPrecallWordEnvelope.alphabet_exponent x.m x.k)

theorem comparator_exponent : Rated (fun x =>
    (GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).J) 0 1 0 :=
  GeneralPaperSourceSoftBounds.dominated GeneralPaperSourceRateAlgebra.lambda
    (fun x => GeneralPaperPrecallWordEnvelope.alphabet_exponent x.m x.k)

theorem root_order_word : Rated (fun x => binaryWordWidth (GeneralPaperProxyParameters.prepare x.m x.k).H) 0 1 0 :=
  GeneralPaperSourceSoftBounds.dominated GeneralPaperSourceStorageRates.denominator_word
    (fun x => binaryWordWidth_mono (GeneralPaperPrecallWordEnvelope.root_order x.m x.k))

theorem comparator_order_word : Rated (fun x => binaryWordWidth
    (GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).D) 0 1 0 := by
  change Rated (fun x => binaryWordWidth (alphabet x).D) 0 1 0
  exact GeneralPaperSourceStorageRates.denominator_word

theorem comparator_power_word : Rated (fun x => binaryWordWidth ((x.m+2)^(
    GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).J)) 0 1 0 := by
  have hJ := comparator_exponent
  apply GeneralPaperSourceSoftBounds.dominated (g:=fun x => 1+(
    GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).J*binaryWordWidth (x.m+2))
  · change Rated _ 0 1 0
    source_space
  · intro x
    exact GeneralPaperNatPowerOperands.power_width _ _

@[fun_prop]
theorem comparator_power_word_small : Small (fun x => binaryWordWidth ((x.m+2)^(
    GeneralPaperComparatorParameters.prepare x.m x.k (GeneralPaperProxyParameters.prepare x.m x.k).qbar).J)) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small comparator_power_word
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

def precallCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperPrecallCachePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat (W x) x.m x.k) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hJ := comparator_exponent
  have hH := root_order_word
  have hD := comparator_order_word
  have hPow := comparator_power_word
  have hRoot : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).d+2) 0 1 0 :=
    GeneralPaperSourceSoftBounds.dominated GeneralPaperSourceRateAlgebra.lambda
      (fun x => GeneralPaperPrecallWordEnvelope.root_exponent x.m x.k)
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,GeneralPaperScoreScalePrice.width,GeneralPaperQuadraticGridPrice.profile,GeneralPaperQuadraticGridPrice.width,GeneralPaperProxyParameterPrice.rawWidth,GeneralPaperComparatorParameterPrice.profile,GeneralPaperComparatorParameterPrice.rawWidth,GeneralPaperNatPowerOperands.width,GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem precall_coarse (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated
    (fun x => GeneralPaperPrecallCachePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat (W x) x.m x.k) 1 2 2 :=
  weaken (precallCertificate C d W hW).bound (by change 1≤1;omega) (by change 2≤2;omega) (by change 1≤2;omega)

theorem precall_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperPrecallCachePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat (W x) x.m x.k) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (precall_coarse C d W hW)
  unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

@[fun_prop]
theorem query_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastInputClassifier.queryProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hw := of_tight hW
  dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
  fun_prop

@[fun_prop]
theorem classifier_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastInputClassifier.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hw := of_tight hW
  dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
  fun_prop

@[fun_prop]
theorem prepared_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastInputClassifier.prepareProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hw := of_tight hW
  have hp := precall_small C d W hW
  dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
  fun_prop

def zeroCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperFastPreparedFrontStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hPrec := precall_coarse C d W hW
  have hP := precall_small C d W hW
  have hQuery : Small (fun x => GeneralPaperFastInputClassifier.queryProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
    dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
    fun_prop
  have hClassifier : Small (fun x => GeneralPaperFastInputClassifier.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
    dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
    fun_prop
  have hPrepared : Small (fun x => GeneralPaperFastInputClassifier.prepareProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
    dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperSelectionPoints.width,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
    fun_prop
  have hQueryWord : Rated (fun x => binaryWordWidth (GeneralPaperFastInputClassifier.queryProfile
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0)) 0 0 0 := word _ hQuery
  have hClassifierWord : Rated (fun x => binaryWordWidth (GeneralPaperFastInputClassifier.profile
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0)) 0 0 0 := word _ hClassifier
  have hPreparedWord : Rated (fun x => binaryWordWidth (GeneralPaperFastInputClassifier.prepareProfile
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0)) 0 0 0 := word _ hPrepared
  have hMeasure := GeneralPaperSourceStorageRates.precall_measure
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperFastPreparedFrontStorage.profile,GeneralPaperPrecallConstructionStorage.profile,GeneralPaperPrecallConstructionStorage.stackProfile,GeneralPaperFastClassifierStorage.profile,GeneralPaperFastQueryStorage.profile,GeneralPaperFastQueryStorage.rootPrice,GeneralPaperFastQueryStorage.recordPrice,GeneralPaperFastInputQuotientStorageRates.storageProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperSelectionConstructionStorage.profile,GeneralPaperSelectionPoints.width,GeneralPaperClassifierResultStorage.frontProfile,GeneralPaperClassifierResultStorage.profile,GeneralPaperPrecallCacheStorage.payload,GeneralPaperCFOperandPrice.width,GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem zero_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((zeroCertificate C d W hW).fields,(zeroCertificate C d W hW).symbols,(zeroCertificate C d W hW).accuracy)=(1,2,2) := rfl

def rate (x : Input) : ℕ := x.B+1+monomial 3 0 4 x

theorem input_rate : Soft rate Input.B := rate_mono (identity Input.B) (fun x => by unfold rate;omega)

theorem source_lift {f : Input → ℕ} (hf : Soft GeneralPaperFastInputQuotientStorageRates.rate f) : Soft rate f :=
  rate_mono hf (fun x => by
    have h := monomial_mono (by decide : 1≤3) (by decide : 0≤0) (by decide : 1≤4) x
    unfold rate GeneralPaperFastInputQuotientStorageRates.rate
    omega)

theorem split_bound (model : RationalCostModel) (W m k B : ℕ) :
    GeneralPaperFastPreparedFrontStorage.profile model W m k B≤GeneralPaperFastPreparedFrontStorage.profile model W m k 0+
      20000*B+26*model.rat (GeneralPaperFastInputQuotient.width m k B)+
      512*model.rat (GeneralPaperSelectionPoints.width (GeneralPaperProxyParameters.prepare m k).Qg B)+
      100*(natBits (GeneralPaperFastInputQuotient.profile model W m k B)+
        natBits (GeneralPaperFastInputClassifier.queryProfile model W m k B)+
        natBits (GeneralPaperFastInputClassifier.profile model W m k B)+
        natBits (GeneralPaperFastInputClassifier.prepareProfile model W m k B)) := by
  dsimp only [GeneralPaperFastPreparedFrontStorage.profile,GeneralPaperPrecallConstructionStorage.profile,GeneralPaperPrecallConstructionStorage.stackProfile,GeneralPaperFastClassifierStorage.profile,GeneralPaperFastQueryStorage.profile,GeneralPaperFastQueryStorage.rootPrice,GeneralPaperFastQueryStorage.recordPrice,GeneralPaperFastInputQuotientStorageRates.storageProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperSelectionConstructionStorage.profile,GeneralPaperSelectionPoints.width,GeneralPaperClassifierResultStorage.frontProfile,GeneralPaperClassifierResultStorage.profile,GeneralPaperPrecallCacheStorage.payload]
  omega

theorem work_words_polylog (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Polylog (fun x =>
    natBits (GeneralPaperFastInputQuotient.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.queryProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.prepareProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)) := by
  have hq := GeneralPaperFastInputQuotientStorageRates.profile_small C d W hW
  have hr := query_price_small C d W hW
  have hc := classifier_price_small C d W hW
  have hp := prepared_price_small C d W hW
  unfold natBits
  fun_prop

theorem profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastPreparedFrontStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B) := by
  have hz : Soft rate (fun x => GeneralPaperFastPreparedFrontStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) :=
    rate_mono (GeneralPaperSourceRowsCallerStorageRates.sharpen_source (zeroCertificate C d W hW).bound) (fun x => by unfold rate;omega)
  have hB := poly_mul_rate (poly_constant 20000) input_rate
  have hQ := poly_mul_rate (poly_constant 26) (source_lift (charge_preserves (C+1) d
    GeneralPaperFastInputQuotientStorageRates.width_rate GeneralPaperFastInputQuotientStorageRates.width_small))
  have hS := poly_mul_rate (poly_constant 512) (source_lift (charge_preserves (C+1) d
    GeneralPaperFastInputQuotientStorageRates.selection_rate GeneralPaperFastInputQuotientStorageRates.selection_small))
  have hWords : Soft rate (fun x => 100*(natBits (GeneralPaperFastInputQuotient.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.queryProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B)+
    natBits (GeneralPaperFastInputClassifier.prepareProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.B))) :=
    rate_mono (poly_mul_rate (poly_constant 100) (work_words_polylog C d W hW)) (fun x => by unfold rate;omega)
  exact GeneralPaperSourceSoftBounds.dominated (add_same (add_same (add_same (add_same hz hB) hQ) hS) hWords)
    (fun x => split_bound _ _ _ _ _)

theorem precall_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k : ℕ) :
    GeneralPaperPrecallCachePrice.profile actual.rat W m k≤GeneralPaperPrecallCachePrice.profile upper.rat W m k := by
  dsimp only [GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,GeneralPaperScoreScalePrice.width,GeneralPaperQuadraticGridPrice.profile,GeneralPaperQuadraticGridPrice.width,GeneralPaperProxyParameterPrice.rawWidth,GeneralPaperComparatorParameterPrice.profile,GeneralPaperComparatorParameterPrice.rawWidth,GeneralPaperNatPowerOperands.width]
  gcongr <;> exact h _

theorem profile_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (W m k B : ℕ) :
    GeneralPaperFastPreparedFrontStorage.profile actual W m k B≤GeneralPaperFastPreparedFrontStorage.profile upper W m k B := by
  have hPrec := precall_model_mono actual upper h W m k
  dsimp only [GeneralPaperFastPreparedFrontStorage.profile,GeneralPaperPrecallConstructionStorage.profile,GeneralPaperPrecallConstructionStorage.stackProfile,GeneralPaperFastClassifierStorage.profile,GeneralPaperFastQueryStorage.profile,GeneralPaperFastQueryStorage.rootPrice,GeneralPaperFastQueryStorage.recordPrice,GeneralPaperFastInputQuotientStorageRates.storageProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperSelectionConstructionStorage.profile,GeneralPaperSelectionPoints.width,GeneralPaperClassifierResultStorage.frontProfile,GeneralPaperClassifierResultStorage.profile,GeneralPaperPrecallCacheStorage.payload,GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification]
  gcongr <;> exact h _

@[fun_prop]
theorem profile_scaling (model : RationalCostModel) (m k B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperFastPreparedFrontStorage.profile model W m k B) := by
  dsimp only [GeneralPaperFastPreparedFrontStorage.profile,GeneralPaperPrecallConstructionStorage.profile,GeneralPaperPrecallConstructionStorage.stackProfile,GeneralPaperFastClassifierStorage.profile,GeneralPaperFastQueryStorage.profile,GeneralPaperFastQueryStorage.rootPrice,GeneralPaperFastQueryStorage.recordPrice,GeneralPaperFastInputQuotientStorageRates.storageProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,GeneralPaperEncodedScalarStorage.natBits,GeneralPaperBoundedQuotient.heightBudget,GeneralPaperSelectionConstructionStorage.profile,GeneralPaperSelectionPoints.width,GeneralPaperClassifierResultStorage.frontProfile,GeneralPaperClassifierResultStorage.profile,GeneralPaperPrecallCacheStorage.payload,GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,GeneralPaperScoreScalePrice.width,GeneralPaperQuadraticGridPrice.profile,GeneralPaperQuadraticGridPrice.width,GeneralPaperProxyParameterPrice.rawWidth,GeneralPaperComparatorParameterPrice.profile,GeneralPaperComparatorParameterPrice.rawWidth,GeneralPaperNatPowerOperands.width]
  fun_prop (maxSteps := 4000)

noncomputable def reservation (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperCachedBitPairStorageRates.reservation model C d W m k Qv B+
    GeneralPaperFastPreparedFrontStorage.profile model W m k B

@[fun_prop]
theorem reservation_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => reservation model C d W m k Qv B) := by
  have hOld := GeneralPaperCachedBitPairStorageRates.reservation_scaling model C d m k Qv B
  have hNew := profile_scaling model m k B
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B≤reservation upper C d W m k Qv B :=
  Nat.add_le_add (GeneralPaperCachedBitPairStorageRates.reservation_mono actual upper h C d W m k Qv B)
    (profile_model_mono actual upper h W m k B)

theorem reservation_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) :=
  add_same (GeneralPaperCachedBitPairStorageRates.majorant_rate C d W hW) (profile_rate C d W hW)

theorem actual_reservation_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => reservation model C d (W x) x.m x.k x.Qv x.B) :=
  GeneralPaperSourceSoftBounds.dominated (reservation_rate C d W hW)
    (fun x => reservation_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv x.B)

theorem at_one_small (C d : ℕ) : Small
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d 1 x.m x.k x.Qv x.B) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservation_rate C d (fun _ => 1) (tight_constant 1))
  unfold rate monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem retained_front {m : ℕ} (model : RationalCostModel) (C d W k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperCachedBitPairStorageRates.reservation model C d W m k Qv B) :
    oldOwner+GeneralPaperFastPreparedFrontStorage.window model W m k b≤reservation model C d W m k Qv B :=
  Nat.add_le_add hOld (GeneralPaperFastPreparedFrontStorage.bounded model W m k B b hb hB hW).1

theorem native_common_word {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ x : Input,
      GeneralPaperFastPreparedFrontStorage.window model (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.b≤
        A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := actual_reservation_rate hg (GeneralPaperCachedBitPairReferenceContract.width C d)
    (GeneralPaperCachedBitPairReferenceContract.width_tight C d)
  refine ⟨A,e,?_⟩
  intro x
  have hn := (GeneralPaperFastPreparedFrontStorage.bounded model _ x.m x.k x.B x.b x.hb x.hB
    (GeneralPaperCachedBitPairReferenceContract.control_word C d x)).1
  have hr : GeneralPaperFastPreparedFrontStorage.profile model (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.B≤
      reservation model C d (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B := Nat.le_add_left _ _
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [rate,monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using hn.trans (hr.trans (h x))

end Blotto.GeneralPaperFastFrontStorageRates
