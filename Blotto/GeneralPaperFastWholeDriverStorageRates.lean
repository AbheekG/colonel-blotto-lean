import Blotto.GeneralPaperFastWholeDriverStorage

/-! Sharp rates for actual retained materialization, prepared input and
whole native driver. Construction keeps its derived local words; full
outer owners sum with all earlier reservations at the caller reference.
The paper input height remains additive. Address calibration is separate. -/
namespace Blotto.GeneralPaperFastWholeDriverStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperNativeSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperInitializerPreparedPoint GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2500000
set_option maxRecDepth 16384

abbrev rate := GeneralPaperFastFrontStorageRates.rate

theorem power_word_tight : Tight (fun x => GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv) := by
  dsimp only [GeneralPaperControlMaterializationStorage.powerWord,GeneralPaperSourcePreparationControls.word]
  fun_prop

theorem grid_word_tight : Tight (fun x => GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv) := by
  dsimp only [GeneralPaperControlMaterializationStorage.gridWord,GeneralPaperMaterializedGridCache.localWord,
    GeneralPaperMaterializedPowerCache.specification,GeneralPaperSourcePreparationCache.specification,
    GeneralPaperProfitOrderPrice.word,GeneralPaperProfitOrderPrice.capacity]
  fun_prop

theorem materialization_price_small (C d : ℕ) : Small
    (fun x => GeneralPaperControlMaterializationStorage.price (GeneralPaperFastRationalMajorant.model C d) x.m (alphabet x).lambda x.k x.Qv) := by
  dsimp only [GeneralPaperControlMaterializationStorage.price,GeneralPaperProfitGridProfile.bound,
    GeneralPaperProfitGridProfile.sizeFactor,GeneralPaperProfitGridProfile.logFactor,GeneralPaperProfitGridPrice.count,
    GeneralPaperFastRationalMajorant.model]
  fun_prop

theorem materialization_metadata_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperControlMaterializationStorage.metadataCap (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hw := of_tight hW
  have hu := of_tight power_word_tight
  have hv := of_tight grid_word_tight
  have hp := materialization_price_small C d
  unfold GeneralPaperControlMaterializationStorage.metadataCap
  fun_prop

def materializationCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperControlMaterializationStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hu : Rated (fun x => GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv) 0 0 0 := poly (poly_tight _ power_word_tight)
  have hv : Rated (fun x => GeneralPaperControlMaterializationStorage.gridWord x.m (alphabet x).lambda x.k x.Qv) 0 0 0 := poly (poly_tight _ grid_word_tight)
  have hus := of_tight power_word_tight
  have hvs := of_tight grid_word_tight
  have hm : Rated (fun x => binaryWordWidth (GeneralPaperControlMaterializationStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv)) 0 0 0 :=
    word _ (materialization_metadata_small C d W hW)
  have hn : Rated (fun x => (GeneralPaperProfitGridPrepare.prepare
      (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).qProf
      (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width
      (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent).size) 0 0 1 := actual_grid
  have hDepth : Rated (fun x => (GeneralPaperPowerCeiling.ceiling
      (((GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent+1)*
        (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width+3)).doublings) 0 0 0 :=
    poly (poly_tight _ (GeneralPaperConstructedWordGrowth.ceiling_depth_tight _ (by fun_prop)))
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperControlMaterializationStorage.profile,
      GeneralPaperMaterializedCacheStorage.gridProfile,GeneralPaperMaterializedCacheStorage.powerProfile,
      GeneralPaperPreparationCacheStorage.profile,GeneralPaperEncodedPreparedPowers.profile,
      GeneralPaperEncodedSharedParameters.preparedProfitProfile,GeneralPaperEncodedProfitGrid.profile,
      GeneralPaperEncodedProfitGrid.word,GeneralPaperPowerConstructionStorage.profile,
      GeneralPaperProfitGridConstructionStorage.profile,GeneralPaperProfitOrderConstructionStorage.profile,
      GeneralPaperGridPointConstructionStorage.profile,GeneralPaperGridPointConstructionStorage.frames,
      GeneralPaperNaturalOrderConstructionStorage.profile,GeneralPaperNaturalOrderConstructionStorage.sortProfile,
      GeneralPaperNaturalOrderConstructionStorage.depth,GeneralPaperSortConstructionStorage.coefficient,
      GeneralPaperSortConstructionStorage.controlWord,GeneralPaperSortConstructionStorage.controlCap,
      GeneralPaperRaySearchControls.depth,GeneralPaperNaturalOrderPrice.profile,GeneralPaperPricedSort.profile,
      GeneralPaperProfitPointPrice.profile,GeneralPaperProfitPointPrice.bandProfile,GeneralPaperProfitPointPrice.width,
      GeneralPaperProfitGridPrice.profile,GeneralPaperProfitGridPrice.depthProfile,
      GeneralPaperProfitOrderConstruction.profile,GeneralPaperProfitGridPrice.count,
      GeneralPaperProfitScalePrice.width,GeneralPaperProfitOrderPrice.word,GeneralPaperProfitOrderPrice.capacity,
      GeneralPaperGridArrayConstructionStorage.frames,GeneralPaperCeilingConstructionStorage.word,
      GeneralPaperEncodedScalarStorage.natBits,GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem materialization_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((materializationCertificate C d W hW).fields,(materializationCertificate C d W hW).symbols,
      (materializationCertificate C d W hW).accuracy)=(0,0,1) := rfl

theorem materialization_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperControlMaterializationStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) :=
  rate_mono (materializationCertificate C d W hW).bound (fun x => by
    have h := monomial_mono (by decide : 0≤3) (by decide : 0≤0) (by decide : 1≤4) x
    change monomial 0 0 1 x≤x.B+1+monomial 3 0 4 x
    omega)

theorem prepared_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastPreparedInputStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B) := by
  have hf := GeneralPaperSourceControlStorageRates.price_small C d W hW
  have hg := materialization_price_small C d
  unfold GeneralPaperFastPreparedInputStorage.price
  fun_prop

theorem prepared_metadata_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastPreparedInputStorage.metadataCap (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B) := by
  have hp := prepared_price_small C d W hW
  have hw := of_tight hW
  unfold GeneralPaperFastPreparedInputStorage.metadataCap
  fun_prop

theorem prepared_profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastPreparedInputStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B) := by
  have hf := GeneralPaperSourceControlStorageRates.profile_rate C d W hW
  have hg := materialization_rate C d W hW
  have hw : Soft rate W := poly_at_rate (poly_tight W hW) (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  have hm : Soft rate (fun x => natBits (GeneralPaperFastPreparedInputStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B)) :=
    poly_at_rate (poly_add _ _ (poly_constant 1) (poly_word _ (prepared_metadata_small C d W hW)))
      (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  exact add_same (add_same (add_same (poly_mul_rate (poly_constant 2) hf) (poly_mul_rate (poly_constant 2) hg))
    (poly_mul_rate (poly_constant 12) (add_same hm hw))) (poly_mul_rate (poly_constant 416) hw)

theorem price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastWholeDriverStorage.price (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) := by
  have hp := prepared_price_small C d W hW
  have hc := GeneralPaperCachedBitPairStorageRates.price_small C d W hW
  have hw := of_tight hW
  unfold GeneralPaperFastWholeDriverStorage.price
  fun_prop

theorem metadata_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastWholeDriverStorage.metadataCap (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) := by
  have hp := price_small C d W hW
  have hw := of_tight hW
  unfold GeneralPaperFastWholeDriverStorage.metadataCap
  fun_prop

theorem profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastWholeDriverStorage.profile (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) := by
  have hp := prepared_profile_rate C d W hW
  have hc : Soft rate (fun x => GeneralPaperCachedBitPairStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      C d (W x) x.m x.k x.Qv x.B) :=
    GeneralPaperSourceSoftBounds.dominated (GeneralPaperCachedBitPairStorageRates.majorant_rate C d W hW)
      (fun x => Nat.le_add_left _ _)
  have hw : Soft rate W := poly_at_rate (poly_tight W hW) (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  have hm : Soft rate (fun x => natBits (GeneralPaperFastWholeDriverStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B)) :=
    poly_at_rate (poly_add _ _ (poly_constant 1) (poly_word _ (metadata_small C d W hW)))
      (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  exact add_same (add_same (add_same (poly_mul_rate (poly_constant 2) hp) (poly_mul_rate (poly_constant 3) hc))
    (poly_mul_rate (poly_constant 12) (add_same hm hw))) (poly_mul_rate (poly_constant 288) hw)

theorem materialization_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W m lambda k Qv : ℕ) :
    GeneralPaperControlMaterializationStorage.profile actual W m lambda k Qv≤
      GeneralPaperControlMaterializationStorage.profile upper W m lambda k Qv := by
  dsimp only [GeneralPaperControlMaterializationStorage.profile,GeneralPaperControlMaterializationStorage.metadataCap,
    GeneralPaperControlMaterializationStorage.price,GeneralPaperPowerConstructionStorage.profile,
    GeneralPaperProfitGridConstructionStorage.profile,GeneralPaperProfitOrderConstructionStorage.profile,
    GeneralPaperGridPointConstructionStorage.profile,GeneralPaperNaturalOrderConstructionStorage.profile,
    GeneralPaperNaturalOrderConstructionStorage.sortProfile,GeneralPaperSortConstructionStorage.coefficient,
    GeneralPaperProfitPointPrice.profile,GeneralPaperProfitPointPrice.bandProfile,GeneralPaperProfitGridPrice.profile,
    GeneralPaperProfitGridPrice.depthProfile,GeneralPaperProfitOrderConstruction.profile,GeneralPaperNaturalOrderPrice.profile,
    GeneralPaperPricedSort.profile,GeneralPaperEncodedScalarStorage.natBits]
  gcongr <;> exact h _

theorem prepared_price_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W m k Qv B : ℕ) :
    GeneralPaperFastPreparedInputStorage.price actual W m k Qv B≤GeneralPaperFastPreparedInputStorage.price upper W m k Qv B := by
  have hp := GeneralPaperFastFrontStorageRates.precall_model_mono actual upper h W m k
  dsimp only [GeneralPaperFastPreparedInputStorage.price,GeneralPaperFastSourceControlStorage.price,
    GeneralPaperSourceControlsConstructionStorage.price,GeneralPaperControlMaterializationStorage.price,
    GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputClassifier.profile,
    GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputQuotient.profile]
  gcongr <;> first | exact hp | exact h _

theorem prepared_profile_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W m k Qv B : ℕ) :
    GeneralPaperFastPreparedInputStorage.profile actual W m k Qv B≤GeneralPaperFastPreparedInputStorage.profile upper W m k Qv B := by
  have hf := GeneralPaperSourceControlStorageRates.profile_model_mono actual upper h W m k Qv B
  have hg := materialization_model_mono actual upper h W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv
  have hp := prepared_price_mono actual upper h W m k Qv B
  dsimp only [GeneralPaperFastPreparedInputStorage.profile,GeneralPaperFastPreparedInputStorage.metadataCap,natBits]
  gcongr

theorem profile_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (C d W m k Qv B : ℕ) :
    GeneralPaperFastWholeDriverStorage.profile actual C d W m k Qv B≤GeneralPaperFastWholeDriverStorage.profile upper C d W m k Qv B := by
  have hp := prepared_profile_mono actual upper h W m k Qv B
  have hc := GeneralPaperCachedBitPairStorageRates.model_mono actual upper h C d W m k Qv B
  have hpp := prepared_price_mono actual upper h W m k Qv B
  have hcp := GeneralPaperCachedBitPairStorageRates.price_mono actual upper h C d W m k Qv
  dsimp only [GeneralPaperFastWholeDriverStorage.profile,GeneralPaperFastWholeDriverStorage.metadataCap,GeneralPaperFastWholeDriverStorage.price,natBits]
  gcongr

@[fun_prop]
theorem prepared_price_scaling (model : RationalCostModel) (m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperFastPreparedInputStorage.price model W m k Qv B) := by
  dsimp only [GeneralPaperFastPreparedInputStorage.price,GeneralPaperFastSourceControlStorage.price,
    GeneralPaperSourceControlsConstructionStorage.price,GeneralPaperFastInputClassifier.prepareProfile,
    GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputQuotient.profile,
    GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,
    GeneralPaperQuadraticGridPrice.profile,GeneralPaperComparatorParameterPrice.profile]
  fun_prop (maxSteps := 4000)

@[fun_prop]
theorem materialization_scaling (model : RationalCostModel) (m lambda k Qv : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperControlMaterializationStorage.profile model W m lambda k Qv) := by
  dsimp only [GeneralPaperControlMaterializationStorage.profile,GeneralPaperControlMaterializationStorage.metadataCap,natBits]
  fun_prop

@[fun_prop]
theorem prepared_profile_scaling (model : RationalCostModel) (m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperFastPreparedInputStorage.profile model W m k Qv B) := by
  have hf := GeneralPaperSourceControlStorageRates.profile_scaling model m k Qv B
  have hg := materialization_scaling model m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv
  have hp := prepared_price_scaling model m k Qv B
  dsimp only [GeneralPaperFastPreparedInputStorage.profile,GeneralPaperFastPreparedInputStorage.metadataCap,natBits]
  fun_prop

@[fun_prop]
theorem profile_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperFastWholeDriverStorage.profile model C d W m k Qv B) := by
  have hp := prepared_profile_scaling model m k Qv B
  have hc := GeneralPaperCachedBitPairStorageRates.scaling model C d m k Qv B
  have hpp := prepared_price_scaling model m k Qv B
  have hcp := GeneralPaperCachedBitPairStorageRates.price_scaling model C d m k Qv
  dsimp only [GeneralPaperFastWholeDriverStorage.profile,GeneralPaperFastWholeDriverStorage.metadataCap,GeneralPaperFastWholeDriverStorage.price,natBits]
  fun_prop

noncomputable def reservation (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperSourceControlStorageRates.reservation model C d W m k Qv B+
    GeneralPaperFastWholeDriverStorage.profile model C d W m k Qv B

@[fun_prop]
theorem reservation_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => reservation model C d W m k Qv B) := by
  have ho := GeneralPaperSourceControlStorageRates.reservation_scaling model C d m k Qv B
  have hn := profile_scaling model C d m k Qv B
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B≤reservation upper C d W m k Qv B :=
  Nat.add_le_add (GeneralPaperSourceControlStorageRates.reservation_mono actual upper h C d W m k Qv B)
    (profile_model_mono actual upper h C d W m k Qv B)

theorem reservation_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) :=
  add_same (GeneralPaperSourceControlStorageRates.reservation_rate C d W hW) (profile_rate C d W hW)

theorem actual_reservation_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Soft rate (fun x => reservation model C d (W x) x.m x.k x.Qv x.B) :=
  GeneralPaperSourceSoftBounds.dominated (reservation_rate C d W hW)
    (fun x => reservation_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv x.B)

theorem at_one_small (C d : ℕ) : Small
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d 1 x.m x.k x.Qv x.B) := by
  apply GeneralPaperSourceRowsStorageRates.soft_small (reservation_rate C d (fun _ => 1) (tight_constant 1))
  unfold rate GeneralPaperFastFrontStorageRates.rate monomial GeneralPaperNativeSourceRates.fields
    GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

def materializationWorkCertificate (C d : ℕ) : Certificate
    (fun x => GeneralPaperControlMaterializationStorage.price (GeneralPaperFastRationalMajorant.model C d)
      x.m (alphabet x).lambda x.k x.Qv) := by
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperControlMaterializationStorage.price,GeneralPaperProfitGridProfile.bound,
      GeneralPaperProfitGridProfile.sizeFactor,GeneralPaperProfitGridProfile.logFactor,GeneralPaperProfitGridPrice.count,
      GeneralPaperFastRationalMajorant.model]
    source_space⟩

theorem materialization_work_degrees (C d : ℕ) :
    ((materializationWorkCertificate C d).fields,(materializationWorkCertificate C d).symbols,
      (materializationWorkCertificate C d).accuracy)=(0,0,1) := rfl

theorem bit_materialization_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (U : Input → ℕ) : Rated (fun x => (GeneralPaperMaterializationFromControls.bit model
      (GeneralPaperControlMaterializationStorage.powerWord x.m (alphabet x).lambda x.k x.Qv) x.k
      (GeneralPaperFastPreparedInputStorage.controls model (U x) x.m x.k x.Qv x.b)).2) 0 0 1 := by
  apply GeneralPaperSourceSoftBounds.dominated (materializationWorkCertificate C d).bound
  intro x
  have h := GeneralPaperMaterializationFromControls.bit_work model x.m (alphabet x).lambda x.k x.Qv
    (GeneralPaperFastPreparedInputStorage.controls model (U x) x.m x.k x.Qv x.b)
    (GeneralPaperFastPreparedInputStorage.controls_data model (U x) x.m x.k x.Qv x.b x.hb)
  apply h.trans
  dsimp only [GeneralPaperControlMaterializationStorage.price]
  gcongr
  exact GeneralPaperFastRationalMajorant.dominates hg _

def arithmeticMaterializationCertificate : Certificate (fun x =>
    524288*(GeneralPaperSourcePreparationSizes.measure x.m (alphabet x).lambda x.k x.Qv+1)^2+
      GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).width
        (GeneralPaperProfitParameters.parameters x.m (alphabet x).lambda x.k x.Qv).exponent) := by
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperProfitGridProfile.bound,GeneralPaperProfitGridProfile.sizeFactor,
      GeneralPaperProfitGridProfile.logFactor,GeneralPaperProfitGridPrice.count]
    source_space⟩

theorem arithmetic_materialization_degrees :
    (arithmeticMaterializationCertificate.fields,arithmeticMaterializationCertificate.symbols,
      arithmeticMaterializationCertificate.accuracy)=(0,0,1) := rfl

theorem arithmetic_materialization_work (model : RationalCostModel) (U : Input → ℕ) : Rated
    (fun x => (GeneralPaperMaterializationFromControls.arithmetic x.k
      (GeneralPaperFastPreparedInputStorage.controls model (U x) x.m x.k x.Qv x.b)).2) 0 0 1 :=
  GeneralPaperSourceSoftBounds.dominated arithmeticMaterializationCertificate.bound (fun x =>
    GeneralPaperMaterializationFromControls.arithmetic_work x.m (alphabet x).lambda x.k x.Qv
      (GeneralPaperFastPreparedInputStorage.controls model (U x) x.m x.k x.Qv x.b)
      (GeneralPaperFastPreparedInputStorage.controls_data model (U x) x.m x.k x.Qv x.b x.hb))

theorem native_common_word {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j)
      (exponent target : ℕ),exponent≤74+2*x.k →
      GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x).lambda x.k x.Qv target →
      ∀ (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x).lambda x.k x.Qv)
        (cursor : ℕ) (hc : cursor≤x.m) (outer : ℕ) (ho : outer≤x.m) (inner : ℕ)
        (hi : inner≤(GeneralPaperProxyParameters.prepare x.m x.k).K),
      GeneralPaperFastWholeDriverStorage.window model (GeneralPaperCachedBitPairReferenceContract.width C d x)
        x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb exponent target material cursor hc outer ho inner hi≤
          A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := actual_reservation_rate hg (GeneralPaperCachedBitPairReferenceContract.width C d)
    (GeneralPaperCachedBitPairReferenceContract.width_tight C d)
  refine ⟨A,e,?_⟩
  intro x hm hQv hp exponent target he ht material cursor hc outer ho inner hi
  have hn := (GeneralPaperFastWholeDriverStorage.at_cached_reference hg x hm hQv hp exponent target he ht material cursor hc outer ho inner hi).1
  have hr : GeneralPaperFastWholeDriverStorage.profile model C d (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B≤
      reservation model C d (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B := Nat.le_add_left _ _
  have heq : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [rate,GeneralPaperFastFrontStorageRates.rate,monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,
    heq,Nat.mul_assoc] using hn.trans (hr.trans (h x))

theorem retained_at_cached_reference {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j)
    (exponent target : ℕ) (he : exponent≤74+2*x.k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x).lambda x.k x.Qv target)
    (material : GeneralPaperFastPreparedInputStorage.Cursor x.m (alphabet x).lambda x.k x.Qv)
    (cursor : ℕ) (hc : cursor≤x.m) (outer : ℕ) (ho : outer≤x.m) (inner : ℕ)
    (hi : inner≤(GeneralPaperProxyParameters.prepare x.m x.k).K) (oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperSourceControlStorageRates.reservation model C d
      (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B) :
    oldOwner+GeneralPaperFastWholeDriverStorage.window model (GeneralPaperCachedBitPairReferenceContract.width C d x)
      x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb exponent target material cursor hc outer ho inner hi≤
        reservation model C d (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B :=
  Nat.add_le_add hOld (GeneralPaperFastWholeDriverStorage.at_cached_reference hg x hm hQv hp
    exponent target he ht material cursor hc outer ho inner hi).1

end Blotto.GeneralPaperFastWholeDriverStorageRates
