import Blotto.GeneralPaperFastSourceControlStorage

/-! Full actual source-control construction and its fast-front parent keep
polylogarithmic new storage and additive original-input height. Their SUM
with the complete prior reservation preserves the sharp paper space rate.
All profiles are closed analysis; no constructor or census is executed. -/
namespace Blotto.GeneralPaperSourceControlStorageRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperNativeSourceRates
open GeneralPaperSourceRateAlgebra GeneralPaperInitializerPreparedPoint GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

theorem control_price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperSourceControlsConstructionStorage.price (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hw := of_tight hW
  dsimp only [GeneralPaperSourceControlsConstructionStorage.price,GeneralPaperSourcePreparationSizes.width,
    GeneralPaperFastRationalMajorant.model]
  fun_prop

theorem control_metadata_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperSourceControlsConstructionStorage.metadataCap (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hw := of_tight hW
  have hp := control_price_small C d W hW
  unfold GeneralPaperSourceControlsConstructionStorage.metadataCap
  fun_prop

def controlCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperSourceControlsConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hw := of_tight hW
  have hp : Rated (fun x => binaryWordWidth (GeneralPaperSourceControlsConstructionStorage.price
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv)) 0 0 0 :=
    word _ (control_price_small C d W hW)
  have hm : Rated (fun x => binaryWordWidth (GeneralPaperSourceControlsConstructionStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv)) 0 0 0 :=
    word _ (control_metadata_small C d W hW)
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperSourceControlsConstructionStorage.profile,
      GeneralPaperPreparationCacheStorage.profile,GeneralPaperParameterTemporaryStorage.profile,
      GeneralPaperSourceControlsConstructionStorage.rawProfile,GeneralPaperSourceControlsConstructionStorage.nestedProfile,
      GeneralPaperSourceControlsConstructionStorage.annotationProfile,
      GeneralPaperPreparationResidentStorage.dyadicProfile,GeneralPaperPreparationResidentStorage.ceilingProfile,
      GeneralPaperEncodedScalarStorage.natBits,GeneralPaperFastRationalMajorant.model,GeneralPaperSourcePreparationSizes.width]
    source_space⟩

theorem control_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((controlCertificate C d W hW).fields,(controlCertificate C d W hW).symbols,
      (controlCertificate C d W hW).accuracy)=(0,0,0) := rfl

theorem price_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastSourceControlStorage.price (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m x.k x.Qv x.B) := by
  have hw := of_tight hW
  have hf := GeneralPaperFastFrontStorageRates.prepared_price_small C d W hW
  have hc := control_price_small C d W hW
  unfold GeneralPaperFastSourceControlStorage.price
  fun_prop

theorem metadata_small (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Small
    (fun x => GeneralPaperFastSourceControlStorage.metadataCap (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m x.k x.Qv x.B) := by
  have hw := of_tight hW
  have hp := price_small C d W hW
  unfold GeneralPaperFastSourceControlStorage.metadataCap
  fun_prop

abbrev rate := GeneralPaperFastFrontStorageRates.rate

theorem profile_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastSourceControlStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m x.k x.Qv x.B) := by
  have hFront := GeneralPaperFastFrontStorageRates.profile_rate C d W hW
  have hControl : Soft rate (fun x => GeneralPaperSourceControlsConstructionStorage.profile
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv) :=
    rate_mono (controlCertificate C d W hW).bound (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  have hMeta : Polylog (fun x => binaryWordWidth (GeneralPaperFastSourceControlStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B)) :=
    poly_word _ (metadata_small C d W hW)
  have hWrate : Soft rate W := rate_mono (poly_tight W hW) (fun x => by change 1≤x.B+1+monomial 3 0 4 x;omega)
  have hWord : Soft rate (fun x => 12*(natBits (GeneralPaperFastSourceControlStorage.metadataCap
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B)+W x)) := by
    apply poly_mul_rate (poly_constant 12)
    apply add_same
    · apply rate_mono (poly_add _ _ (poly_constant 1) hMeta)
      intro x
      change 1≤x.B+1+monomial 3 0 4 x
      omega
    · exact hWrate
  exact add_same (add_same (add_same (poly_mul_rate (poly_constant 2) hFront)
    (poly_mul_rate (poly_constant 2) hControl)) hWord) (poly_mul_rate (poly_constant 288) hWrate)

theorem control_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W m lambda k Qv : ℕ) :
    GeneralPaperSourceControlsConstructionStorage.profile actual W m lambda k Qv≤
      GeneralPaperSourceControlsConstructionStorage.profile upper W m lambda k Qv := by
  dsimp only [GeneralPaperSourceControlsConstructionStorage.profile,GeneralPaperSourceControlsConstructionStorage.rawProfile,
    GeneralPaperSourceControlsConstructionStorage.nestedProfile,GeneralPaperSourceControlsConstructionStorage.metadataCap,
    GeneralPaperSourceControlsConstructionStorage.price,GeneralPaperEncodedScalarStorage.natBits,
    GeneralPaperPreparationResidentStorage.dyadicProfile,GeneralPaperPreparationResidentStorage.ceilingProfile]
  gcongr <;> exact h _

theorem profile_model_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (W m k Qv B : ℕ) :
    GeneralPaperFastSourceControlStorage.profile actual W m k Qv B≤
      GeneralPaperFastSourceControlStorage.profile upper W m k Qv B := by
  have hp := GeneralPaperFastFrontStorageRates.precall_model_mono actual upper h W m k
  have hf := GeneralPaperFastFrontStorageRates.profile_model_mono actual upper h W m k B
  have hc := control_model_mono actual upper h W m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv
  dsimp only [GeneralPaperFastSourceControlStorage.profile,GeneralPaperFastSourceControlStorage.metadataCap,
    GeneralPaperFastSourceControlStorage.price,GeneralPaperSourceControlsConstructionStorage.price,
    GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputClassifier.profile,
    GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperEncodedScalarStorage.natBits]
  gcongr <;> first | exact hp | exact h _

@[fun_prop]
theorem profile_scaling (model : RationalCostModel) (m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => GeneralPaperFastSourceControlStorage.profile model W m k Qv B) := by
  have hf := GeneralPaperFastFrontStorageRates.profile_scaling model m k B
  dsimp only [GeneralPaperFastSourceControlStorage.profile,GeneralPaperFastSourceControlStorage.metadataCap,
    GeneralPaperFastSourceControlStorage.price,GeneralPaperSourceControlsConstructionStorage.profile,
    GeneralPaperSourceControlsConstructionStorage.metadataCap,GeneralPaperSourceControlsConstructionStorage.price,
    GeneralPaperSourceControlsConstructionStorage.rawProfile,GeneralPaperSourceControlsConstructionStorage.nestedProfile,
    GeneralPaperSourceControlsConstructionStorage.annotationProfile,
    GeneralPaperPreparationCacheStorage.profile,GeneralPaperParameterTemporaryStorage.profile,
    GeneralPaperPreparationResidentStorage.dyadicProfile,GeneralPaperPreparationResidentStorage.ceilingProfile,
    GeneralPaperFastInputClassifier.prepareProfile,GeneralPaperFastInputClassifier.profile,GeneralPaperFastInputClassifier.queryProfile,
    GeneralPaperFastInputQuotient.profile,GeneralPaperEncodedScalarStorage.natBits,
    GeneralPaperPrecallCachePrice.profile,GeneralPaperProxyParameterPrice.profile,GeneralPaperScoreScalePrice.profile,
    GeneralPaperScoreScalePrice.width,GeneralPaperQuadraticGridPrice.profile,GeneralPaperQuadraticGridPrice.width,
    GeneralPaperProxyParameterPrice.rawWidth,GeneralPaperComparatorParameterPrice.profile,
    GeneralPaperComparatorParameterPrice.rawWidth,GeneralPaperNatPowerOperands.width]
  fun_prop (maxSteps := 4000)

noncomputable def reservation (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  GeneralPaperFastFrontStorageRates.reservation model C d W m k Qv B+
    GeneralPaperFastSourceControlStorage.profile model W m k Qv B

@[fun_prop]
theorem reservation_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) : GeneralPaperReferenceScaling.Scale
    (fun W => reservation model C d W m k Qv B) := by
  have ho := GeneralPaperFastFrontStorageRates.reservation_scaling model C d m k Qv B
  have hn := profile_scaling model m k Qv B
  unfold reservation
  fun_prop

theorem reservation_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n) (C d W m k Qv B : ℕ) :
    reservation actual C d W m k Qv B≤reservation upper C d W m k Qv B :=
  Nat.add_le_add (GeneralPaperFastFrontStorageRates.reservation_mono actual upper h C d W m k Qv B)
    (profile_model_mono actual upper h W m k Qv B)

theorem reservation_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => reservation (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) :=
  add_same (GeneralPaperFastFrontStorageRates.reservation_rate C d W hW) (profile_rate C d W hW)

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

theorem retained_source {m : ℕ} (model : RationalCostModel) (C d W k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (hB : RationalHeight b B) (hW : GeneralPaperPrecallControlWord.word m k≤W) (exponent target : ℕ)
    (he : exponent≤74+2*k) (ht : GeneralPaperSourcePreparationControls.IsTarget m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv target)
    (oldOwner : ℕ) (hOld : oldOwner≤GeneralPaperFastFrontStorageRates.reservation model C d W m k Qv B) :
    oldOwner+GeneralPaperFastSourceControlStorage.window model W m k Qv b exponent target≤
      reservation model C d W m k Qv B :=
  Nat.add_le_add hOld (GeneralPaperFastSourceControlStorage.bounded model W m k Qv B b hb hB hW exponent target he ht).1

theorem control_price_polylog (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Polylog
    (fun x => GeneralPaperSourceControlsConstructionStorage.price (GeneralPaperFastRationalMajorant.model C d)
      (W x) x.m (alphabet x).lambda x.k x.Qv) := by
  have hm := poly_tight _ measure_tight
  have hw := poly_tight W hW
  dsimp only [GeneralPaperSourceControlsConstructionStorage.price,GeneralPaperSourcePreparationSizes.width,
    GeneralPaperFastRationalMajorant.model]
  fun_prop

theorem actual_control_work {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Polylog
    (fun x => (GeneralPaperSourcePreparationCache.prepare model.rat (W x) x.m (alphabet x).lambda x.k x.Qv).2) := by
  apply GeneralPaperSourceSoftBounds.dominated (control_price_polylog C d W hW)
  intro x
  have h := GeneralPaperSourcePreparationEnvelope.work model.rat model.monotone (W x) x.m (alphabet x).lambda x.k x.Qv
  change _≤GeneralPaperSourceControlsConstructionStorage.price model (W x) x.m (alphabet x).lambda x.k x.Qv at h
  apply h.trans
  dsimp only [GeneralPaperSourceControlsConstructionStorage.price]
  gcongr
  exact GeneralPaperFastRationalMajorant.dominates hg _

theorem native_common_word {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (exponent target : ℕ),exponent≤74+2*x.k →
      GeneralPaperSourcePreparationControls.IsTarget x.m (alphabet x).lambda x.k x.Qv target →
      GeneralPaperFastSourceControlStorage.window model (GeneralPaperCachedBitPairReferenceContract.width C d x)
        x.m x.k x.Qv x.b exponent target≤A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := actual_reservation_rate hg (GeneralPaperCachedBitPairReferenceContract.width C d)
    (GeneralPaperCachedBitPairReferenceContract.width_tight C d)
  refine ⟨A,e,?_⟩
  intro x exponent target he ht
  have hn := (GeneralPaperFastSourceControlStorage.bounded model _ x.m x.k x.Qv x.B x.b x.hb x.hB
    (GeneralPaperCachedBitPairReferenceContract.control_word C d x) exponent target he ht).1
  have hr : GeneralPaperFastSourceControlStorage.profile model (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B≤
      reservation model C d (GeneralPaperCachedBitPairReferenceContract.width C d x) x.m x.k x.Qv x.B := Nat.le_add_left _ _
  have heq : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by
    simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [rate,GeneralPaperFastFrontStorageRates.rate,monomial,pow_zero,Nat.mul_one,GeneralPaperNativeSourceRates.fields,
    heq,Nat.mul_assoc] using hn.trans (hr.trans (h x))

end Blotto.GeneralPaperSourceControlStorageRates
