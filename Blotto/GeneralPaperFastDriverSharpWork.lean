import Blotto.GeneralPaperCompilerSharpWork

/-! Complete actual fast bit-driver time, with original input length
additive and compiler/source tradeoffs retained until reduced-field
substitution. All native work uses the already calibrated global word. -/
namespace Blotto.GeneralPaperFastDriverSharpWork
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra GeneralPaperNativeSourceRates
open GeneralPaperSourceCallerSharpWork GeneralPaperUnitCallerSharpWork
open GeneralPaperConstructedWordGrowth
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

def rate (x : Input) : ℕ := x.B+1+GeneralPaperCompilerSharpWork.bitRate x

def precallSubstitution : Certificate (fun x => monomial 1 2 1 x) := by
  have hL := GeneralPaperSourceSharpOperandRates.alphabet_length
  have hAcc : Rated (fun x => 2^x.k) 0 0 1 := by simpa only [Nat.zero_add] using dyadic_accuracy 0
  refine ⟨_,_,_,by
    unfold monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
    source_space⟩

theorem precall_degrees : (precallSubstitution.fields,precallSubstitution.symbols,precallSubstitution.accuracy)=(3,0,3) := rfl

theorem precall_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Rated
    (fun x => GeneralPaperPrecallCachePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat (W x) x.m x.k) 3 0 3 := by
  have h := (GeneralPaperFastFrontStorageRates.precallCertificate C d W hW).bound
  change Rated (fun x => GeneralPaperPrecallCachePrice.profile (GeneralPaperFastRationalMajorant.model C d).rat (W x) x.m x.k) 1 2 1 at h
  exact soft_trans precallSubstitution.bound h

theorem grid_bits_rate : Rated (fun x => (GeneralPaperProxyParameters.prepare x.m x.k).gridBits) 1 0 1 :=
  GeneralPaperSourceSoftBounds.dominated GeneralPaperFastDriverIndexReference.front_measure_rate
    (fun x => by have h := (GeneralPaperPrecallControlWord.root_controls x.m x.k).1;omega)

def zeroQueryCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperFastInputClassifier.queryProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hH := GeneralPaperBasisStorageRates.determinant_length
  have hQ := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  have hGB := grid_bits_rate
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperFastInputClassifier.queryProfile,GeneralPaperFastInputQuotient.profile,GeneralPaperFastInputQuotient.width,
      GeneralPaperCFOperandPrice.width,GeneralPaperPrecallCachePrice.specification,GeneralPaperFastRationalMajorant.model]
    source_space⟩

def zeroClassifierCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperFastInputClassifier.profile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hs := of_tight hW
  have hQuery := (zeroQueryCertificate C d W hW).bound
  have hQ := GeneralPaperSourceEndpointFractionConstructionStorageRates.grid_word_sharp
  refine ⟨_,_,_,by
    dsimp only [GeneralPaperFastInputClassifier.profile,GeneralPaperSelectionPoints.width,GeneralPaperFastRationalMajorant.model]
    source_space⟩

def zeroFrontCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperFastInputClassifier.prepareProfile (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hp := precall_rate C d W hW
  have hClass := (zeroClassifierCertificate C d W hW).bound
  refine ⟨_,_,_,by dsimp only [GeneralPaperFastInputClassifier.prepareProfile];source_space⟩

def zeroPreparedCertificate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperFastPreparedInputStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv 0) := by
  have hp : Rated (fun x => GeneralPaperFastInputClassifier.prepareProfile
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k 0) 3 0 3 := (zeroFrontCertificate C d W hW).bound
  have hc : Rated (fun x => GeneralPaperSourceControlsConstructionStorage.price
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m (alphabet x).lambda x.k x.Qv) 0 0 0 :=
    poly (GeneralPaperSourceControlStorageRates.control_price_polylog C d W hW)
  have hg : Rated (fun x => GeneralPaperControlMaterializationStorage.price
      (GeneralPaperFastRationalMajorant.model C d) x.m (alphabet x).lambda x.k x.Qv) 0 0 1 :=
    (GeneralPaperFastWholeDriverStorageRates.materializationWorkCertificate C d).bound
  have hw : Rated (fun x => 64*W x) 0 0 0 :=
    poly (poly_mul _ _ (poly_constant 64) (poly_tight W hW))
  have h1 := GeneralPaperSourceRateAlgebra.add _ _ 3 0 3 0 0 0 hp hc
  have h2 := GeneralPaperSourceRateAlgebra.add _ _ 3 0 3 0 0 0 h1 hw
  have h3 := GeneralPaperSourceRateAlgebra.add _ _ 3 0 3 0 0 1 h2 hg
  exact ⟨3,0,3,GeneralPaperSourceRateAlgebra.add _ _ 3 0 3 0 0 0 h3 (constant 128)⟩

theorem zero_degrees (C d : ℕ) (W : Input → ℕ) (hW : Tight W) :
    ((zeroQueryCertificate C d W hW).fields,(zeroQueryCertificate C d W hW).symbols,(zeroQueryCertificate C d W hW).accuracy)=(2,0,2) ∧
      ((zeroClassifierCertificate C d W hW).fields,(zeroClassifierCertificate C d W hW).symbols,(zeroClassifierCertificate C d W hW).accuracy)=(2,0,2) ∧
      ((zeroFrontCertificate C d W hW).fields,(zeroFrontCertificate C d W hW).symbols,(zeroFrontCertificate C d W hW).accuracy)=(3,0,3) ∧
      ((zeroPreparedCertificate C d W hW).fields,(zeroPreparedCertificate C d W hW).symbols,(zeroPreparedCertificate C d W hW).accuracy)=(3,0,3) := ⟨rfl,rfl,rfl,rfl⟩

theorem rate_positive (x : Input) : 1≤rate x := by unfold rate;omega

theorem bit_rate_positive (x : Input) : 1≤GeneralPaperCompilerSharpWork.bitRate x :=
  (monomial_positive 5 0 4 x).trans (Nat.le_add_right _ _)

theorem lift_source {f : Input → ℕ} (h : Soft GeneralPaperCompilerSharpWork.bitRate f) : Soft rate f :=
  rate_mono h (fun x => by unfold rate;omega)

theorem lift_input {f : Input → ℕ} (h : Soft GeneralPaperFastInputQuotientStorageRates.rate f) : Soft rate f :=
  rate_mono h (fun x => by
    have hm := monomial_mono (by decide : 1≤3) (by decide : 0≤0) (by decide : 1≤6) x
    unfold rate GeneralPaperCompilerSharpWork.bitRate GeneralPaperSourceCallerSharpWork.bitRate GeneralPaperFastInputQuotientStorageRates.rate
    omega)

theorem prepared_split (model : RationalCostModel) (W m k Qv B : ℕ) :
    GeneralPaperFastPreparedInputStorage.price model W m k Qv B≤GeneralPaperFastPreparedInputStorage.price model W m k Qv 0+
      GeneralPaperFastInputQuotientStorageRates.inputOverhead model m k B := by
  have h := GeneralPaperFastInputQuotientStorageRates.source_split model W m k Qv B
  dsimp only [GeneralPaperFastInputClassifier.sourceProfile] at h
  dsimp only [GeneralPaperFastPreparedInputStorage.price,GeneralPaperFastSourceControlStorage.price]
  omega

theorem prepared_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastPreparedInputStorage.price (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv x.B) := by
  have hz : Rated (fun x => GeneralPaperFastPreparedInputStorage.price
      (GeneralPaperFastRationalMajorant.model C d) (W x) x.m x.k x.Qv 0) 3 0 3 := (zeroPreparedCertificate C d W hW).bound
  have hZero := lift_source (GeneralPaperCompilerSharpWork.embed hz (Or.inr (Or.inr ⟨by decide,by decide⟩)))
  have hInput := lift_input (GeneralPaperFastInputQuotientStorageRates.overhead_rate (GeneralPaperFastRationalMajorant.growth C d))
  exact GeneralPaperSourceSoftBounds.dominated (add_same hZero hInput) (fun x => prepared_split _ _ _ _ _ _)

theorem cached_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperCompilerSharpWork.bitRate
    (fun x => GeneralPaperCachedBitPairStorage.price (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv) := by
  have hSource := GeneralPaperCompilerSharpWork.lift_source (source_work_rate C d W hW)
  have hUnit := GeneralPaperCompilerSharpWork.lift_source (unit_rate C d W hW)
  have hValues := GeneralPaperCompilerSharpWork.lift_source (values_rate C d W hW)
  have hScalar := GeneralPaperCompilerSharpWork.lift_source (scalar_rate C d W hW)
  have hCompiler := GeneralPaperCompilerSharpWork.price_rate C d W hW
  have hw : Soft GeneralPaperCompilerSharpWork.bitRate W := poly_at_rate (poly_tight W hW) bit_rate_positive
  have hColumn := add_same (add_same hSource hUnit) (poly_mul_rate (poly_constant 64) hw)
  have hPrepared := add_same (add_same (add_same hValues (poly_mul_rate (poly_constant 2) hColumn)) hCompiler)
    (poly_mul_rate (poly_constant 128) hw)
  apply GeneralPaperSourceSoftBounds.dominated (add_same hScalar hPrepared)
  intro x
  dsimp only [GeneralPaperCachedBitPairStorage.price,GeneralPaperSourcePreparedPairOwners.price,
    GeneralPaperRetainedSourceColumnCallerStorage.price,GeneralPaperSourceWordGrowth.alphabet]
  omega

theorem price_rate (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastWholeDriverStorage.price (GeneralPaperFastRationalMajorant.model C d) C d (W x) x.m x.k x.Qv x.B) :=
  add_same (add_same (prepared_rate C d W hW) (lift_source (cached_rate C d W hW)))
    (poly_mul_rate (poly_constant 192) (poly_at_rate (poly_tight W hW) rate_positive))

theorem price_mono (actual upper : RationalCostModel) (h : ∀ n,actual.rat n≤upper.rat n)
    (C d W m k Qv B : ℕ) : GeneralPaperFastWholeDriverStorage.price actual C d W m k Qv B≤
      GeneralPaperFastWholeDriverStorage.price upper C d W m k Qv B :=
  Nat.add_le_add_right (Nat.add_le_add
    (GeneralPaperFastWholeDriverStorageRates.prepared_price_mono actual upper h W m k Qv B)
    (GeneralPaperCachedBitPairStorageRates.price_mono actual upper h C d W m k Qv)) _

theorem actual_price_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) : Soft rate
    (fun x => GeneralPaperFastWholeDriverStorage.price model C d (W x) x.m x.k x.Qv x.B) :=
  GeneralPaperSourceSoftBounds.dominated (price_rate C d W hW) (fun x =>
    price_mono model (GeneralPaperFastRationalMajorant.model C d) (GeneralPaperFastRationalMajorant.dominates hg)
      C d (W x) x.m x.k x.Qv x.B)

theorem input_collapse (x : Input) (cap : ℕ) (h : x.m≤cap*accuracy x) :
    rate x≤((cap+1)^2+cap+3)*(x.B+1+monomial 3 0 6 x) := by
  let D := (cap+1)^2+cap+2
  have hComp : GeneralPaperCompilerSharpWork.bitRate x≤D*monomial 3 0 6 x := GeneralPaperCompilerSharpWork.collapse x cap h
  have hB : x.B+1≤(D+1)*(x.B+1) := Nat.le_mul_of_pos_left _ (Nat.succ_pos D)
  have hLast := hComp.trans (Nat.mul_le_mul_right _ (Nat.le_succ D))
  change x.B+1+GeneralPaperCompilerSharpWork.bitRate x≤(D+1)*(x.B+1+monomial 3 0 6 x)
  exact (Nat.add_le_add hB hLast).trans_eq (by rw [Nat.succ_eq_add_one];ring)

theorem native_price {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j) :
    let W := GeneralPaperFastDriverReference.width C d x
    (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
      GeneralPaperFastWholeDriverStorage.price model C d W x.m x.k x.Qv x.B := by
  let material : GeneralPaperFastPreparedInputStorage.Cursor x.m (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k x.Qv :=
    ⟨0,0,0,0,Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  exact (GeneralPaperFastDriverReferenceContract.native_bounds hg x hm hQv hp 0 x.m (Nat.zero_le _) (Or.inl rfl)
    material 0 (Nat.zero_le _) 0 (Nat.zero_le _) 0 (Nat.zero_le _)).2

theorem native_time {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      let W := GeneralPaperFastDriverReference.width C d x
      (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
        A*(x.B+1+monomial 3 0 6 x)*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := actual_price_rate hg (GeneralPaperFastDriverReference.width C d) (GeneralPaperFastDriverReference.width_tight C d)
  refine ⟨A*((cap+1)^2+cap+3),e,?_⟩
  intro x hm hQv hp hCap
  exact (native_price hg x hm hQv hp).trans ((h x).trans
    ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (input_collapse x cap hCap))).trans_eq (by ring)))

theorem time_and_return {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (cap : ℕ) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),x.m≤cap*accuracy x →
      let W := GeneralPaperFastDriverReference.width C d x
      ∃ physical pair,(GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).1=some physical ∧
        GeneralPaperSourcePairRun.run x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ)=some pair ∧
        GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
        GeneralPaperSourcePairContract.Contract x.k x.Qv hQv x.weights hp x.weight_sum (x.b:ℝ) pair ∧
        (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
          A*(x.B+1+monomial 3 0 6 x)*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := native_time hg cap
  refine ⟨A,e,?_⟩
  intro x hm hQv hp hCap
  obtain ⟨physical,pair,hNative,hSource,hMatch,hContract⟩ := GeneralPaperFastDriverReferenceContract.actual_return
    model (GeneralPaperFastDriverReference.width C d x) x.k x.Qv hQv x.weights hp x.weight_sum x.b hm x.hb
  exact ⟨physical,pair,hNative,hSource,hMatch,hContract,h x hm hQv hp hCap⟩

end Blotto.GeneralPaperFastDriverSharpWork
