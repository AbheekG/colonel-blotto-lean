import Blotto.GeneralPaperCachedBitPairStorageRates

/-! The reference now covers the actual cached bit-pair driver, both scalar
constructors, complete owners and every prior source/compiler lifetime.
Original rational front/grid construction and original-field phases are
separate remaining joins. No native algorithm or cache is replayed. -/
namespace Blotto.GeneralPaperCachedBitPairReferenceContract
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperReferenceScaling GeneralPaperReferenceCapacity
open GeneralPaperProxyParameters
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 16384

noncomputable def profile (C d W : ℕ) (x : Input) : ℕ :=
  GeneralPaperCachedBitPairStorageRates.reservation (GeneralPaperFastRationalMajorant.model C d) C d W x.m x.k x.Qv x.B+
    GeneralPaperCompilerReference.indexSize x.m x.k*W

theorem scaling (C d : ℕ) (x : Input) : Scale (fun W => profile C d W x) := by
  have h := GeneralPaperCachedBitPairStorageRates.reservation_scaling (GeneralPaperFastRationalMajorant.model C d) C d x.m x.k x.Qv x.B
  unfold profile
  fun_prop

noncomputable def width (C d : ℕ) (x : Input) : ℕ :=
  referenceWord (profile C d 1 x)+GeneralPaperPrecallControlWord.word x.m x.k

theorem positive_width (C d : ℕ) (x : Input) : 1≤width C d x := by
  have h := positive (profile C d 1 x)
  unfold width
  omega

theorem control_word (C d : ℕ) (x : Input) : GeneralPaperPrecallControlWord.word x.m x.k≤width C d x := by
  unfold width
  omega

theorem capacity (C d : ℕ) (x : Input) : profile C d (width C d x) x<2^width C d x :=
  padded_profile_capacity (fun W => profile C d W x) (scaling C d x) _

theorem address_word (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤profile C d (width C d x) x) : binaryWordWidth address≤width C d x :=
  binaryWordWidth_le_of_lt_pow (positive_width C d x) (h.trans_lt (capacity C d x))

theorem index_address (C d : ℕ) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperCompilerReference.indexSize x.m x.k) : binaryWordWidth address≤width C d x := by
  apply address_word C d x address
  have hw := Nat.mul_le_mul_left (GeneralPaperCompilerReference.indexSize x.m x.k) (positive_width C d x)
  unfold profile
  nlinarith only [h,hw,Nat.zero_le (GeneralPaperCachedBitPairStorageRates.reservation
    (GeneralPaperFastRationalMajorant.model C d) C d (width C d x) x.m x.k x.Qv x.B)]

theorem local_words (C d : ℕ) (x : Input) :
    let p := GeneralPaperProxyParameters.prepare x.m x.k
    let W := width C d x
    binaryWordWidth (x.m*(p.K-1)+3)≤W ∧
    binaryWordWidth (p.K+1)≤W ∧ binaryWordWidth (x.m+1)≤W ∧
    binaryWordWidth (p.S+2)≤W ∧ binaryWordWidth ((p.S+1)*(p.K*p.K)+3)≤W ∧
    binaryWordWidth (p.S+4)≤W ∧ binaryWordWidth (x.m+p.K+1)≤W ∧
    binaryWordWidth (2*(GeneralPaperTrajectoryParameters.prepare (alphabet x).lambda x.k).rows+p.K+x.m+1)≤W := by
  dsimp only
  refine ⟨index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_,index_address C d x _ ?_,
    index_address C d x _ ?_,index_address C d x _ ?_⟩
  all_goals unfold GeneralPaperCompilerReference.indexSize;dsimp only [GeneralPaperSourceWordGrowth.alphabet];omega

theorem at_one_small (C d : ℕ) : Small (fun x => profile C d 1 x) := by
  have h := GeneralPaperCachedBitPairStorageRates.reservation_at_one_small C d
  unfold profile
  fun_prop

theorem width_tight (C d : ℕ) : Tight (width C d) :=
  tight_add _ _ (tight_mul_left 4 _ (word_tight _ (at_one_small C d)))
    GeneralPaperLogarithmicSourceReference.controls_tight

theorem logarithmic_width (C d : ℕ) : ∃ A : ℕ,∀ x,width C d x≤A*logSize x := width_tight C d

def indexCertificate (W : Input → ℕ) (hW : Tight W) : Certificate
    (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) := by
  have hr : Rated W 0 0 0 := poly (poly_tight W hW)
  have hRows := GeneralPaperSourceStaticConstructionRates.sharp_rows
  refine ⟨_,_,_,by
    unfold GeneralPaperCompilerReference.indexSize
    dsimp only
    source_space⟩

theorem index_degrees (W : Input → ℕ) (hW : Tight W) :
    ((indexCertificate W hW).fields,(indexCertificate W hW).symbols,(indexCertificate W hW).accuracy)=(1,0,3) := rfl

theorem profile_soft (C d : ℕ) (W : Input → ℕ) (hW : Tight W) : Soft GeneralPaperSourcePreparedPairOwnerRates.rate
    (fun x => profile C d (W x) x) := by
  have hR := GeneralPaperCachedBitPairStorageRates.majorant_rate C d W hW
  have hi : Rated (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) 3 0 4 :=
    weaken (indexCertificate W hW).bound (by decide : 1≤3) (by decide : 0≤0) (by decide : 3≤4)
  have hI : Soft GeneralPaperSourcePreparedPairOwnerRates.rate (fun x => GeneralPaperCompilerReference.indexSize x.m x.k*W x) := rate_mono hi (fun x => by unfold GeneralPaperSourcePreparedPairOwnerRates.rate;omega)
  exact add_same hR hI

theorem common_word_bound (C d : ℕ) : ∃ A e : ℕ,∀ x,profile C d (width C d x) x≤
    A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := profile_soft C d (width C d) (width_tight C d)
  refine ⟨A,e,?_⟩
  intro x
  have he : (GeneralPaperNativeSourceRates.accuracy x)^4=2^(4*x.k) := by simp only [GeneralPaperNativeSourceRates.accuracy,←pow_mul,Nat.mul_comm x.k 4]
  simpa only [GeneralPaperSourcePreparedPairOwnerRates.rate,monomial,pow_zero,Nat.mul_one,
    GeneralPaperNativeSourceRates.fields,he,Nat.mul_assoc] using h x

theorem actual_reserve {actual : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth actual C d) (W : ℕ) (x : Input) :
    GeneralPaperCachedBitPairStorageRates.reservation actual C d W x.m x.k x.Qv x.B≤profile C d W x :=
  (GeneralPaperCachedBitPairStorageRates.reservation_mono actual (GeneralPaperFastRationalMajorant.model C d)
    (GeneralPaperFastRationalMajorant.dominates hg) C d W x.m x.k x.Qv x.B).trans (Nat.le_add_right _ _)


theorem row_words (C d : ℕ) (x : Input) :
    let W := width C d x
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W ∧
    binaryWordWidth ((GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1)≤W := by
  have h := (local_words C d x).2.2.2.2.2.2.2
  refine ⟨?_,?_⟩
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h
  · exact (binaryWordWidth_mono (show
      (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+
        (GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+1≤
      2*(GeneralPaperTrajectoryParameters.prepare (alphabet x.m x.k).lambda x.k).rows+(prepare x.m x.k).K+x.m+1 by omega)).trans h


theorem prepared_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperSourcePreparedPairOwnerRates.reservation model C d W m k Qv B≤
      GeneralPaperCachedBitPairStorageRates.reservation model C d W m k Qv B := by
  unfold GeneralPaperCachedBitPairStorageRates.reservation
  omega

theorem modified_reserve_le (model : RationalCostModel) (C d W m k Qv B : ℕ) :
    GeneralPaperSourceModifiedColumnStorageRates.reservation model C d W m k Qv≤
      GeneralPaperCachedBitPairStorageRates.reservation model C d W m k Qv B :=
  (GeneralPaperPreparedPairReferenceContract.modified_reserve_le model C d W m k Qv B).trans
    (prepared_reserve_le model C d W m k Qv B)

theorem complete_reserve_capacity {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) :
    GeneralPaperCachedBitPairStorageRates.reservation model C d (width C d x) x.m x.k x.Qv x.B<2^width C d x :=
  (actual_reserve hg _ x).trans_lt (capacity C d x)

theorem reserved_address {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (address : ℕ)
    (h : address≤GeneralPaperCachedBitPairStorageRates.reservation model C d (width C d x) x.m x.k x.Qv x.B) :
    binaryWordWidth address≤width C d x :=
  address_word C d x address (h.trans (actual_reserve hg _ x))

theorem native_bounds {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := width C d x
    ∀ cursor hc outer ho inner hi,
      GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
        GeneralPaperCachedBitPairStorage.profile model C d W x.m x.k x.Qv x.B ∧
      (GeneralPaperCachedBitPairStorage.run model W x.k x.Qv hQv x.weights hp x.weight_sum x.b).2≤
        GeneralPaperCachedBitPairStorage.price model C d W x.m x.k x.Qv := by
  dsimp only
  intro cursor hc outer ho inner hi
  have hw := positive_width C d x
  have h := local_words C d x
  have hr := row_words C d x
  have hPrepared := GeneralPaperSourcePreparedPairOwners.bounded model (width C d x)
    x.k x.Qv hQv x.weights hp x.weight_sum x.b C d x.B hg hm x.hb x.hB hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 h.2.2.2.2.2.1 hr.2
    cursor hc outer ho inner hi
  exact GeneralPaperCachedBitPairStorage.bounded_of_prepared model C d (width C d x) x.k x.Qv x.B hQv
    x.weights hp x.weight_sum x.b x.hb cursor hc outer ho inner hi hPrepared

theorem native_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) :
    let W := width C d x
    ∀ cursor hc outer ho inner hi,
      GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤profile C d W x ∧
      (GeneralPaperCachedBitPairStorage.run model W x.k x.Qv hQv x.weights hp x.weight_sum x.b).2≤
        GeneralPaperCachedBitPairStorage.price model C d W x.m x.k x.Qv ∧
      (∀ address,address≤GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi →
        binaryWordWidth address≤W) := by
  dsimp only
  intro cursor hc outer ho inner hi
  have h := native_bounds hg x hm hQv hp cursor hc outer ho inner hi
  have hWindow := h.1.trans ((Nat.le_add_left _ _).trans (actual_reserve hg _ x))
  exact ⟨hWindow,h.2,fun address hAddress => address_word C d x address (hAddress.trans hWindow)⟩

theorem paper_space {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∃ A e : ℕ,∀ (x : Input) (_hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j),
      let W := width C d x
      ∀ cursor hc outer ho inner hi,
        GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤
          A*(x.B+1+(x.m+1)^3*2^(4*x.k))*(logSize x)^e := by
  obtain ⟨A,e,h⟩ := common_word_bound C d
  exact ⟨A,e,fun x hm hQv hp cursor hc outer ho inner hi =>
    ((native_window hg x hm hQv hp cursor hc outer ho inner hi).1).trans (h x)⟩

theorem actual_return {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv)
    (b : ℚ) (hm : 0<m) (hb : 0<b ∧ b<1) (cache : GeneralPaperCachedSourcePair.Input m k Qv (b:ℝ)) :
    ∃ physical pair,(GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hs (b:ℝ) cache).1=some physical ∧
      GeneralPaperSourcePairRun.run k Qv hQv weights hp hs (b:ℝ)=some pair ∧
      GeneralPaperOriginalDrawEquilibrium.Matches physical pair ∧
      GeneralPaperSourcePairContract.Contract k Qv hQv weights hp hs (b:ℝ) pair := by
  obtain ⟨physical,pair,hNative,hSource,hMatch,hContract⟩ := GeneralPaperSourcePreparedPairOwners.actual_return
    model W k Qv hQv weights hp hs b hm hb
  have hc := congrArg Prod.fst (GeneralPaperCachedBitPairStorage.actual_input model W k Qv hQv weights hp hs b cache)
  have hd := congrArg Prod.fst (GeneralPaperCachedBitPairStorage.run_data model W k Qv hQv weights hp hs b)
  exact ⟨physical,pair,hc.trans (hd.trans hNative),hSource,hMatch,hContract⟩

theorem reached_controller {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : ¬(reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0)),
        let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
        let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        ∃ state,(GeneralPaperBasisControllerBits.stages model W prep.dictionary.label inputs.matrix (prepare z.m z.k).S prep.threshold
          inputs.controls.N inputs.betaN inputs.initialGrid (z.m*((prepare z.m z.k).K-1)) le_rfl).1=some state ∧
          GeneralPaperSourceModifiedColumnStorage.AtBound
            (fun constructionBound => GeneralPaperSourceCompilerBranchStorage.AtBound
              (fun compilerBound => GeneralPaperSourceColumnCallerStorage.AtBound
              (fun bound => GeneralPaperSourceRowsCallerStorage.AtBound
              (fun limit => GeneralPaperSourceUnitCallerStorage.AtBound model W z.k limit b reciprocal prep inputs state
            (GeneralPaperSourceEnclosingOwners.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceStrictConstructorStorage.parentWindow model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (GeneralPaperSourceEnclosingOwners.columns model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperRetainedFieldValues.run true model W z.Qv hQv z.weights hp z.weight_sum).1
            (GeneralPaperInitializerPreparedPoint.ownBudget z.m z.k b reciprocal) (GeneralPaperInitializerPreparedPoint.opposingBudget z.m z.k b reciprocal)
            (GeneralPaperSourceDictionaryNormalizationStorage.quantized model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceQuantizedAnchorStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceRepresentativeSortStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceColumnInputStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceBlockDivisionStorage.window model W z.m z.k)
            (GeneralPaperSourceLabelScatterStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceQuantizationParentStorage.window model W z.k z.Qv z.weights b reciprocal)
            (GeneralPaperSourceUnitCallerStorage.window model W z.k z.Qv z.weights b reciprocal))
            (GeneralPaperSourceRowsCallerStorage.window model W z.k z.Qv z.weights b reciprocal) bound)
            (GeneralPaperSourceColumnCallerStorage.window model W z.k z.Qv z.weights b reciprocal) compilerBound)
            (GeneralPaperSourceCompilerBranchStorage.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal) constructionBound)
            (GeneralPaperSourceModifiedColumnStorage.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal)
            (profile C d W z) := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := width C d z
  have hw := positive_width C d z
  have h := local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (actual_reserve hg W z)
  obtain ⟨state,hNative,hBound⟩ := GeneralPaperSourceModifiedColumnStorage.actual_reached hg W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1 h.1 h.2.2.2.2.1 hr.1 hr.2 h.2.2.2.2.2.1
  refine ⟨state,hNative,?_⟩
  exact GeneralPaperSourceModifiedColumnStorage.bound_mono _ _ _ _ hTop hBound

theorem guard_lifetimes {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) :
    ∀ z : Input,
      let W := width C d z
      ∀ (_hm : 0<z.m) (hQv : 0<z.Qv) (hp : ∀ j,0<z.weights.read j)
        (b : ℝ) (_hb : 0<b ∧ b<1) (reciprocal : Bool)
        (_hModify : (GeneralPaperProxyClassifier.classify z.m z.k b).choice.modify≠none)
        (_hGuard : reciprocal=true ∧ (GeneralPaperProxyClassifier.classify z.m z.k b).choice.endpoint=0),
        let prep := GeneralPaperSourceInitializer.prepared z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal
        let v := GeneralPaperNativeRationalValues.selector z.Qv hQv z.weights hp z.weight_sum
        let f := (GeneralPaperProxyClassifier.classify z.m z.k b).choice.proxy
        let inputs := GeneralPaperSharedBasisInputs.prepare z.k prep v f.num f.den reciprocal
        GeneralPaperSourceOuterEndpointStorage.window model W z.k b reciprocal prep inputs+
          GeneralPaperSourceEndpointFractionConstructionStorage.window model W z.m z.k b+
          GeneralPaperSourceEnclosingOwners.window model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal+
          GeneralPaperSourceStrictConstructorStorage.parentWindow model W z.k z.Qv hQv z.weights hp z.weight_sum b reciprocal+
          GeneralPaperSourceMatrixStorage.sourceProfile model W z.m z.k z.Qv+GeneralPaperSourceScoreStorage.profile model W z.m z.k+
          GeneralPaperScoreResidencyRates.initialProfile model W z.m z.k+GeneralPaperSourceScoreResidents.thresholdProfile model W z.m z.k+
          GeneralPaperSourceGuardStorage.sourceProfile model W z.m z.k z.Qv+
          GeneralPaperSourceDictionaryNormalizationStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceQuantizedAnchorStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceRepresentativeSortStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceColumnInputStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceBlockDivisionStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceLabelScatterStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceQuantizationParentStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceUnitCallerStorageRates.sourceProfile model W z.m z.k+
          GeneralPaperSourceRowsCallerStorageRates.sourceProfile C d W z.m z.k z.Qv+
          GeneralPaperSourceColumnCallerStorageRates.sourceProfile model C d W z.m z.k z.Qv+
          GeneralPaperSourceCompilerBranchStorageRates.sourceProfile model W z.m z.k z.Qv+
          GeneralPaperSourceModifiedColumnStorageRates.sourceProfile model W z.m z.k z.Qv≤
            profile C d W z := by
  intro z
  dsimp only
  intro hm hQv hp b hb reciprocal hModify hGuard
  let W := width C d z
  have hw := positive_width C d z
  have h := local_words C d z
  have hr := row_words C d z
  have hTop := (modified_reserve_le model C d W z.m z.k z.Qv z.B).trans
    (actual_reserve hg W z)
  exact (GeneralPaperSourceModifiedColumnStorage.guard_stage model C d W z.k z.Qv hm hQv z.weights hp z.weight_sum b hb reciprocal hModify hGuard
    hw h.2.1 h.2.2.1 h.2.2.2.1).trans hTop


theorem simultaneous_window {model : RationalCostModel} {C d : ℕ}
    (hg : GeneralPaperFastRationalModel.Growth model C d) (x : Input) (hm : 0<x.m) (hQv : 0<x.Qv)
    (hp : ∀ j,0<x.weights.read j) (oldOwner : ℕ)
    (hOld : oldOwner≤GeneralPaperSourcePreparedPairOwnerRates.reservation model C d (width C d x) x.m x.k x.Qv x.B) :
    let W := width C d x
    ∀ cursor hc outer ho inner hi,
      oldOwner+GeneralPaperCachedBitPairStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b cursor hc outer ho inner hi≤profile C d W x := by
  dsimp only
  intro cursor hc outer ho inner hi
  have hNative := (native_bounds hg x hm hQv hp cursor hc outer ho inner hi).1
  have hSum := Nat.add_le_add hOld hNative
  exact hSum.trans (actual_reserve hg _ x)

end Blotto.GeneralPaperCachedBitPairReferenceContract
