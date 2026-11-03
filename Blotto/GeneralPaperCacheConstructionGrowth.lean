import Blotto.GeneralPaperSortedConstructionProfileRates

/-! Original-size cache construction is linear up to proved logarithms.
The original field count is kept separate from the reduced-field/accuracy
monomial, preserving an additive original-input term in working space. -/
namespace Blotto.GeneralPaperCacheConstructionGrowth
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperConstructedWordGrowth GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 20000000
set_option maxRecDepth 16384

@[fun_prop]
def Linear (f n : Input → ℕ) : Prop := Soft (fun x => n x+1) f

@[fun_prop]
theorem linear_identity (n : Input → ℕ) : Linear n n := by
  apply bounded 1
  intro x
  omega

@[fun_prop]
theorem linear_poly (f n : Input → ℕ) (hf : Polylog f) : Linear f n :=
  poly_at_rate hf (fun _ => by omega)

@[fun_prop]
theorem linear_add (f g n : Input → ℕ) (hf : Linear f n) (hg : Linear g n) :
    Linear (fun x => f x+g x) n := add_same hf hg

@[fun_prop]
theorem linear_mul_left (f g n : Input → ℕ) (hf : Polylog f) (hg : Linear g n) :
    Linear (fun x => f x*g x) n := poly_mul_rate hf hg

@[fun_prop]
theorem linear_mul_right (f g n : Input → ℕ) (hf : Linear f n) (hg : Polylog g) :
    Linear (fun x => f x*g x) n := mul_poly hf hg

theorem small_of_poly {f : Input → ℕ} (hf : Polylog f) : Small f :=
  GeneralPaperSourceRowsStorageRates.soft_small hf (small_constant 1)

@[fun_prop]
theorem linear_constant (c : ℕ) (n : Input → ℕ) : Linear (fun _ => c) n :=
  linear_poly _ n (poly_constant c)

@[fun_prop]
theorem linear_word (f n : Input → ℕ) (hf : Small f) : Linear (fun x => binaryWordWidth (f x)) n :=
  linear_poly _ n (poly_word f hf)

@[fun_prop]
theorem linear_charge (C d : ℕ) (f n : Input → ℕ) (hf : Polylog f) (hw : Small f) :
    Linear (fun x => GeneralPaperFastRationalModel.charge C d (f x)) n :=
  linear_poly _ n (poly_charge C d f hf hw)

@[fun_prop]
theorem fill (n W P C Q : Input → ℕ) (hn : Small n) (hW : Tight W)
    (hp : Polylog P) (hc : Polylog C) (hq : Polylog Q) :
    Linear (fun x => GeneralPaperNativePayloadFillStorage.profile (W x) (P x) (n x) (C x) (Q x)) n := by
  have hw := of_tight hW
  have hcSmall := small_of_poly hc
  have hr : Polylog W := poly_tight W hW
  unfold GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap natBits
  fun_prop (config := {maxSteps := 20000})

theorem common_linear (C d : ℕ) (W g R mass : Input → ℕ) (hW : Tight W)
    (hg : Small g) (hR : Small R) (hMass : Small mass) :
    Linear (fun x => GeneralPaperSharedCacheConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (g x) (R x) (mass x)) g := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  unfold GeneralPaperSharedCacheConstructionStorage.profile GeneralPaperCircleCoefficientConstructionStorage.profile
    GeneralPaperCircleCoefficientConstructionStorage.scalarProfile GeneralPaperCircleCoefficientConstructionStorage.scalarCap
    GeneralPaperCircleCoefficientConstructionStorage.metadataCap GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleRationalCoefficients.width
    GeneralPaperCircleArcConstructionStorage.profile GeneralPaperCircleArcConstructionStorage.frameProfile
    GeneralPaperCircleArcConstructionStorage.cap GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.cap GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.magnitude GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperStockListPayloadStorage.ofFnProfile GeneralPaperCachedCircleRetainedStorage.commonProfile
    GeneralPaperEncodedBasisStorage.arrayProfile natBits
  dsimp only [GeneralPaperCircleCoefficientConstructionStorage.price,GeneralPaperCircleCoefficientConstructionStorage.callbackPrice,
    GeneralPaperCircleRationalCoefficients.width,GeneralPaperCircleArcConstructionStorage.price,
    GeneralPaperSharedCacheConstructionStorage.magnitude,GeneralPaperNativePayloadFillStorage.workCap,
    GeneralPaperFastRationalMajorant.model]
  fun_prop (config := {maxSteps := 20000})

def extraProfile (model : RationalCostModel) (W n g R mass : ℕ) : ℕ :=
  GeneralPaperNativePayloadFillStorage.profile W (natBits mass) g (64*W)
    (GeneralPaperSharedCacheConstructionStorage.lightScalarProfile W n g mass)+
    GeneralPaperSharedCacheConstructionStorage.profile model W g R mass+
    5*(natBits (GeneralPaperNativePayloadFillStorage.workCap W g (64*W)+
      GeneralPaperSharedCacheConstructionStorage.price model W g R mass+64*W)+W)+160*W

theorem original_decomposition {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperSharedCacheConstructionStorage.originalProfile model W o=
      GeneralPaperOriginalReductionRetainedStorage.footprint W o+
        extraProfile model W n o.classified.light.size o.representatives o.classified.lightWeight := by
  unfold GeneralPaperSharedCacheConstructionStorage.originalProfile GeneralPaperSharedCacheConstructionStorage.originalPrice extraProfile
  ring

theorem extra_linear (C d : ℕ) (W n g R mass : Input → ℕ) (hW : Tight W)
    (hn : Small n) (hg : Small g) (hR : Small R) (hMass : Small mass) :
    Linear (fun x => extraProfile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (n x) (g x) (R x) (mass x)) g := by
  have hw := of_tight hW
  have hr : Polylog W := poly_tight W hW
  have hCommon := common_linear C d W g R mass hW hg hR hMass
  unfold extraProfile GeneralPaperSharedCacheConstructionStorage.lightScalarProfile
    GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleRationalCoefficients.width
    GeneralPaperCircleArcConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.magnitude
    GeneralPaperNativePayloadFillStorage.workCap natBits
  dsimp only [GeneralPaperFastRationalMajorant.model] at hCommon ⊢
  fun_prop (config := {maxSteps := 20000})

theorem extra_at_original_count (C d : ℕ) (W n g R mass : Input → ℕ) (hW : Tight W)
    (hn : Small n) (hg : Small g) (hR : Small R) (hMass : Small mass) (hgn : ∀ x,g x≤n x) :
    Soft (fun x => n x+1) (fun x => extraProfile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (n x) (g x) (R x) (mass x)) :=
  rate_mono (extra_linear C d W n g R mass hW hn hg hR hMass) (fun x => Nat.add_le_add_right (hgn x) 1)

theorem common_model_mono (actual upper : RationalCostModel) (hPrice : ∀ w,actual.rat w≤upper.rat w)
    (W g R mass : ℕ) :
    GeneralPaperSharedCacheConstructionStorage.profile actual W g R mass≤
      GeneralPaperSharedCacheConstructionStorage.profile upper W g R mass := by
  unfold GeneralPaperSharedCacheConstructionStorage.profile GeneralPaperCircleCoefficientConstructionStorage.profile
    GeneralPaperCircleCoefficientConstructionStorage.scalarProfile GeneralPaperCircleCoefficientConstructionStorage.scalarCap
    GeneralPaperCircleCoefficientConstructionStorage.metadataCap GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.profile
    GeneralPaperCircleArcConstructionStorage.frameProfile GeneralPaperCircleArcConstructionStorage.cap GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperSharedCacheConstructionStorage.cap GeneralPaperSharedCacheConstructionStorage.price
    GeneralPaperNativePayloadFillStorage.profile GeneralPaperNativePayloadFillStorage.frameProfile
    GeneralPaperNativePayloadFillStorage.metadataCap GeneralPaperNativePayloadFillStorage.workCap
  dsimp only [GeneralPaperCircleCoefficientConstructionStorage.price,GeneralPaperCircleCoefficientConstructionStorage.callbackPrice,
    GeneralPaperCircleArcConstructionStorage.price,GeneralPaperNativePayloadFillStorage.workCap,natBits]
  gcongr <;> exact hPrice _

theorem extra_model_mono (actual upper : RationalCostModel) (hPrice : ∀ w,actual.rat w≤upper.rat w)
    (W n g R mass : ℕ) : extraProfile actual W n g R mass≤extraProfile upper W n g R mass := by
  have hCommon := common_model_mono actual upper hPrice W g R mass
  unfold extraProfile
  apply Nat.add_le_add_right
  apply Nat.add_le_add
  · exact Nat.add_le_add_left hCommon _
  · unfold GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
      GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.price
      GeneralPaperNativePayloadFillStorage.workCap natBits
    gcongr <;> exact hPrice _

theorem original_extra_rate {model : RationalCostModel} {C d : ℕ} (hPrice : GeneralPaperFastRationalModel.Growth model C d)
    (W n g R mass : Input → ℕ) (hW : Tight W) (hn : Small n) (hg : Small g) (hR : Small R) (hMass : Small mass)
    (hgn : ∀ x,g x≤n x) :
    Soft (fun x => n x+1) (fun x => extraProfile model (W x) (n x) (g x) (R x) (mass x)) :=
  GeneralPaperSourceSoftBounds.dominated (extra_at_original_count C d W n g R mass hW hn hg hR hMass hgn)
    (fun x => extra_model_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hPrice) (W x) (n x) (g x) (R x) (mass x))

theorem fill_return_profile (W P n C Q : ℕ) :
    GeneralPaperEncodedBasisStorage.arrayProfile W n P+32*W≤
      GeneralPaperNativePayloadFillStorage.profile W P n C Q := by
  unfold GeneralPaperEncodedBasisStorage.arrayProfile GeneralPaperNativePayloadFillStorage.profile
  nlinarith only [Nat.zero_le (n*(P+W)),Nat.zero_le ((n+1)*GeneralPaperNativePayloadFillStorage.frameProfile W P n C)]

theorem row_return_profile (model : RationalCostModel) (W T h R K H : ℕ) :
    GeneralPaperCachedCircleRetainedStorage.rowsProfile W T h R K H≤
      GeneralPaperCachedRowConstructionStorage.profile model W T h R K (1+2*H) := by
  have hFill := fill_return_profile W (GeneralPaperEncodedBasisStorage.arrayProfile W R 0) T
    (GeneralPaperCachedRowConstructionStorage.rowPrice model W R (1+2*H)+64*W)
    (GeneralPaperCachedRowConstructionStorage.rowProfile model W T h R K (1+2*H)+
      GeneralPaperCachedRowConstructionStorage.tableScalarProfile model W T h R K (1+2*H))
  unfold GeneralPaperCachedCircleRetainedStorage.rowsProfile GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile
    GeneralPaperCachedRowConstructionStorage.profile
  omega

theorem pair_return_profile {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperCachedCircleRetainedStorage.pairProfile W T o.classified.heavy.size o.classified.light.size
      o.representatives o.classified.lightWeight K H≤
      extraProfile model W n o.classified.light.size o.representatives o.classified.lightWeight+
        2*GeneralPaperCachedRowConstructionStorage.profile model W T o.classified.heavy.size o.representatives K (1+2*H)+32*W := by
  have hRows := row_return_profile model W T o.classified.heavy.size o.representatives K H
  have hCommon : GeneralPaperCachedCircleRetainedStorage.commonProfile W o.classified.light.size
      o.representatives o.classified.lightWeight≤
      GeneralPaperSharedCacheConstructionStorage.profile model W o.classified.light.size o.representatives o.classified.lightWeight := by
    unfold GeneralPaperSharedCacheConstructionStorage.profile
    omega
  unfold GeneralPaperCachedCircleRetainedStorage.pairProfile extraProfile
  omega

theorem pair_profile_bound {n : ℕ} (model : RationalCostModel) (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperCachedPairConstructionStorage.profile model W T K H o≤
      GeneralPaperOriginalReductionRetainedStorage.footprint W o+
        2*extraProfile model W n o.classified.light.size o.representatives o.classified.lightWeight+
        4*GeneralPaperCachedRowConstructionStorage.profile model W T o.classified.heavy.size o.representatives K (1+2*H)+
        9*(natBits (GeneralPaperCachedPairConstructionStorage.cap model W T H o)+W)+192*W := by
  have hRetained := pair_return_profile model W T K H o
  unfold GeneralPaperCachedPairConstructionStorage.profile
  rw [original_decomposition]
  omega

def rate (n : Input → ℕ) (x : Input) : ℕ := n x+1+monomial 2 0 3 x

theorem pair_majorant_rate (C d : ℕ) (W n : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hM : ∀ x,(o x).m=x.m)
    (hG : Small (fun x => (o x).classified.light.size)) (hR : Small (fun x => (o x).representatives))
    (hMass : Small (fun x => (o x).classified.lightWeight))
    (hGN : ∀ x,(o x).classified.light.size≤n x)
    (hHeavy : ∀ x,(o x).classified.heavy.size≤x.m) (hRep : ∀ x,(o x).representatives≤x.m)
    (hOwner : Soft (fun x => n x+1) (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x))) :
    Soft (rate n) (fun x => GeneralPaperCachedPairConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x)) := by
  have hw := of_tight hW
  have hA := GeneralPaperSortedConstructionProfileRates.anchor_small
  have hMsmall : Small (fun x => (o x).m) := dominated m_small (fun x => by rw [hM x])
  have hExtra := extra_at_original_count C d W n (fun x => (o x).classified.light.size)
    (fun x => (o x).representatives) (fun x => (o x).classified.lightWeight) hW hn hG hR hMass hGN
  have hRows := GeneralPaperSortedConstructionProfileRates.native_profile (GeneralPaperFastRationalMajorant.growth C d) W hW
    (fun x => (o x).classified.heavy.size) (fun x => (o x).representatives) hHeavy hRep
  have hControl : Polylog (fun x => 9*(natBits (GeneralPaperCachedPairConstructionStorage.cap
      (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x))+W x)+192*W x) := by
    have hr : Polylog W := poly_tight W hW
    unfold GeneralPaperCachedPairConstructionStorage.cap GeneralPaperCachedPairConstructionStorage.price
      GeneralPaperSharedCacheConstructionStorage.originalPrice GeneralPaperSharedCacheConstructionStorage.price
      GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
      GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
      GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
      GeneralPaperCircleCoefficientConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.callbackPrice
      GeneralPaperCircleRationalCoefficients.width GeneralPaperCircleArcConstructionStorage.price
      GeneralPaperSharedCacheConstructionStorage.magnitude GeneralPaperNativePayloadFillStorage.workCap natBits
    dsimp only [GeneralPaperFastRationalMajorant.model]
    fun_prop (config := {maxSteps := 20000})
  have hOwn' : Soft (rate n) (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x)) :=
    rate_mono hOwner (fun x => by unfold rate;omega)
  have hExtra' : Soft (rate n) (fun x => extraProfile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (n x) (o x).classified.light.size (o x).representatives (o x).classified.lightWeight) :=
    rate_mono hExtra (fun x => by unfold rate;omega)
  have hRows' : Soft (rate n) (fun x => GeneralPaperCachedRowConstructionStorage.profile (GeneralPaperFastRationalMajorant.model C d)
      (W x) (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (o x).classified.heavy.size (o x).representatives (GeneralPaperProxyParameters.prepare x.m x.k).K
      (1+2*GeneralPaperSourcePairAnchorHeights.width x.m x.k)) :=
    rate_mono hRows (fun x => by unfold rate;omega)
  have hControl' : Soft (rate n) (fun x => 9*(natBits (GeneralPaperCachedPairConstructionStorage.cap
      (GeneralPaperFastRationalMajorant.model C d) (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x))+W x)+192*W x) :=
    poly_at_rate hControl (fun x => by unfold rate;omega)
  apply GeneralPaperSourceSoftBounds.dominated
    (add_same (add_same (add_same hOwn' (poly_mul_rate (poly_constant 2) hExtra'))
      (poly_mul_rate (poly_constant 4) hRows')) hControl')
  intro x
  simpa only [Nat.add_assoc] using pair_profile_bound (GeneralPaperFastRationalMajorant.model C d) (W x)
    (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
    (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x)

theorem pair_model_mono {n : ℕ} (actual upper : RationalCostModel) (hPrice : ∀ w,actual.rat w≤upper.rat w)
    (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperCachedPairConstructionStorage.profile actual W T K H o≤
      GeneralPaperCachedPairConstructionStorage.profile upper W T K H o := by
  have hOriginal : GeneralPaperSharedCacheConstructionStorage.originalProfile actual W o≤
      GeneralPaperSharedCacheConstructionStorage.originalProfile upper W o := by
    rw [original_decomposition,original_decomposition]
    exact Nat.add_le_add_left (extra_model_mono actual upper hPrice _ _ _ _ _) _
  have hRows := GeneralPaperSortedConstructionProfileRates.model_mono actual upper hPrice W T
    o.classified.heavy.size o.representatives K (1+2*H)
  have hCap : GeneralPaperCachedPairConstructionStorage.cap actual W T H o≤
      GeneralPaperCachedPairConstructionStorage.cap upper W T H o := by
    unfold GeneralPaperCachedPairConstructionStorage.cap GeneralPaperCachedPairConstructionStorage.price
      GeneralPaperSharedCacheConstructionStorage.originalPrice GeneralPaperSharedCacheConstructionStorage.price
      GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
      GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
      GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile
      GeneralPaperCircleCoefficientConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.callbackPrice
      GeneralPaperCircleArcConstructionStorage.price GeneralPaperNativePayloadFillStorage.workCap
    gcongr <;> exact hPrice _
  have hf := Nat.add_le_add_left (binaryWordWidth_mono hCap) 1
  change natBits (GeneralPaperCachedPairConstructionStorage.cap actual W T H o)≤
    natBits (GeneralPaperCachedPairConstructionStorage.cap upper W T H o) at hf
  unfold GeneralPaperCachedPairConstructionStorage.profile
  omega

theorem pair_rate {model : RationalCostModel} {C d : ℕ} (hPrice : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hM : ∀ x,(o x).m=x.m)
    (hG : Small (fun x => (o x).classified.light.size)) (hR : Small (fun x => (o x).representatives))
    (hMass : Small (fun x => (o x).classified.lightWeight))
    (hGN : ∀ x,(o x).classified.light.size≤n x)
    (hHeavy : ∀ x,(o x).classified.heavy.size≤x.m) (hRep : ∀ x,(o x).representatives≤x.m)
    (hOwner : Soft (fun x => n x+1) (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x))) :
    Soft (rate n) (fun x => GeneralPaperCachedPairConstructionStorage.profile model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x)) :=
  GeneralPaperSourceSoftBounds.dominated (pair_majorant_rate C d W n o hW hn hM hG hR hMass hGN hHeavy hRep hOwner)
    (fun x => pair_model_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hPrice) (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x))

end Blotto.GeneralPaperCacheConstructionGrowth
