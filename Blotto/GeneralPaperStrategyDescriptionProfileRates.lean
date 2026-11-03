import Blotto.GeneralPaperSelectedCircleProfileRates

/-! Complete description-construction profiles preserve additive original
count and the sharp reduced-field cache rate. Prices below bound only native
work-field encodings; their coarse values are not promoted to sharp bit time. -/
namespace Blotto.GeneralPaperStrategyDescriptionProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperStrategyDescriptionConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W T H n : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Small W) (hT : Small T) (hH : Small H) (hG : Small (fun x => (o x).classified.light.size))
    (hR : Small (fun x => (o x).representatives)) (hMass : Small (fun x => (o x).classified.lightWeight)) :
    Small (fun x => price model (W x) (T x) (H x) (o x)) := by
  have hCoeffWidth : Small (fun x => GeneralPaperCircleRationalCoefficients.width (o x).representatives (o x).classified.lightWeight) := by
    unfold GeneralPaperCircleRationalCoefficients.width
    fun_prop
  have hArcWidth : Small (fun x => 1+binaryWordWidth (GeneralPaperSharedCacheConstructionStorage.magnitude
      (o x).representatives (o x).classified.lightWeight)) := by
    unfold GeneralPaperSharedCacheConstructionStorage.magnitude
    fun_prop
  have hCoeff := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hCoeffWidth
  have hArc := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hArcWidth
  have hSort := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg (fun x => 1+2*H x) (by fun_prop)
  unfold price GeneralPaperCachedPairConstructionStorage.price GeneralPaperSharedCacheConstructionStorage.originalPrice
    GeneralPaperSharedCacheConstructionStorage.price GeneralPaperCircleCoefficientConstructionStorage.price
    GeneralPaperCircleCoefficientConstructionStorage.callbackPrice GeneralPaperCircleArcConstructionStorage.price
    GeneralPaperCachedRowConstructionStorage.price GeneralPaperCachedRowConstructionStorage.rowPrice
    GeneralPaperSortedReferenceConstructionStorage.price GeneralPaperRepresentativeSortStorage.price
    GeneralPaperNativeRepresentativeSort.profile GeneralPaperPricedSort.profile GeneralPaperNativePayloadFillStorage.workCap
  fun_prop (config := {maxSteps := 4000})

theorem common_rate (W n g R mass : Input → ℕ) (hW : Tight W) (hR : Small R) (hMass : Small mass)
    (hgn : ∀ x,g x≤n x) : Linear (fun x => GeneralPaperCachedCircleRetainedStorage.commonProfile (W x) (g x) (R x) (mass x)) n := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hG : Linear g n := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by have := hgn x;omega)
  unfold GeneralPaperCachedCircleRetainedStorage.commonProfile arrayProfile natBits
  fun_prop (config := {maxSteps := 4000})

theorem layout_le (model : RationalCostModel) (W T m K H : ℕ) :
    2*GeneralPaperEnclosingSourceOwners.columnsProfile W T m K (1+2*H)+
      2*GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile W T m+128*W≤
    2*GeneralPaperCachedRowConstructionStorage.profile model W T 0 m K (1+2*H)+64*W := by
  have h := row_return_profile model W T 0 m K H
  unfold GeneralPaperCachedCircleRetainedStorage.rowsProfile at h
  simp only [Nat.zero_add] at h
  omega

theorem layout_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) :
    Rated (fun x => 2*GeneralPaperEnclosingSourceOwners.columnsProfile (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      x.m (GeneralPaperProxyParameters.prepare x.m x.k).K (1+2*GeneralPaperSourcePairAnchorHeights.width x.m x.k)+
      2*GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile (W x)
        (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows x.m+128*W x) 2 0 3 := by
  have hRows := GeneralPaperSortedConstructionProfileRates.native_profile hg W hW (fun _ => 0) Input.m
    (fun _ => Nat.zero_le _) (fun _ => le_rfl)
  have hWP : Rated W 0 0 0 := poly (poly_tight W hW)
  have hBound : Rated (fun x => 2*GeneralPaperCachedRowConstructionStorage.profile model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      0 x.m (GeneralPaperProxyParameters.prepare x.m x.k).K (1+2*GeneralPaperSourcePairAnchorHeights.width x.m x.k)+64*W x) 2 0 3 := by
    source_space
  exact GeneralPaperSourceSoftBounds.dominated hBound (fun x => layout_le model (W x) _ _ _ _)

theorem profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hM : ∀ x,(o x).m=x.m)
    (hG : Small (fun x => (o x).classified.light.size)) (hR : Small (fun x => (o x).representatives))
    (hMass : Small (fun x => (o x).classified.lightWeight)) (hGN : ∀ x,(o x).classified.light.size≤n x)
    (hHeavy : ∀ x,(o x).classified.heavy.size≤x.m)
    (hBranch : ∀ x,(o x).replaced=true → (o x).representatives≤(o x).m)
    (hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x)) n) :
    Soft (rate n) (fun x => profile model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x)) := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hm : Small (fun x => (o x).m) := GeneralPaperSourceWordGrowth.dominated m_small (fun x => by rw [hM x])
  have hPrice := price_small hg W _ _ n o hw GeneralPaperNativeSourceWordGrowth.rows_small
    GeneralPaperSortedConstructionProfileRates.anchor_small hG hR hMass
  have hTail : Polylog (fun x => 7*(natBits (cap model (W x)
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet x.m x.k).lambda x.k).rows
      (GeneralPaperProxyParameters.prepare x.m x.k).K (GeneralPaperSourcePairAnchorHeights.width x.m x.k) (o x))+W x)+160*W x) := by
    unfold cap natBits
    fun_prop (config := {maxSteps := 4000})
  have hOwner' := rate_mono hOwner (fun x => show n x+1≤rate n x by unfold rate;omega)
  have hCommon := rate_mono (common_rate W n (fun x => (o x).classified.light.size)
    (fun x => (o x).representatives) (fun x => (o x).classified.lightWeight) hW hR hMass hGN)
    (fun x => show n x+1≤rate n x by unfold rate;omega)
  have hLayout := rate_mono (layout_rate hg W hW) (fun x => show monomial 2 0 3 x≤rate n x by unfold rate;omega)
  have hChild := GeneralPaperSelectedCircleProfileRates.selected_rate hg W n o hW hn hM hG hR hMass hGN hHeavy hBranch hOwner
  have hTail' := poly_at_rate hTail (fun x => show 1≤rate n x by unfold rate;omega)
  have hSum := add_same (add_same (add_same (add_same (add_same hOwner' hLayout) hCommon) hLayout) hChild) hTail'
  apply GeneralPaperSourceSoftBounds.dominated hSum
  intro x
  unfold GeneralPaperStrategyDescriptionConstructionStorage.profile physicalProfile GeneralPaperClosedDescriptionStorage.descriptionProfile
  rw [hM x]
  omega

end Blotto.GeneralPaperStrategyDescriptionProfileRates
