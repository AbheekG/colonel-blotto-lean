import Blotto.GeneralPaperCachedPreparationScalarStorage
import Blotto.GeneralPaperRationalSourcePairData

/-! Enclosing cached bit-pair activation. Complete input/cache/Shared and
returned pair owners coexist with all prepared-pair cursors and both
actual scalar constructors. The native driver is used without replay. -/
namespace Blotto.GeneralPaperCachedBitPairStorage
open GeneralPaperProxyParameters GeneralPaperEncodedScalarStorage
open scoped BigOperators Classical
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

noncomputable def input (m k Qv : ℕ) (b : ℚ) : GeneralPaperCachedSourcePair.Input m k Qv (b:ℝ) :=
  ⟨GeneralPaperPrecallCachePrice.specification m k,alphabet m k,
    GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv,
    GeneralPaperProxyClassifier.classify m k (b:ℝ),rfl,rfl,rfl,rfl⟩

noncomputable def proxy (m k : ℕ) (b : ℚ) := (GeneralPaperProxyClassifier.classify m k (b:ℝ)).choice.proxy

noncomputable def decoded (model : RationalCostModel) (W m k : ℕ) (b : ℚ) :=
  GeneralPaperCachedBitSourcePair.decode model W (proxy m k b)

noncomputable def shared {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℚ) (reciprocal : Bool) :=
  GeneralPaperCachedSharedPreparation.fromCache model.rat W k (alphabet m k)
    (GeneralPaperMaterializedGridCache.specification m (alphabet m k).lambda k Qv) weights
    (if reciprocal then (decoded model W m k b).1 else 1) (if reciprocal then 1 else (decoded model W m k b).1)

noncomputable def run {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) :=
  GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hs (b:ℝ) (input m k Qv b)

theorem run_data {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) :
    run model W k Qv hQv weights hp hs b=
      ((GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b).1,
        (decoded model W m k b).2+(shared model W k Qv weights b false).2+(shared model W k Qv weights b true).2+
          (GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b).2+128*W) := by
  change ((GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b).1.map
    (GeneralPaperColumnPairReindex.run rfl rfl),_)=_
  rw [GeneralPaperColumnPairReindex.map_reflexive]
  rfl

theorem actual_input {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ)
    (x : GeneralPaperCachedSourcePair.Input m k Qv (b:ℝ)) :
    GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hs (b:ℝ) x=run model W k Qv hQv weights hp hs b :=
  congrArg (GeneralPaperCachedBitSourcePair.run model W k Qv hQv weights hp hs (b:ℝ))
    (GeneralPaperRationalSourcePairData.input_unique x (input m k Qv b))

noncomputable def precision (m k : ℕ) : ℕ := (GeneralPaperPowerPrecision.prepare (alphabet m k).lambda k).fractionalBits

noncomputable def price (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  GeneralPaperCachedPreparationScalarStorage.decodePrice model W (prepare m k).qbar+
    2*GeneralPaperCachedPreparationScalarStorage.sharedPrice model W k (precision m k) (alphabet m k)+
    GeneralPaperSourcePreparedPairOwners.price model C d W m k Qv+128*W

noncomputable def metadataCap (model : RationalCostModel) (C d W m k Qv : ℕ) : ℕ :=
  m+k+Qv+(GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows+(prepare m k).K+
    precision m k+W+price model C d W m k Qv+40

noncomputable def owners {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (weights : FixedArrayTable m ℕ) (b : ℚ) : ℕ :=
  rationalWordWidth b+GeneralPaperEncodedNatArray.footprint W weights+GeneralPaperSourcePreparedPairOwners.front W m k b+
    GeneralPaperMaterializedCacheStorage.gridFootprint W (input m k Qv b).grid+
    GeneralPaperEncodedSharedSource.footprint W (shared model W k Qv weights b false).1+
    GeneralPaperEncodedSharedSource.footprint W (shared model W k Qv weights b true).1

noncomputable def window {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) : ℕ :=
  let rho := decoded model W m k b
  let rich := shared model W k Qv weights b false
  let poor := shared model W k Qv weights b true
  let prepared := GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b
  let result := run model W k Qv hQv weights hp hs b
  let grid := (input m k Qv b).grid
  GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi+
    owners model W k Qv weights b+GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1+
    GeneralPaperCachedPreparationScalarStorage.decodeFrame model W (proxy m k b)+
    GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights 1 rho.1+
    GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights rho.1 1+
    fields W [m,k,Qv,W,rho.2,rich.2,poor.2,prepared.2,result.2,rho.2+rich.2,rho.2+rich.2+poor.2,
      rho.2+rich.2+poor.2+prepared.2,128*W,32*W,192*W,precision m k,k+precision m k+35,
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows]+192*W

noncomputable def profile (model : RationalCostModel) (C d W m k Qv B : ℕ) : ℕ :=
  3*GeneralPaperSourcePreparedPairOwners.profile model C d W m k Qv B+
    GeneralPaperCachedPreparationScalarStorage.decodeProfile model W (prepare m k).qbar+
    2*GeneralPaperCachedPreparationScalarStorage.sharedProfile model W k (precision m k) (alphabet m k)+
    18*(natBits (metadataCap model C d W m k Qv)+W)+224*W

theorem owners_retained {m : ℕ} (model : RationalCostModel) (W k Qv : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K) :
    owners model W k Qv weights b≤GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi := by
  have h := GeneralPaperSourcePreparedPairOwners.shared_inputs model W k Qv hQv weights hp hs b cursor hc outer ho inner hi
  change owners model W k Qv weights b+_≤_ at h
  omega

theorem bounded_of_prepared {m : ℕ} (model : RationalCostModel) (C d W k Qv B : ℕ) (hQv : 0<Qv)
    (weights : FixedArrayTable m ℕ) (hp : ∀ j,0<weights.read j) (hs : ∑ j,weights.read j=Qv) (b : ℚ) (hb : 0<b ∧ b<1)
    (cursor : ℕ) (hc : cursor≤m) (outer : ℕ) (ho : outer≤m) (inner : ℕ) (hi : inner≤(prepare m k).K)
    (hPrepared : GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤
        GeneralPaperSourcePreparedPairOwners.profile model C d W m k Qv B ∧
      (GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b).2≤
        GeneralPaperSourcePreparedPairOwners.price model C d W m k Qv) :
    window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi≤profile model C d W m k Qv B ∧
      (run model W k Qv hQv weights hp hs b).2≤price model C d W m k Qv := by
  let rho := decoded model W m k b
  let rich := shared model W k Qv weights b false
  let poor := shared model W k Qv weights b true
  let prepared := GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b
  let result := run model W k Qv hQv weights hp hs b
  let grid := (input m k Qv b).grid
  have hbReal : (0:ℝ)<b ∧ (b:ℝ)<1 := by exact_mod_cast hb
  have hRaw := GeneralPaperProxyClassifier.proxy_integer_representation m k (b:ℝ) hbReal
  change 0<(proxy m k b).num ∧ (proxy m k b).num<(proxy m k b).den ∧ (proxy m k b).den≤(prepare m k).qbar at hRaw
  have hDecode := GeneralPaperCachedPreparationScalarStorage.decode_bounded model W (prepare m k).qbar (proxy m k b)
    (le_trans (Nat.le_of_lt hRaw.2.1) hRaw.2.2) hRaw.2.2
  have hRich := GeneralPaperCachedPreparationScalarStorage.shared_bounded model W k (alphabet m k) grid weights 1 rho.1
  have hPoor := GeneralPaperCachedPreparationScalarStorage.shared_bounded model W k (alphabet m k) grid weights rho.1 1
  have hR : rich.2≤GeneralPaperCachedPreparationScalarStorage.sharedPrice model W k (precision m k) (alphabet m k) := hRich.2
  have hP : poor.2≤GeneralPaperCachedPreparationScalarStorage.sharedPrice model W k (precision m k) (alphabet m k) := hPoor.2
  have hD : rho.2≤GeneralPaperCachedPreparationScalarStorage.decodePrice model W (prepare m k).qbar := hDecode.2
  have hPW : prepared.2≤GeneralPaperSourcePreparedPairOwners.price model C d W m k Qv := hPrepared.2
  have hRichFrame : GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights 1 rho.1≤
    GeneralPaperCachedPreparationScalarStorage.sharedProfile model W k (precision m k) (alphabet m k) := hRich.1
  have hPoorFrame : GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights rho.1 1≤
    GeneralPaperCachedPreparationScalarStorage.sharedProfile model W k (precision m k) (alphabet m k) := hPoor.1
  have hWorkEq := congrArg Prod.snd (run_data model W k Qv hQv weights hp hs b)
  change result.2=rho.2+rich.2+poor.2+prepared.2+128*W at hWorkEq
  have hWork : result.2≤price model C d W m k Qv := by unfold price;omega
  have hOwners := (owners_retained model W k Qv hQv weights hp hs b cursor hc outer ho inner hi).trans hPrepared.1
  have hReturned : GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1≤
      GeneralPaperSourcePreparedPairOwners.profile model C d W m k Qv B := by
    have hData := congrArg Prod.fst (run_data model W k Qv hQv weights hp hs b)
    change result.1=prepared.1 at hData
    rw [hData]
    have hInside : GeneralPaperRetainedCompilerPairStorage.optionFoot W
        (GeneralPaperSourcePreparedPairOwners.run model W k Qv hQv weights hp hs b).1≤
        GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi := by
      dsimp only [GeneralPaperSourcePreparedPairOwners.window]
      omega
    exact hInside.trans hPrepared.1
  have hf := fields_bound W (natBits (metadataCap model C d W m k Qv))
    [m,k,Qv,W,rho.2,rich.2,poor.2,prepared.2,result.2,rho.2+rich.2,rho.2+rich.2+poor.2,
      rho.2+rich.2+poor.2+prepared.2,128*W,32*W,192*W,precision m k,k+precision m k+35,
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals
      unfold metadataCap price GeneralPaperCachedPreparationScalarStorage.sharedPrice GeneralPaperCachedPreparationScalarStorage.decodePrice at *
      omega)
  change fields W _≤18*(natBits (metadataCap model C d W m k Qv)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  dsimp only [window]
  change GeneralPaperSourcePreparedPairOwners.window model W k Qv hQv weights hp hs b cursor hc outer ho inner hi+
    owners model W k Qv weights b+GeneralPaperRetainedCompilerPairStorage.optionFoot W result.1+
    GeneralPaperCachedPreparationScalarStorage.decodeFrame model W (proxy m k b)+
    GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights 1 rho.1+
    GeneralPaperCachedPreparationScalarStorage.sharedFrame model W k (alphabet m k) grid weights rho.1 1+
    fields W [m,k,Qv,W,rho.2,rich.2,poor.2,prepared.2,result.2,rho.2+rich.2,rho.2+rich.2+poor.2,
      rho.2+rich.2+poor.2+prepared.2,128*W,32*W,192*W,precision m k,k+precision m k+35,
      (GeneralPaperTrajectoryParameters.prepare (alphabet m k).lambda k).rows]+192*W≤_
  unfold profile
  omega

end Blotto.GeneralPaperCachedBitPairStorage
