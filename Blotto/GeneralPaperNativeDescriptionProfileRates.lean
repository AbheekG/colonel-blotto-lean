import Blotto.GeneralPaperStrategyDescriptionProfileRates

/-! Native original-input reductions discharge the complete description
profile hypotheses, for either producer model and any value-pricing word.
The analysis word stays uniformly any proved logarithmic reference. -/
namespace Blotto.GeneralPaperNativeDescriptionProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem native_parameters (bits : Bool) (model : RationalCostModel) (U W n : Input → ℕ)
    (values : (x : Input) → FixedArrayTable (n x) ℚ) (v : (x : Input) → RationalFieldSelector (n x))
    (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
    (∀ x,(o x).m=x.m) →
    Small (fun x => (o x).classified.light.size) ∧ Small (fun x => (o x).representatives) ∧
    Small (fun x => (o x).classified.lightWeight) ∧ (∀ x,(o x).classified.light.size≤n x) ∧
    (∀ x,(o x).classified.heavy.size≤x.m) ∧
    (∀ x,(o x).replaced=true → (o x).representatives≤(o x).m) ∧
    Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x)) n := by
  dsimp only
  intro hM
  let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
  have hGN (x : Input) : (o x).classified.light.size≤n x :=
    GeneralPaperStrategyPreparationWork.light_size bits model (U x) x.k (values x)
  have hG : Small (fun x => (o x).classified.light.size) := GeneralPaperSourceWordGrowth.dominated hn hGN
  have hPow := pow_two _ k_tight
  have hR : Small (fun x => (o x).representatives) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 8*2^x.k) (by fun_prop)
    intro x
    dsimp only [o]
    rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]
  have hMass : Small (fun x => (o x).classified.lightWeight) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 257*n x*2^x.k) (by fun_prop)
    intro x
    exact (GeneralPaperNativeCircleLoss.original_mass_bound bits model (U x) x.k (values x)).trans
      (GeneralPaperOriginalValueReduction.denominator bits model (U x) x.k (values x) (v x) (hv x))
  have hBranch (x : Input) (he : (o x).replaced=true) : (o x).representatives≤(o x).m := by
    have h := (GeneralPaperNativeReductionShape.original_shape bits model (U x) x.k (values x) he).1
    change (o x).m=(o x).classified.heavy.size+(o x).representatives at h
    omega
  have hHeavy (x : Input) : (o x).classified.heavy.size≤x.m := by
    by_cases he:(o x).replaced=true
    · have h := (GeneralPaperNativeReductionShape.original_shape bits model (U x) x.k (values x) he).1
      change (o x).m=(o x).classified.heavy.size+(o x).representatives at h
      have hm := hM x
      change (o x).m=x.m at hm
      omega
    · have hFalse : (o x).replaced=false := by cases ht:(o x).replaced <;> simp_all
      have h := (GeneralPaperUnreplacedShape.original_shape bits model (U x) x.k (values x) hFalse).1
      have hh := GeneralPaperClosedArithmeticSampling.heavy_size bits model (U x) x.k (values x)
      change (o x).classified.heavy.size≤n x at hh
      change (o x).m=n x at h
      have hm := hM x
      change (o x).m=x.m at hm
      omega
  have hWP := poly_tight W hW
  have hUpper : Linear (fun x => 2048*(n x+1)*(W x+binaryWordWidth (n x)+x.k+1)) n := by fun_prop
  have hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (o x)) n :=
    GeneralPaperSourceSoftBounds.dominated hUpper (fun x =>
      GeneralPaperOriginalReductionRetainedStorage.original_linear bits model (U x) (W x) x.k (values x) (v x) (hv x))
  exact ⟨hG,hR,hMass,hGN,hHeavy,hBranch,hOwner⟩

theorem native_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (bits : Bool) (U W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) :
    let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
    (∀ x,(o x).m=x.m) →
    Soft (rate n) (fun x => GeneralPaperStrategyDescriptionConstructionStorage.profile model (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (o x)) (GeneralPaperProxyParameters.prepare (o x).m x.k).K
      (GeneralPaperSourcePairAnchorHeights.width (o x).m x.k) (o x)) := by
  dsimp only
  intro hM
  let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
  obtain ⟨hG,hR,hMass,hGN,hHeavy,hBranch,hOwner⟩ := native_parameters bits model U W n values v hv hW hn hM
  have h := GeneralPaperStrategyDescriptionProfileRates.profile_rate hg W n o hW hn hM hG hR hMass hGN hHeavy hBranch hOwner
  apply GeneralPaperSourceSoftBounds.dominated h
  intro x
  unfold GeneralPaperOriginalStrategyConstructionStorage.rows
  rw [hM x]

theorem native_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (bits : Bool) (U W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) :
    let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
    (∀ x,(o x).m=x.m) →
    Small (fun x => GeneralPaperStrategyDescriptionConstructionStorage.price model (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (o x))
      (GeneralPaperSourcePairAnchorHeights.width (o x).m x.k) (o x)) := by
  dsimp only
  intro hM
  let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
  obtain ⟨hG,hR,hMass,_,_,_,_⟩ := native_parameters bits model U W n values v hv hW hn hM
  have h := GeneralPaperStrategyDescriptionProfileRates.price_small hg W _ _ n o (of_tight hW)
    GeneralPaperNativeSourceWordGrowth.rows_small GeneralPaperSortedConstructionProfileRates.anchor_small hG hR hMass
  apply GeneralPaperSourceWordGrowth.dominated h
  intro x
  unfold GeneralPaperOriginalStrategyConstructionStorage.rows
  rw [hM x]
  exact le_rfl

theorem native_profile_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (bits : Bool) (U W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) :
    let o := fun x : Input => (GeneralPaperOriginalValueReduction.run bits model (U x) x.k (values x)).1
    (∀ x,(o x).m=x.m) →
    Small (fun x => GeneralPaperStrategyDescriptionConstructionStorage.profile model (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (o x)) (GeneralPaperProxyParameters.prepare (o x).m x.k).K
      (GeneralPaperSourcePairAnchorHeights.width (o x).m x.k) (o x)) := by
  dsimp only
  intro hM
  apply GeneralPaperSourceRowsStorageRates.soft_small (native_profile_rate hg bits U W n values v hv hW hn hM)
  unfold rate monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  have hPow := pow_two _ k_tight
  fun_prop

end Blotto.GeneralPaperNativeDescriptionProfileRates
