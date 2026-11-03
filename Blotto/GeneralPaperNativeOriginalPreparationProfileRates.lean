import Blotto.GeneralPaperNativeDescriptionProfileRates

/-! Native fixed-data preparation profiles, short second input and complete
retained original owners. Original precision remains additive. Coarse prices
are used only to bound work-field encodings. -/
namespace Blotto.GeneralPaperNativeOriginalPreparationProfileRates
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperNativePreparationReferenceContract (data)
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem fields (model : RationalCostModel) (n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    Small (fun x => (p x).reduced.denominator) ∧ Small (fun x => (p x).reduced.representatives) ∧
    Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) ∧
    Small (fun x => (p x).Qv) ∧ (∀ x,(p x).reduced.m≤n x) ∧
    (∀ x,(p x).reduced.classified.heavy.size≤n x) := by
  dsimp only
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  have hPow := pow_two _ k_tight
  have hM (x : Input) : (p x).reduced.m≤n x :=
    (GeneralPaperOriginalSourceValuePreparation.count_bounds false model 1 x.k (values x) (v x) (hv x)).2.1
  have hQ : Small (fun x => (p x).reduced.denominator) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 257*n x*2^x.k) (by fun_prop)
    intro x
    exact GeneralPaperOriginalValueReduction.denominator false model 1 x.k (values x) (v x) (hv x)
  have hR : Small (fun x => (p x).reduced.representatives) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 8*2^x.k) (by fun_prop)
    intro x
    change (GeneralPaperOriginalValueReduction.run false model 1 x.k (values x)).1.representatives≤_
    rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]
  have hQv : Small (fun x => (p x).Qv) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 513*n x*2^x.k) (by fun_prop)
    intro x
    have h := GeneralPaperOriginalSourceValuePreparation.denominator false model 1 x.k (values x) (v x) (hv x)
    have hm := hM x
    change (p x).Qv≤513*(p x).reduced.m*2^x.k at h
    exact h.trans (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 513 hm))
  have hSecond : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => n x*(512*(binaryWordWidth (n x)+x.k+1))) (by fun_prop)
    intro x
    have hw := GeneralPaperOriginalReductionRetainedStorage.original_words false model 1 x.k (values x) (v x) (hv x)
    have hs := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hw j)
    have hs' : GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values≤
        (p x).reduced.m*(512*(binaryWordWidth (n x)+x.k+1)) := by
      change GeneralPaperValueRoundingInputPrice.inputSize
        (GeneralPaperOriginalValueReduction.run false model 1 x.k (values x)).1.values≤
        (GeneralPaperOriginalValueReduction.run false model 1 x.k (values x)).1.m*(512*(binaryWordWidth (n x)+x.k+1))
      simpa only [GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,Fintype.card_fin,
        nsmul_eq_mul,Nat.cast_id] using hs
    exact hs'.trans (Nat.mul_le_mul_right _ (hM x))
  exact ⟨hQ,hR,hSecond,hQv,hM,fun x => GeneralPaperClosedArithmeticSampling.heavy_size false model 1 x.k (values x)⟩

theorem preparation_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    Small (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationPrice model (W x) x.k
      (GeneralPaperValueRoundingInputPrice.inputSize (values x)) (p x).reduced.denominator
      (GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) (p x).reduced) := by
  dsimp only
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  obtain ⟨hQ,hR,hSecond,_,hM,hHeavy⟩ := fields model n values v hv hn
  have hw := of_tight hW
  have hReduction := GeneralPaperOriginalSourcePreparationStorage.reduction_price_small hg W n
    (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)) (fun x => (p x).reduced.denominator)
    (fun x => (p x).reduced) hW hn hS hQ hR hHeavy
  have hm := GeneralPaperSourceWordGrowth.dominated hn hM
  have hSecondPrice := GeneralPaperOriginalSourcePreparationStorage.rounding_price_small hg W (fun _ => 512)
    (fun x => (p x).reduced.m) (fun x => GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values)
    hW (small_constant 512) hm hSecond
  unfold GeneralPaperOriginalSourcePreparationStorage.preparationPrice GeneralPaperOriginalSourcePreparationStorage.reference
    GeneralPaperReducedValuesConstructionStorage.reference GeneralPaperSummaryArrayExecution.arrayWord
  fun_prop (config := {maxSteps := 4000})

theorem preparation_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    Soft (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+n x+2^x.k+1)
      (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model (W x) x.k
        (GeneralPaperValueRoundingInputPrice.inputSize (values x)) (p x).reduced.denominator
        (GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) (p x).reduced) := by
  dsimp only
  have h := GeneralPaperOriginalSourcePreparationStorage.native_profile_rate hg W n values v hv hW hn hS
  apply GeneralPaperSourceSoftBounds.dominated h
  intro x
  unfold GeneralPaperOriginalSourcePreparationStorage.nativeProfile
  rw [GeneralPaperOriginalValueReduction.models_data model (W x) x.k (values x) (v x) (hv x)]
  exact le_rfl

theorem original_rate (model : RationalCostModel) (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    Linear (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced) n := by
  dsimp only
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  obtain ⟨_,_,_,hQv,hM,_⟩ := fields model n values v hv hn
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hm : Linear (fun x => (p x).reduced.m) n := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by
    have h := hM x
    change (p x).reduced.m≤n x at h
    omega)
  have hUpper : Linear (fun x => 2048*(n x+1)*(W x+binaryWordWidth (n x)+x.k+1)) n := by fun_prop
  have hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (W x) (p x).reduced) n :=
    GeneralPaperSourceSoftBounds.dominated hUpper (fun x =>
      GeneralPaperOriginalReductionRetainedStorage.original_linear false model 1 (W x) x.k (values x) (v x) (hv x))
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile arrayProfile natBits
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperNativeOriginalPreparationProfileRates
