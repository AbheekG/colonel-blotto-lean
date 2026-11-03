import Blotto.GeneralPaperNativeOriginalPreparationProfileRates

/-! Complete source/strategy profile growth with original input length and
accuracy encoding additive. Only already checked native phase profiles join;
coarse prices are used for the encoded work fields, not sharp bit time.
Native-family matching premises below are conditional algebra, not a final
uniform native-input theorem. The actual problem-domain transport is separate. -/
namespace Blotto.GeneralPaperOriginalStrategyProfileGrowth
open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperSourceRateAlgebra
open GeneralPaperCacheConstructionGrowth GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperNativePreparationReferenceContract (data)
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

def rate (n S E : Input → ℕ) (x : Input) : ℕ := n x+S x+E x+x.B+1+monomial 3 0 4 x

@[fun_prop]
def AtRate (f n S E : Input → ℕ) : Prop := Soft (rate n S E) f

@[fun_prop]
theorem at_poly (f n S E : Input → ℕ) (h : Polylog f) : AtRate f n S E :=
  poly_at_rate h (fun x => by unfold rate;omega)

@[fun_prop]
theorem at_constant (c : ℕ) (n S E : Input → ℕ) : AtRate (fun _ => c) n S E := at_poly _ _ _ _ (poly_constant c)

@[fun_prop]
theorem at_bits (f n S E : Input → ℕ) (hf : Small f) : AtRate (fun x => natBits (f x)) n S E := by
  apply at_poly
  unfold natBits
  fun_prop

@[fun_prop]
theorem at_add (f g n S E : Input → ℕ) (hf : AtRate f n S E) (hg : AtRate g n S E) : AtRate (fun x => f x+g x) n S E := add_same hf hg

@[fun_prop]
theorem at_mul_left (f g n S E : Input → ℕ) (hf : Polylog f) (hg : AtRate g n S E) : AtRate (fun x => f x*g x) n S E := poly_mul_rate hf hg

@[fun_prop]
theorem at_mul_right (f g n S E : Input → ℕ) (hf : AtRate f n S E) (hg : Polylog g) : AtRate (fun x => f x*g x) n S E := mul_poly hf hg

@[fun_prop]
theorem at_n (n S E : Input → ℕ) : AtRate n n S E := bounded 1 (fun x => by unfold rate;omega)

@[fun_prop]
theorem at_S (n S E : Input → ℕ) : AtRate S n S E := bounded 1 (fun x => by unfold rate;omega)

@[fun_prop]
theorem at_E (n S E : Input → ℕ) : AtRate E n S E := bounded 1 (fun x => by unfold rate;omega)

@[fun_prop]
theorem at_B (n S E : Input → ℕ) : AtRate Input.B n S E := bounded 1 (fun x => by unfold rate;omega)

theorem at_linear {f n S E : Input → ℕ} (h : Linear f n) : AtRate f n S E :=
  rate_mono h (fun x => by unfold rate;omega)

theorem at_description {f n S E : Input → ℕ} (h : Soft (GeneralPaperCacheConstructionGrowth.rate n) f) : AtRate f n S E := by
  apply rate_mono h
  intro x
  have hm := monomial_mono (by decide : 2≤3) (by decide : 0≤0) (by decide : 3≤4) x
  unfold GeneralPaperCacheConstructionGrowth.rate rate
  omega

theorem at_source {f n S E : Input → ℕ} (h : Soft GeneralPaperFastFrontStorageRates.rate f) : AtRate f n S E :=
  rate_mono h (fun x => by unfold GeneralPaperFastFrontStorageRates.rate rate;omega)

theorem rate_small (n S E : Input → ℕ) (hn : Small n) (hS : Small S) (hE : Small E) : Small (rate n S E) := by
  have hp := pow_two _ k_tight
  unfold rate monomial GeneralPaperNativeSourceRates.fields GeneralPaperNativeSourceRates.symbols GeneralPaperNativeSourceRates.accuracy
  fun_prop

theorem power_le (x : Input) : 2^x.k≤monomial 3 0 4 x := by
  have h := monomial_mono (by decide : 0≤3) (by decide : 0≤0) (by decide : 1≤4) x
  simpa only [monomial,pow_zero,pow_one,Nat.one_mul,GeneralPaperNativeSourceRates.accuracy] using h

theorem whole_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : Input → ℕ) (hW : Tight W) :
    Small (fun x => GeneralPaperFastWholeDriverStorage.price model C d (W x) x.m x.k x.Qv x.B) :=
  GeneralPaperSourceWordGrowth.dominated (GeneralPaperFastWholeDriverStorageRates.price_small C d W hW) (fun x =>
    GeneralPaperFastDriverSharpWork.price_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv x.B)

theorem source_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    Small (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.price model C d (W x) x.k
      (GeneralPaperValueRoundingInputPrice.inputSize (values x)) (p x).Qv x.B (p x).reduced) := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  have hPrep := GeneralPaperNativeOriginalPreparationProfileRates.preparation_price_small hg W n values v hv hW hn hS
  have hWhole : Small (fun x => GeneralPaperFastWholeDriverStorage.price model C d (W x) (p x).reduced.m x.k (p x).Qv x.B) := by
    apply GeneralPaperSourceWordGrowth.dominated (whole_price_small hg W hW)
    intro x
    rw [hM x,hQv x]
  have hw := of_tight hW
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.price
  fun_prop (config := {maxSteps := 4000})

theorem return_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile
      (W x) x.k (p x).Qv (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  have hOriginal : AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced) n S E :=
    at_linear (GeneralPaperNativeOriginalPreparationProfileRates.original_rate model W n values v hv hW hn)
  have hLayout := GeneralPaperStrategyDescriptionProfileRates.layout_rate hg W hW
  have hPhysical : Rated (fun x => GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced) (p x).reduced.m
      (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k)) 2 0 3 := by
    apply GeneralPaperSourceSoftBounds.dominated hLayout
    intro x
    unfold GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile GeneralPaperOriginalStrategyConstructionStorage.rows
    rw [hM x]
    omega
  have hPhysical' : AtRate (fun x => GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced) (p x).reduced.m
      (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k)) n S E := by
    apply rate_mono hPhysical
    intro x
    have hm := monomial_mono (by decide : 2≤3) (by decide : 0≤0) (by decide : 3≤4) x
    unfold rate
    omega
  have hWP := poly_tight W hW
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile
  change AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced+
    GeneralPaperStrategyDescriptionConstructionStorage.physicalProfile (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced) (p x).reduced.m
      (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k)+64*W x) n S E
  fun_prop (config := {maxSteps := 4000})

theorem source_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.profile model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  let S := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  have hw := of_tight hW
  have hWP := poly_tight W hW
  obtain ⟨_,_,_,hQSmall,hMN,_⟩ := GeneralPaperNativeOriginalPreparationProfileRates.fields model n values v hv hn
  have hm : Small (fun x => (p x).reduced.m) := GeneralPaperSourceWordGrowth.dominated hn hMN
  have hPrep : AtRate (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model (W x) x.k (S x)
      (p x).reduced.denominator (GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) (p x).reduced) n S E := by
    apply rate_mono (GeneralPaperNativeOriginalPreparationProfileRates.preparation_rate hg W n values v hv hW hn hS)
    intro x
    have hp := power_le x
    change S x+n x+2^x.k+1≤rate n S E x
    unfold rate
    omega
  have hWhole : AtRate (fun x => GeneralPaperFastWholeDriverStorage.profile model C d (W x) (p x).reduced.m x.k (p x).Qv x.B) n S E := by
    apply GeneralPaperSourceSoftBounds.dominated (at_source (GeneralPaperFastWholeDriverStorageRates.profile_rate C d W hW))
    intro x
    rw [hM x,hQv x]
    exact GeneralPaperFastWholeDriverStorageRates.profile_model_mono model (GeneralPaperFastRationalMajorant.model C d)
      (GeneralPaperFastRationalMajorant.dominates hg) C d (W x) x.m x.k x.Qv x.B
  have hOriginal : AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced) n S E :=
    at_linear (GeneralPaperNativeOriginalPreparationProfileRates.original_rate model W n values v hv hW hn)
  have hReturn := return_rate hg W n S E values v hv hW hn hM
  have hPrice := source_price_small hg W n values v hv hW hn hS hM hQv
  have hCap : Small (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.cap model C d (W x)
      x.k (S x) (p x).Qv x.B (p x).reduced) := by
    unfold GeneralPaperOriginalSourceDriverConstructionStorage.cap
    fun_prop (config := {maxSteps := 4000})
  have hInput : AtRate S n S E := at_S n S E
  have hCount : AtRate n n S E := at_n n S E
  have hBudget : AtRate Input.B n S E := at_B n S E
  unfold GeneralPaperOriginalSourceDriverConstructionStorage.profile
  change AtRate (fun x => GeneralPaperOriginalSourcePreparationStorage.preparationProfile model (W x) x.k (S x)
      (p x).reduced.denominator (GeneralPaperValueRoundingInputPrice.inputSize (p x).reduced.values) (p x).reduced+
    GeneralPaperFastWholeDriverStorage.profile model C d (W x) (p x).reduced.m x.k (p x).Qv x.B+
    (S x+n x*W x+64*W x)+(1+2*x.B)+GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced+
    GeneralPaperOriginalSourceDriverConstructionStorage.returnProfile (W x) x.k (p x).Qv
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced+
    10*(natBits (GeneralPaperOriginalSourceDriverConstructionStorage.cap model C d (W x) x.k (S x) (p x).Qv x.B (p x).reduced)+W x)+288*W x) n S E
  fun_prop (config := {maxSteps := 4000})

theorem description_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → AtRate (fun x => GeneralPaperStrategyDescriptionConstructionStorage.profile model (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced) (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM
  exact at_description (GeneralPaperNativeDescriptionProfileRates.native_profile_rate hg false (fun _ => 1) W n values v hv hW hn hM)

theorem attach_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → Small (fun x => GeneralPaperOriginalStrategyConstructionStorage.attachPrice model (W x) x.k
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
  dsimp only
  intro hM
  have h := GeneralPaperNativeDescriptionProfileRates.native_price_small hg false (fun _ => 1) W n values v hv hW hn hM
  have hw := of_tight hW
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachPrice
  fun_prop

theorem prepared_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → AtRate (fun x => GeneralPaperOriginalStrategyConstructionStorage.preparedProfile (W x) x.k
      (p x).Qv (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  have hOriginal : AtRate (fun x => GeneralPaperOriginalSourceDriverConstructionStorage.originalProfile (W x) (p x).Qv (p x).reduced) n S E :=
    at_linear (GeneralPaperNativeOriginalPreparationProfileRates.original_rate model W n values v hv hW hn)
  have hDescription : AtRate (fun x => GeneralPaperClosedDescriptionStorage.descriptionProfile (W x)
      (GeneralPaperOriginalStrategyConstructionStorage.rows x.k (p x).reduced)
      (GeneralPaperProxyParameters.prepare (p x).reduced.m x.k).K
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
    apply GeneralPaperSourceSoftBounds.dominated (description_rate hg W n S E values v hv hW hn hM)
    intro x
    unfold GeneralPaperStrategyDescriptionConstructionStorage.profile
    dsimp only [p]
    omega
  have hWP := poly_tight W hW
  unfold GeneralPaperOriginalStrategyConstructionStorage.preparedProfile
  fun_prop

theorem attach_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j) (hW : Tight W) (hn : Small n) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → AtRate (fun x => GeneralPaperOriginalStrategyConstructionStorage.attachProfile model (W x) x.k
      (p x).Qv (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hSource := return_rate hg W n S E values v hv hW hn hM
  have hDescription := description_rate hg W n S E values v hv hW hn hM
  have hPrepared := prepared_rate hg W n S E values v hv hW hn hM
  have hPrice := attach_price_small hg W n values v hv hW hn hM
  have hCap : Small (fun x => GeneralPaperOriginalStrategyConstructionStorage.attachCap model (W x) x.k
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.attachCap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.attachProfile
  fun_prop (config := {maxSteps := 4000})

theorem strategy_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    Small (fun x => GeneralPaperOriginalStrategyConstructionStorage.price model C d (W x) x.k
      (GeneralPaperValueRoundingInputPrice.inputSize (values x)) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
  dsimp only
  intro hM hQv
  have hSource := source_price_small hg W n values v hv hW hn hS hM hQv
  have hAttach := attach_price_small hg W n values v hv hW hn hM
  have hw := of_tight hW
  unfold GeneralPaperOriginalStrategyConstructionStorage.price
  fun_prop

theorem strategy_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n E : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    let p := fun x : Input => data model x.k (values x) (v x) (hv x)
    let S := fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)
    (∀ x,(p x).reduced.m=x.m) → (∀ x,(p x).Qv=x.Qv) →
    AtRate (fun x => GeneralPaperOriginalStrategyConstructionStorage.profile model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) n S E := by
  dsimp only
  intro hM hQv
  let p := fun x : Input => data model x.k (values x) (v x) (hv x)
  let S := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (values x)
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hSource := source_rate hg W n E values v hv hW hn hS hM hQv
  have hAttach := attach_rate hg W n S E values v hv hW hn hM
  have hPrice := strategy_price_small hg W n values v hv hW hn hS hM hQv
  have hCap : Small (fun x => GeneralPaperOriginalStrategyConstructionStorage.cap model C d (W x) x.k (S x) (p x).Qv x.B
      (GeneralPaperSourcePairAnchorHeights.width (p x).reduced.m x.k) (p x).reduced) := by
    unfold GeneralPaperOriginalStrategyConstructionStorage.cap
    fun_prop
  unfold GeneralPaperOriginalStrategyConstructionStorage.profile
  fun_prop (config := {maxSteps := 4000})

end Blotto.GeneralPaperOriginalStrategyProfileGrowth
