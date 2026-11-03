import Blotto.GeneralPaperReducedValueArrayConstructionStorage

/-! Complete actual classifier/reduced-array caller. Native branch data
selects one constructor; all prefix peaks are erased maxima over literal
existing fills, with no runtime census or extra construction pass. -/
namespace Blotto.GeneralPaperReducedValuesConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperSummaryArrayExecution
open GeneralPaperReducedValueArrayConstructionStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def reference (W n R : ℕ) : ℕ := arrayWord W (2*n+R)
def selectedPrice {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  if o.replaced then replacedPrice model W n o.classified.heavy.size Q o.representatives else identityPrice model W n Q
def selectedProfile {n : ℕ} (model : RationalCostModel) (W Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  if o.replaced then replacedProfile model W n o.classified.heavy.size Q o.representatives else identityProfile model W n Q
def price {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperLightFieldScanConstructionStorage.classificationPrice model W n k Q+selectedPrice model W Q o+128*reference W n o.representatives
def cap {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+k+Q+o.representatives+price model W k Q o+128*reference W n o.representatives+1

theorem native_data {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    let c := (GeneralPaperLightFieldClassification.run true model W k Q weights).1
    let o := (GeneralPaperReducedValuesDriver.run true model W k Q weights).1
    o.classified=c.1 ∧ o.representatives=c.2 ∧ (o.replaced=true ↔ c.2<c.1.light.size) ∧ o.m≤n := by
  have hSizes := GeneralPaperReducedValuesPrice.sizes true model W k Q weights
  unfold GeneralPaperReducedValuesDriver.run
  dsimp only
  split_ifs with he
  · refine ⟨rfl,rfl,?_,?_⟩
    · constructor
      · intro _;exact he
      · intro _;rfl
    · change (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2≤n
      omega
  · refine ⟨rfl,rfl,?_,le_rfl⟩
    constructor
    · intro h;cases h
    · intro h;exact (he h).elim

theorem native_work {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    (GeneralPaperReducedValuesDriver.run true model W k Q weights).2≤
      price model W k Q (GeneralPaperReducedValuesDriver.run true model W k Q weights).1 := by
  have hw (j : Fin n) : weights.read j≤Q := by
    rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hClass := GeneralPaperLightFieldScanConstructionStorage.classification_work model W k Q weights hs
  have hSizes := GeneralPaperReducedValuesPrice.sizes true model W k Q weights
  have hL : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound true model W _ Q weights hs n le_rfl
  unfold GeneralPaperReducedValuesDriver.run
  dsimp only
  split_ifs
  · have ha := replaced_work model W Q (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight weights hw
      (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy hL
    have hA := GeneralPaperReducedValuesPrice.arrayWord_mono W
      (n+(GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.heavy.size+
        (GeneralPaperLightFieldClassification.run true model W k Q weights).1.2)
      (2*n+(GeneralPaperLightFieldClassification.run true model W k Q weights).1.2) (by omega)
    unfold price selectedPrice reference
    simp only [ite_true,GeneralPaperSourceRowsExecution.address]
    omega
  · have ha := identity_work model W Q weights hw
    have hA := GeneralPaperReducedValuesPrice.arrayWord_mono W (n+n)
      (2*n+(GeneralPaperLightFieldClassification.run true model W k Q weights).1.2) (by omega)
    unfold price selectedPrice reference
    simp only [Bool.false_eq_true,ite_false,GeneralPaperSourceRowsExecution.address,ite_true]
    omega

def selectedPeak {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : ℕ :=
  let c := (GeneralPaperLightFieldClassification.run true model W k Q weights).1
  if c.2<c.1.light.size then
    prefixPeak (c.1.heavy.size+c.2) (fun count hc => replacedWindow model W Q c.2 c.1.lightWeight weights c.1.heavy count hc)
  else prefixPeak n (fun count hc => identityWindow model W Q weights count hc)

theorem selected_bounded {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    selectedPeak model W k Q weights≤selectedProfile model W Q (GeneralPaperReducedValuesDriver.run true model W k Q weights).1 := by
  have hw (j : Fin n) : weights.read j≤Q := by
    rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hL : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound true model W _ Q weights hs n le_rfl
  unfold selectedPeak GeneralPaperReducedValuesDriver.run
  dsimp only
  split_ifs
  · unfold selectedProfile
    simp only [ite_true]
    apply prefix_peak_bound
    exact replaced_bounded model W Q _ _ weights hw _ hL
  · unfold selectedProfile
    simp only [Bool.false_eq_true,ite_false]
    apply prefix_peak_bound
    exact identity_bounded model W Q weights hw

def builtWork {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : ℕ :=
  let c := (GeneralPaperLightFieldClassification.run true model W k Q weights).1
  if c.2<c.1.light.size then (GeneralPaperReducedValueArray.replaced true model W Q c.2 c.1.lightWeight weights c.1.heavy).2
  else (GeneralPaperReducedValueArray.identity true model W Q weights).2
def overhead {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : ℕ :=
  let c := (GeneralPaperLightFieldClassification.run true model W k Q weights).1
  if c.2<c.1.light.size then 128*arrayWord W (n+c.1.heavy.size+c.2) else 128*arrayWord W (n+n)

theorem work_shape {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) :
    (GeneralPaperReducedValuesDriver.run true model W k Q weights).2=
      (GeneralPaperLightFieldClassification.run true model W k Q weights).2+builtWork model W k Q weights+overhead model W k Q weights := by
  unfold GeneralPaperReducedValuesDriver.run builtWork overhead
  dsimp only
  split_ifs <;> rfl

def controls {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : List ℕ :=
  let classified := GeneralPaperLightFieldClassification.run true model W k Q weights
  let o := GeneralPaperReducedValuesDriver.run true model W k Q weights
  [n,k,Q,classified.1.1.heavy.size,classified.1.1.light.size,classified.1.2,classified.1.1.lightWeight,o.1.m,
    classified.2,builtWork model W k Q weights,overhead model W k Q weights,
    classified.2+builtWork model W k Q weights,o.2]

def window {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ) : ℕ :=
  let o := (GeneralPaperReducedValuesDriver.run true model W k Q weights).1
  let A := reference W n o.representatives
  prefixPeak n (fun count hc => GeneralPaperLightFieldScanConstructionStorage.classificationWindow model W k Q weights count hc)+
    selectedPeak model W k Q weights+GeneralPaperOriginalReductionRetainedStorage.footprint A o+fields A (controls model W k Q weights)+128*A
def profile {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  let A := reference W n o.representatives
  GeneralPaperLightFieldScanConstructionStorage.classificationProfile model W n k Q+selectedProfile model W Q o+
    GeneralPaperOriginalReductionRetainedStorage.footprint A o+13*(natBits (cap model W k Q o)+A)+160*A

theorem bounded {n : ℕ} (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    window model W k Q weights≤profile model W k Q (GeneralPaperReducedValuesDriver.run true model W k Q weights).1 := by
  let o := (GeneralPaperReducedValuesDriver.run true model W k Q weights).1
  let A := reference W n o.representatives
  have hClass := prefix_peak_bound n _ (fun count hc => GeneralPaperLightFieldScanConstructionStorage.classificationWindow model W k Q weights count hc)
    (GeneralPaperLightFieldScanConstructionStorage.classification_bounded model W k Q weights hs)
  have hSelected := selected_bounded model W k Q weights hs
  have hw := native_work model W k Q weights hs
  have hShape := work_shape model W k Q weights
  have hData := native_data model W k Q weights
  have hSizes := GeneralPaperReducedValuesPrice.sizes true model W k Q weights
  have hL : (GeneralPaperLightFieldClassification.run true model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound true model W _ Q weights hs n le_rfl
  have hf := fields_bound A (natBits (cap model W k Q o)) (controls model W k Q weights) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    change (GeneralPaperReducedValuesDriver.run true model W k Q weights).2≤price model W k Q o at hw
    change o.classified=_ ∧ o.representatives=_ ∧ _ ∧ o.m≤n at hData
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [o,A] at * <;> omega)
  change fields A _≤13*(natBits (cap model W k Q o)+A)+32*A at hf
  unfold window profile
  change _≤GeneralPaperLightFieldScanConstructionStorage.classificationProfile model W n k Q+selectedProfile model W Q o+
    GeneralPaperOriginalReductionRetainedStorage.footprint A o+13*(natBits (cap model W k Q o)+A)+160*A
  dsimp only [o,A] at *
  omega

@[fun_prop]
theorem selected_price_scaling {n : ℕ} (model : RationalCostModel) (Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => selectedPrice model W Q o) := by
  unfold selectedPrice
  split_ifs
  · unfold replacedPrice coordinatePrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
    dsimp only [coordinatePrice]
    fun_prop
  · unfold identityPrice ratioPrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
    dsimp only
    fun_prop

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (k Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model W k Q o) := by
  have hc : GeneralPaperReferenceScaling.Scale (fun W =>
      GeneralPaperLightFieldScanConstructionStorage.classificationPrice model W n k Q) := by
    unfold GeneralPaperLightFieldScanConstructionStorage.classificationPrice GeneralPaperLightFieldScanConstructionStorage.price
      GeneralPaperNativeScaleConstructionStorage.price GeneralPaperOriginalSourceValuePrice.scalePrice arrayWord
    fun_prop
  unfold price reference
  fun_prop

@[fun_prop]
theorem selected_scaling {n : ℕ} (model : RationalCostModel) (Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => selectedProfile model W Q o) := by
  unfold selectedProfile
  split_ifs <;> fun_prop

@[fun_prop]
theorem profile_scaling {n : ℕ} (model : RationalCostModel) (k Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model W k Q o) := by
  unfold profile cap price selectedPrice reference arrayWord
    GeneralPaperLightFieldScanConstructionStorage.classificationPrice GeneralPaperLightFieldScanConstructionStorage.price
    replacedPrice identityPrice coordinatePrice ratioPrice GeneralPaperNativePayloadFillStorage.workCap
    GeneralPaperNativeScaleConstructionStorage.price GeneralPaperOriginalSourceValuePrice.scalePrice
  dsimp only [coordinatePrice,ratioPrice,GeneralPaperNativePayloadFillStorage.workCap]
  split_ifs <;> fun_prop (config := {maxSteps := 4000})

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem rate_amplify {r s f : Input → ℕ} (hf : Soft r f) (A : ℕ) (h : ∀ x,r x≤A*s x) : Soft s f := by
  rcases hf with ⟨B,e,hf⟩
  refine ⟨B*A,e,?_⟩
  intro x
  exact (hf x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left B (h x))).trans_eq (by ring))

theorem selected_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n Q : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hQ : Small Q) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x) :
    Soft (fun x => n x+(o x).representatives+1) (fun x => selectedProfile model (W x) (Q x) (o x)) := by
  have hh := GeneralPaperSourceWordGrowth.dominated hn hHeavy
  have hi := rate_mono (identity_rate hg W n Q hW hn hQ)
    (fun x => show n x+1≤n x+(o x).representatives+1 by omega)
  have hr := rate_amplify (replaced_rate hg W n (fun x => (o x).classified.heavy.size) Q
    (fun x => (o x).representatives) hW hn hh hQ hR) 2 (fun x => by
      change n x+(o x).classified.heavy.size+(o x).representatives+1≤2*(n x+(o x).representatives+1)
      have := hHeavy x
      omega)
  apply GeneralPaperSourceSoftBounds.dominated (add_same hi hr)
  intro x
  unfold selectedProfile
  split_ifs <;> omega

theorem price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n Q : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hQ : Small Q) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x) :
    Small (fun x => price model (W x) x.k (Q x) (o x)) := by
  have hw := of_tight hW
  have hh := GeneralPaperSourceWordGrowth.dominated hn hHeavy
  have hWidthI : Polylog (fun x => GeneralPaperReducedValueArrayPrice.width (Q x) 1) := by
    unfold GeneralPaperReducedValueArrayPrice.width;fun_prop
  have hWidthR : Polylog (fun x => GeneralPaperReducedValueArrayPrice.width (Q x) (o x).representatives) := by
    unfold GeneralPaperReducedValueArrayPrice.width;fun_prop
  have hRatI := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ (small_of_poly hWidthI)
  have hRatR := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ (small_of_poly hWidthR)
  have hi : Small (fun x => identityPrice model (W x) (n x) (Q x)) := by
    unfold identityPrice ratioPrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
    dsimp only
    fun_prop
  have hr : Small (fun x => replacedPrice model (W x) (n x) (o x).classified.heavy.size (Q x) (o x).representatives) := by
    unfold replacedPrice coordinatePrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
    dsimp only [coordinatePrice]
    fun_prop
  have hSelected : Small (fun x => selectedPrice model (W x) (Q x) (o x)) := by
    apply GeneralPaperSourceWordGrowth.dominated (small_add _ _ hi hr)
    intro x
    unfold selectedPrice
    split_ifs <;> omega
  have hPower := pow_two _ k_tight
  have hThreshold : Small (fun x => GeneralPaperLightFieldScanContract.multiplier x.k) := by
    unfold GeneralPaperLightFieldScanContract.multiplier;fun_prop
  have hPriceT := small_of_poly (GeneralPaperNativeScaleConstructionStorage.price_poly hg W (fun _ => 10) (fun _ => 1)
    hW (small_constant 10) (small_constant 1))
  have hPriceR := small_of_poly (GeneralPaperNativeScaleConstructionStorage.price_poly hg W (fun _ => 8) (fun _ => 1)
    hW (small_constant 8) (small_constant 1))
  have hOperand : Polylog (fun x => 1+binaryWordWidth (GeneralPaperLightFieldScanPrice.magnitude
      (GeneralPaperLightFieldScanContract.multiplier x.k) (Q x))) := by
    unfold GeneralPaperLightFieldScanPrice.magnitude;fun_prop
  have hRat := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ (small_of_poly hOperand)
  have hClass : Small (fun x => GeneralPaperLightFieldScanConstructionStorage.classificationPrice model (W x) (n x) x.k (Q x)) := by
    unfold GeneralPaperLightFieldScanConstructionStorage.classificationPrice GeneralPaperLightFieldScanConstructionStorage.price arrayWord
    fun_prop
  unfold price reference arrayWord
  fun_prop

theorem profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n Q : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hQ : Small Q) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x)
    (hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint
      (reference (W x) (n x) (o x).representatives) (o x)) n) :
    Soft (fun x => n x+(o x).representatives+1) (fun x => profile model (W x) x.k (Q x) (o x)) := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hPrice := price_small hg W n Q o hW hn hQ hR hHeavy
  have hClass := rate_mono (GeneralPaperLightFieldScanConstructionStorage.classification_profile_rate hg W n Q hW hn hQ)
    (fun x => show n x+1≤n x+(o x).representatives+1 by omega)
  have hSelected := selected_rate hg W n Q o hW hn hQ hR hHeavy
  have hOwner' := rate_mono hOwner (fun x => show n x+1≤n x+(o x).representatives+1 by omega)
  have hTail : Polylog (fun x => 13*(natBits (cap model (W x) x.k (Q x) (o x))+
      reference (W x) (n x) (o x).representatives)+160*reference (W x) (n x) (o x).representatives) := by
    unfold cap reference arrayWord natBits
    fun_prop (config := {maxSteps := 4000})
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤n x+(o x).representatives+1)
  have hAll := add_same (add_same (add_same hClass hSelected) hOwner') hTail'
  simpa only [profile,Nat.add_assoc] using hAll

end Blotto.GeneralPaperReducedValuesConstructionStorage
