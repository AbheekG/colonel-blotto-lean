import Blotto.GeneralPaperReducedValuesConstructionStorage

/-! Join the actual first value-rounding, classifier/reduction and second
value-rounding construction windows. All original and returned owners stay
visible. Prefix suprema are erased analysis of the existing fills; no extra
runtime traversal, size computation or discarded branch is executed. -/
namespace Blotto.GeneralPaperOriginalSourcePreparationStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperSummaryArrayExecution
open GeneralPaperReducedValueArrayConstructionStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 16000000
set_option maxRecDepth 16384

def reference {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperReducedValuesConstructionStorage.reference W n o.representatives

def reductionPrice {n : ℕ} (model : RationalCostModel) (W k S Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperNativeScaleConstructionStorage.roundingPrice model W 256 n k S+
    GeneralPaperReducedValuesConstructionStorage.price model W k Q o+128*reference W o

def reductionCap {n : ℕ} (model : RationalCostModel) (W k S Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+k+S+Q+o.representatives+reductionPrice model W k S Q o+128*reference W o+1

def reductionControls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) : List ℕ :=
  let first := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let reduced := GeneralPaperReducedValuesDriver.run true model W k first.1.2 first.1.1
  [n,k,first.1.2,reduced.1.m,first.2,reduced.2,128*arrayWord W (n+reduced.1.m),first.2+reduced.2,
    (GeneralPaperOriginalValueReduction.run true model W k values).2]

def reductionWindow {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  let first := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
  prefixPeak n (fun count hc => GeneralPaperNativeScaleConstructionStorage.roundingWindow model W 256 k values count hc)+
    GeneralPaperReducedValuesConstructionStorage.window model W k first.1.2 first.1.1+
    fields (reference W o) (reductionControls model W k values)+128*reference W o

def reductionProfile {n : ℕ} (model : RationalCostModel) (W k S Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperNativeScaleConstructionStorage.roundingProfile model W 256 n k S+
    GeneralPaperReducedValuesConstructionStorage.profile model W k Q o+
    9*(natBits (reductionCap model W k S Q o)+reference W o)+160*reference W o

theorem reduction_work {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    (GeneralPaperOriginalValueReduction.run true model W k values).2≤
      reductionPrice model W k (GeneralPaperValueRoundingInputPrice.inputSize values)
        (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
        (GeneralPaperOriginalValueReduction.run true model W k values).1 := by
  have hf := GeneralPaperNativeScaleConstructionStorage.rounding_work model W 256 k values v hv
  have hr := GeneralPaperReducedValuesConstructionStorage.native_work model W k
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.1
    (GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values)
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  have ha := GeneralPaperReducedValuesPrice.arrayWord_mono W
    (n+(GeneralPaperOriginalValueReduction.run true model W k values).1.m)
    (2*n+(GeneralPaperOriginalValueReduction.run true model W k values).1.representatives) (by omega)
  unfold reductionPrice reference GeneralPaperReducedValuesConstructionStorage.reference
  change _≤GeneralPaperNativeScaleConstructionStorage.roundingPrice model W 256 n k _+
    GeneralPaperReducedValuesConstructionStorage.price model W k _ _+128*arrayWord W _
  unfold GeneralPaperOriginalValueReduction.run
  simp only [GeneralPaperSourceRowsExecution.address,ite_true,GeneralPaperOriginalValueReduction.data] at *
  omega

theorem reduction_bounded {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    reductionWindow model W k values≤
      reductionProfile model W k (GeneralPaperValueRoundingInputPrice.inputSize values)
        (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
        (GeneralPaperOriginalValueReduction.run true model W k values).1 := by
  let first := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let A := reference W o
  have hf : prefixPeak n (fun count hc => GeneralPaperNativeScaleConstructionStorage.roundingWindow model W 256 k values count hc)≤
      GeneralPaperNativeScaleConstructionStorage.roundingProfile model W 256 n k S :=
    prefix_peak_bound n _ _ (GeneralPaperNativeScaleConstructionStorage.rounding_bounded model W 256 k values v hv)
  have hr := GeneralPaperReducedValuesConstructionStorage.bounded model W k first.1.2 first.1.1
    (GeneralPaperValueRoundingPaperContract.source_sum true model W 256 k values)
  have hw := reduction_work model W k values v hv
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  have hShape : (GeneralPaperOriginalValueReduction.run true model W k values).2=first.2+
      (GeneralPaperReducedValuesDriver.run true model W k first.1.2 first.1.1).2+128*arrayWord W (n+o.m) := rfl
  have hFields := fields_bound A (natBits (reductionCap model W k S first.1.2 o)) (reductionControls model W k values) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [reductionControls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold reductionCap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [first,o,S,A] at * <;>
      simp only [GeneralPaperOriginalValueReduction.data] at * <;> omega)
  change fields A _≤9*(natBits (reductionCap model W k S first.1.2 o)+A)+32*A at hFields
  unfold reductionWindow reductionProfile
  dsimp only [first,o,S,A] at *
  simp only [GeneralPaperOriginalValueReduction.data] at *
  omega

def preparationPrice {n : ℕ} (model : RationalCostModel) (W k S Q S₂ : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  reductionPrice model W k S Q o+GeneralPaperNativeScaleConstructionStorage.roundingPrice model W 512 o.m k S₂+128*reference W o

def preparationCap {n : ℕ} (model : RationalCostModel) (W k S Q S₂ : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+k+S+Q+S₂+o.m+o.representatives+513*n*2^k+preparationPrice model W k S Q S₂ o+128*reference W o+1

def preparationControls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) : List ℕ :=
  let reduced := GeneralPaperOriginalValueReduction.run true model W k values
  let rounded := GeneralPaperValueRoundingPaperContract.run true model W 512 k reduced.1.values
  [n,k,reduced.1.m,rounded.1.2,reduced.2,rounded.2,128*arrayWord W (n+reduced.1.m),reduced.2+rounded.2,
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2]

def preparationWindow {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) : ℕ :=
  let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
  reductionWindow model W k values+
    prefixPeak o.m (fun count hc => GeneralPaperNativeScaleConstructionStorage.roundingWindow model W 512 k o.values count hc)+
    fields (reference W o) (preparationControls model W k values v hv)+128*reference W o

def preparationProfile {n : ℕ} (model : RationalCostModel) (W k S Q S₂ : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  reductionProfile model W k S Q o+GeneralPaperNativeScaleConstructionStorage.roundingProfile model W 512 o.m k S₂+
    9*(natBits (preparationCap model W k S Q S₂ o)+reference W o)+160*reference W o

theorem preparation_work {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
    (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2≤
      preparationPrice model W k (GeneralPaperValueRoundingInputPrice.inputSize values)
        (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
        (GeneralPaperValueRoundingInputPrice.inputSize o.values) o := by
  dsimp only
  have hr := reduction_work model W k values v hv
  have hs := GeneralPaperNativeScaleConstructionStorage.rounding_work model W 512 k
    (GeneralPaperOriginalValueReduction.run true model W k values).1.values
    (GeneralPaperOriginalValueReduction.selector true model W k values v hv) (fun _ => rfl)
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  have ha := GeneralPaperReducedValuesPrice.arrayWord_mono W
    (n+(GeneralPaperOriginalValueReduction.run true model W k values).1.m)
    (2*n+(GeneralPaperOriginalValueReduction.run true model W k values).1.representatives) (by omega)
  unfold preparationPrice reference GeneralPaperReducedValuesConstructionStorage.reference GeneralPaperOriginalSourceValuePreparation.run
  simp only [GeneralPaperSourceRowsExecution.address,ite_true]
  omega

theorem preparation_bounded {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
    preparationWindow model W k values v hv≤
      preparationProfile model W k (GeneralPaperValueRoundingInputPrice.inputSize values)
        (GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2
        (GeneralPaperValueRoundingInputPrice.inputSize o.values) o := by
  let first := GeneralPaperValueRoundingPaperContract.run true model W 256 k values
  let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let S₂ := GeneralPaperValueRoundingInputPrice.inputSize o.values
  let A := reference W o
  have hr := reduction_bounded model W k values v hv
  have hs : prefixPeak o.m (fun count hc => GeneralPaperNativeScaleConstructionStorage.roundingWindow model W 512 k o.values count hc)≤
      GeneralPaperNativeScaleConstructionStorage.roundingProfile model W 512 o.m k S₂ :=
    prefix_peak_bound o.m _ _ (GeneralPaperNativeScaleConstructionStorage.rounding_bounded model W 512 k o.values
      (GeneralPaperOriginalValueReduction.selector true model W k values v hv) (fun _ => rfl))
  have hw := preparation_work model W k values v hv
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model W k values v hv).2.1
  have hQ := GeneralPaperOriginalSourceValuePreparation.denominator true model W k values v hv
  change (GeneralPaperValueRoundingPaperContract.run true model W 512 k o.values).1.2≤513*o.m*2^k at hQ
  have hQ' := Nat.mul_le_mul_right (2^k) (Nat.mul_le_mul_left 513 hm)
  have hShape : (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).2=
      (GeneralPaperOriginalValueReduction.run true model W k values).2+
      (GeneralPaperValueRoundingPaperContract.run true model W 512 k o.values).2+128*arrayWord W (n+o.m) := rfl
  have hFields := fields_bound A (natBits (preparationCap model W k S first.1.2 S₂ o))
    (preparationControls model W k values v hv) (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [preparationControls,List.mem_cons,List.not_mem_nil,or_false] at hz
      unfold preparationCap
      rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [first,o,S,S₂,A] at * <;> omega)
  change fields A _≤9*(natBits (preparationCap model W k S first.1.2 S₂ o)+A)+32*A at hFields
  unfold preparationWindow preparationProfile
  dsimp only [first,o,S,S₂,A] at *
  omega

@[fun_prop]
theorem rounding_price_scaling (model : RationalCostModel) (c n k S : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperNativeScaleConstructionStorage.roundingPrice model W c n k S) := by
  unfold GeneralPaperNativeScaleConstructionStorage.roundingPrice GeneralPaperNativeScaleConstructionStorage.price
    GeneralPaperOriginalSourceValuePrice.scalePrice GeneralPaperValueWeightSumConstructionStorage.driverPrice
    GeneralPaperValueWeightSumConstructionStorage.price GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice
    GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
  dsimp only
  fun_prop

@[fun_prop]
theorem reduction_price_scaling {n : ℕ} (model : RationalCostModel) (k S Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => reductionPrice model W k S Q o) := by
  unfold reductionPrice reference GeneralPaperReducedValuesConstructionStorage.reference
  fun_prop

@[fun_prop]
theorem reduction_scaling {n : ℕ} (model : RationalCostModel) (k S Q : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => reductionProfile model W k S Q o) := by
  unfold reductionProfile reductionCap reference GeneralPaperReducedValuesConstructionStorage.reference
  fun_prop

@[fun_prop]
theorem preparation_scaling {n : ℕ} (model : RationalCostModel) (k S Q S₂ : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => preparationProfile model W k S Q S₂ o) := by
  unfold preparationProfile preparationCap preparationPrice reference GeneralPaperReducedValuesConstructionStorage.reference
  fun_prop

open GeneralPaperSourceWordGrowth GeneralPaperSourceSoftBounds GeneralPaperCacheConstructionGrowth

theorem rate_substitute {r s f : Input → ℕ} (hf : Soft r f) (hr : Soft s r) : Soft s f := by
  rcases hf with ⟨A,e,hf⟩
  rcases hr with ⟨B,d,hr⟩
  refine ⟨A*B,d+e,?_⟩
  intro x
  exact (hf x).trans ((Nat.mul_le_mul_right _ (Nat.mul_le_mul_left A (hr x))).trans_eq (by rw [pow_add];ring))

theorem rounding_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W c n S : Input → ℕ) (hW : Tight W) (hc : Small c) (hn : Small n) (hS : Small S) :
    Small (fun x => GeneralPaperNativeScaleConstructionStorage.roundingPrice model (W x) (c x) (n x) x.k (S x)) := by
  have hw := of_tight hW
  have hPow := pow_two _ k_tight
  have hM : Small (fun x => GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k) := by
    unfold GeneralPaperValueRoundingPaperContract.scale;fun_prop
  have hLong : Small (fun x => GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth
      (GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k) (S x)) := by
    unfold GeneralPaperOriginalValueRoundConstructionStorage.aggregateWidth;fun_prop
  have hLongRat := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hLong
  have hShort : Small (fun x => 1+binaryWordWidth (GeneralPaperValueRoundingPaperContract.scale (c x) (n x) x.k+n x)) := by
    fun_prop
  have hShortRat := GeneralPaperValueWeightSumConstructionStorage.primitive_small hg _ hShort
  have hScale := small_of_poly (GeneralPaperNativeScaleConstructionStorage.price_poly hg W c n hW hc hn)
  unfold GeneralPaperNativeScaleConstructionStorage.roundingPrice GeneralPaperValueWeightSumConstructionStorage.driverPrice
    GeneralPaperValueWeightSumConstructionStorage.price GeneralPaperOriginalValueRoundConstructionStorage.callbackPrice
    GeneralPaperOriginalValueRoundConstructionStorage.scalarPrice GeneralPaperNativePayloadFillStorage.workCap arrayWord
  dsimp only
  fun_prop (config := {maxSteps := 4000})

theorem reduction_price_small {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S Q : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hS : Small S) (hQ : Small Q) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x) :
    Small (fun x => reductionPrice model (W x) x.k (S x) (Q x) (o x)) := by
  have hw := of_tight hW
  have hFirst := rounding_price_small hg W (fun _ => 256) n S hW (small_constant 256) hn hS
  have hReduced := GeneralPaperReducedValuesConstructionStorage.price_small hg W n Q o hW hn hQ hR hHeavy
  unfold reductionPrice reference GeneralPaperReducedValuesConstructionStorage.reference arrayWord
  fun_prop

theorem reduction_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S Q : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hS : Small S) (hQ : Small Q) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x)
    (hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (reference (W x) (o x)) (o x)) n) :
    Soft (fun x => S x+n x+(o x).representatives+1) (fun x => reductionProfile model (W x) x.k (S x) (Q x) (o x)) := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hPrice := reduction_price_small hg W n S Q o hW hn hS hQ hR hHeavy
  have hFirst := rate_mono (GeneralPaperNativeScaleConstructionStorage.rounding_profile_rate hg W (fun _ => 256) n S
    hW (small_constant 256) hn hS) (fun x => show S x+n x+1≤S x+n x+(o x).representatives+1 by omega)
  have hReduced := rate_mono (GeneralPaperReducedValuesConstructionStorage.profile_rate hg W n Q o hW hn hQ hR hHeavy hOwner)
    (fun x => show n x+(o x).representatives+1≤S x+n x+(o x).representatives+1 by omega)
  have hTail : Polylog (fun x => 9*(natBits (reductionCap model (W x) x.k (S x) (Q x) (o x))+
      reference (W x) (o x))+160*reference (W x) (o x)) := by
    unfold reductionCap reference GeneralPaperReducedValuesConstructionStorage.reference arrayWord natBits
    fun_prop (config := {maxSteps := 4000})
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤S x+n x+(o x).representatives+1)
  simpa only [reductionProfile,Nat.add_assoc] using add_same (add_same hFirst hReduced) hTail'

theorem preparation_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n S Q S₂ : Input → ℕ) (o : (x : Input) → GeneralPaperReducedValuesDriver.Output (n x))
    (hW : Tight W) (hn : Small n) (hS : Small S) (hQ : Small Q) (hS₂ : Small S₂)
    (hS₂Rate : Linear S₂ n) (hM : ∀ x,(o x).m≤n x) (hR : Small (fun x => (o x).representatives))
    (hHeavy : ∀ x,(o x).classified.heavy.size≤n x)
    (hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (reference (W x) (o x)) (o x)) n) :
    Soft (fun x => S x+n x+(o x).representatives+1) (fun x => preparationProfile model (W x) x.k (S x) (Q x) (S₂ x) (o x)) := by
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hm := GeneralPaperSourceWordGrowth.dominated hn hM
  have hPow := pow_two _ k_tight
  have hReduction := reduction_profile_rate hg W n S Q o hW hn hS hQ hR hHeavy hOwner
  have hPriceR := reduction_price_small hg W n S Q o hW hn hS hQ hR hHeavy
  have hPrice₂ := rounding_price_small hg W (fun _ => 512) (fun x => (o x).m) S₂ hW (small_constant 512) hm hS₂
  have hSecond := GeneralPaperNativeScaleConstructionStorage.rounding_profile_rate hg W (fun _ => 512) (fun x => (o x).m) S₂
    hW (small_constant 512) hm hS₂
  have hMRate : Linear (fun x => (o x).m) n := GeneralPaperSourceSoftBounds.bounded 1 (fun x => by have := hM x;omega)
  have hSecondRate := rate_substitute hSecond (add_same (add_same hS₂Rate hMRate) (linear_constant 1 n))
  have hSecond' := rate_mono hSecondRate (fun x => show n x+1≤S x+n x+(o x).representatives+1 by omega)
  have hTail : Polylog (fun x => 9*(natBits (preparationCap model (W x) x.k (S x) (Q x) (S₂ x) (o x))+
      reference (W x) (o x))+160*reference (W x) (o x)) := by
    unfold preparationCap preparationPrice reference GeneralPaperReducedValuesConstructionStorage.reference arrayWord natBits
    fun_prop (config := {maxSteps := 4000})
  have hTail' := poly_at_rate hTail (fun x => by omega : ∀ x,1≤S x+n x+(o x).representatives+1)
  simpa only [preparationProfile,Nat.add_assoc] using add_same (add_same hReduction hSecond') hTail'

def nativeProfile {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ) : ℕ :=
  let o := (GeneralPaperOriginalValueReduction.run true model W k values).1
  preparationProfile model W k (GeneralPaperValueRoundingInputPrice.inputSize values) o.denominator
    (GeneralPaperValueRoundingInputPrice.inputSize o.values) o

theorem native_bounded {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    preparationWindow model W k values v hv≤nativeProfile model W k values := by
  unfold nativeProfile
  dsimp only
  rw [(GeneralPaperOriginalValueReduction.retained true model W k values).2]
  exact preparation_bounded model W k values v hv

theorem native_profile_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    Soft (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+n x+2^x.k+1)
      (fun x => nativeProfile model (W x) x.k (values x)) := by
  let o := fun x : Input => (GeneralPaperOriginalValueReduction.run true model (W x) x.k (values x)).1
  let S₂ := fun x : Input => GeneralPaperValueRoundingInputPrice.inputSize (o x).values
  have hw := of_tight hW
  have hWP := poly_tight W hW
  have hPower := pow_two _ k_tight
  have hR : Small (fun x => (o x).representatives) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 8*2^x.k) (by fun_prop)
    intro x
    dsimp only [o]
    rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]
  have hQ : Small (fun x => (o x).denominator) := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => 257*n x*2^x.k) (by fun_prop)
    intro x
    exact GeneralPaperOriginalValueReduction.denominator true model (W x) x.k (values x) (v x) (hv x)
  have hM (x : Input) : (o x).m≤n x :=
    (GeneralPaperOriginalValueReduction.count_bounds true model (W x) x.k (values x) (v x) (hv x)).2.1
  have hHeavy (x : Input) : (o x).classified.heavy.size≤n x :=
    GeneralPaperClosedArithmeticSampling.heavy_size true model (W x) x.k (values x)
  have hWidth : Polylog (fun x => 512*(binaryWordWidth (n x)+x.k+1)) := by fun_prop
  have hWidthSmall := small_of_poly hWidth
  have hS₂Bound (x : Input) : S₂ x≤n x*(512*(binaryWordWidth (n x)+x.k+1)) := by
    have hWords := GeneralPaperOriginalReductionRetainedStorage.original_words true model (W x) x.k (values x) (v x) (hv x)
    have hSum := Finset.sum_le_sum (s:=Finset.univ) (fun j _ => hWords j)
    have hSize : S₂ x≤(o x).m*(512*(binaryWordWidth (n x)+x.k+1)) := by
      simpa only [S₂,GeneralPaperValueRoundingInputPrice.inputSize,Finset.sum_const,Finset.card_univ,
        Fintype.card_fin,nsmul_eq_mul,Nat.cast_id] using hSum
    exact hSize.trans (Nat.mul_le_mul_right _ (hM x))
  have hS₂ : Small S₂ := by
    apply GeneralPaperSourceWordGrowth.dominated (g:=fun x => n x*(512*(binaryWordWidth (n x)+x.k+1)))
      (by fun_prop) hS₂Bound
  have hS₂Rate : Linear S₂ n :=
    GeneralPaperSourceSoftBounds.dominated (mul_poly (linear_identity n) hWidth) hS₂Bound
  have hReference : Polylog (fun x => reference (W x) (o x)) := by
    unfold reference GeneralPaperReducedValuesConstructionStorage.reference arrayWord
    fun_prop
  have hOwnerUpper : Linear (fun x => 2048*(n x+1)*(reference (W x) (o x)+binaryWordWidth (n x)+x.k+1)) n := by
    fun_prop
  have hOwner : Linear (fun x => GeneralPaperOriginalReductionRetainedStorage.footprint (reference (W x) (o x)) (o x)) n := by
    apply GeneralPaperSourceSoftBounds.dominated hOwnerUpper
    intro x
    exact GeneralPaperOriginalReductionRetainedStorage.original_linear true model (W x) (reference (W x) (o x)) x.k
      (values x) (v x) (hv x)
  have hRate := preparation_profile_rate hg W n (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))
    (fun x => (o x).denominator) S₂ o hW hn hS hQ hS₂ hS₂Rate hM hR hHeavy hOwner
  apply GeneralPaperReducedValuesConstructionStorage.rate_amplify hRate 8
  intro x
  dsimp only [o]
  rw [GeneralPaperNativeReductionShape.original_representatives,GeneralPaperLightFieldReduction.representatives]
  omega

theorem native_window_rate {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W n : Input → ℕ) (values : (x : Input) → FixedArrayTable (n x) ℚ)
    (v : (x : Input) → RationalFieldSelector (n x)) (hv : ∀ x j,(values x).read j=(v x).weight j)
    (hW : Tight W) (hn : Small n) (hS : Small (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x))) :
    Soft (fun x => GeneralPaperValueRoundingInputPrice.inputSize (values x)+n x+2^x.k+1)
      (fun x => preparationWindow model (W x) x.k (values x) (v x) (hv x)) :=
  GeneralPaperSourceSoftBounds.dominated (native_profile_rate hg W n values v hv hW hn hS)
    (fun x => native_bounded model (W x) x.k (values x) (v x) (hv x))

end Blotto.GeneralPaperOriginalSourcePreparationStorage
