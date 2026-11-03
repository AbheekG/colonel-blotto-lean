import Blotto.GeneralPaperStrategyDescriptionConstructionStorage

/-! Full original-value/source caller with original rational input,
reconstruction data and complete physical output retained. The source
bound extends to every word above the already derived local reference;
no supplied source/cost/width oracle or runtime census is introduced. -/
namespace Blotto.GeneralPaperOriginalSourceDriverConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage GeneralPaperProxyParameters
open GeneralPaperStrategyDescriptionConstructionStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

structure SourceCursor (m k Qv : ℕ) where
  exponent : ℕ
  target : ℕ
  hExponent : exponent≤74+2*k
  hTarget : GeneralPaperSourcePreparationControls.IsTarget m (alphabet m k).lambda k Qv target
  material : GeneralPaperFastPreparedInputStorage.Cursor m (alphabet m k).lambda k Qv
  cursor : ℕ
  hCursor : cursor≤m
  outer : ℕ
  hOuter : outer≤m
  inner : ℕ
  hInner : inner≤(prepare m k).K

theorem enlarged_source_bound {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W : ℕ) (x : GeneralPaperSourceWordGrowth.Input) (hm : 0<x.m) (hQv : 0<x.Qv) (hp : ∀ j,0<x.weights.read j)
    (hReference : GeneralPaperFastDriverReference.width C d x≤W) (c : SourceCursor x.m x.k x.Qv) :
    GeneralPaperFastWholeDriverStorage.window model W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb
      c.exponent c.target c.material c.cursor c.hCursor c.outer c.hOuter c.inner c.hInner≤
        GeneralPaperFastWholeDriverStorage.profile model C d W x.m x.k x.Qv x.B ∧
      (GeneralPaperFastRationalPairDriver.run model W W x.k x.Qv hQv x.weights hp x.weight_sum x.b x.hb).2≤
        GeneralPaperFastWholeDriverStorage.price model C d W x.m x.k x.Qv x.B := by
  have h := GeneralPaperFastDriverReference.local_words C d x
  have hr := GeneralPaperFastDriverReference.row_words C d x
  have hW := (GeneralPaperFastDriverReference.positive_width C d x).trans hReference
  have hPrepared := GeneralPaperSourcePreparedPairOwners.bounded model W x.k x.Qv hQv x.weights hp x.weight_sum x.b
    C d x.B hg hm x.hb x.hB hW (h.2.1.trans hReference) (h.2.2.1.trans hReference)
    (h.2.2.2.1.trans hReference) (h.1.trans hReference) (h.2.2.2.2.1.trans hReference)
    (h.2.2.2.2.2.1.trans hReference) (hr.2.trans hReference) c.cursor c.hCursor c.outer c.hOuter c.inner c.hInner
  have hCached := GeneralPaperCachedBitPairStorage.bounded_of_prepared model C d W x.k x.Qv x.B hQv
    x.weights hp x.weight_sum x.b x.hb c.cursor c.hCursor c.outer c.hOuter c.inner c.hInner hPrepared
  exact GeneralPaperFastWholeDriverStorage.bounded_of_cached model C d W x.k x.Qv x.B hQv x.weights hp x.weight_sum
    x.b x.hb x.hB ((GeneralPaperFastDriverReference.control_word C d x).trans hReference)
    c.exponent c.target c.hExponent c.hTarget c.material c.cursor c.hCursor c.outer c.hOuter c.inner c.hInner hCached

def originalFoot {n : ℕ} (W : ℕ) (o : GeneralPaperOriginalSourceValuePreparation.Output n) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o.reduced+arrayFootprint W natBits o.weights+natBits o.Qv+128*W

def originalProfile {n : ℕ} (W Qv : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W red+arrayProfile W red.m (natBits Qv)+natBits Qv+128*W

theorem original_bound {n : ℕ} (W : ℕ) (o : GeneralPaperOriginalSourceValuePreparation.Output n) :
    originalFoot W o≤originalProfile W o.Qv o.reduced := by
  have hw (j : Fin o.reduced.m) : o.weights.read j≤o.Qv := by
    rw [←o.weight_sum]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have ha := array_bound W (natBits o.Qv) natBits o.weights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  unfold originalFoot originalProfile
  omega

def sourceFoot {n k : ℕ} (W : ℕ) (source : GeneralPaperOriginalSourceValueDriver.Prepared n k) : ℕ :=
  originalFoot W source.original+(match source.physical with | none => 0 | some columns => physicalFoot W columns)+64*W

def returnProfile {n : ℕ} (W k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  originalProfile W Qv red+physicalProfile W (GeneralPaperTrajectoryParameters.prepare (alphabet red.m k).lambda k).rows
    red.m (prepare red.m k).K H+64*W

noncomputable def price {n : ℕ} (model : RationalCostModel) (C d W k S Qv B : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalSourcePreparationStorage.preparationPrice model W k S red.denominator
    (GeneralPaperValueRoundingInputPrice.inputSize red.values) red+
    GeneralPaperFastWholeDriverStorage.price model C d W red.m k Qv B+128*W

noncomputable def cap {n : ℕ} (model : RationalCostModel) (C d W k S Qv B : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  n+k+W+red.m+Qv+price model C d W k S Qv B red+128*W+1

def controls {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1) : List ℕ :=
  let p := GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv
  let pair := GeneralPaperFastRationalPairDriver.run model W W k p.1.Qv p.1.Qv_positive p.1.weights p.1.weights_positive p.1.weight_sum b hb
  [n,k,W,p.1.reduced.m,p.1.Qv,p.2,pair.2,p.2+pair.2,128*W,(GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb).2]

noncomputable def window {n : ℕ} (model : RationalCostModel) (W k : ℕ) (values : FixedArrayTable n ℚ)
    (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hb : 0<b ∧ b<1)
    (c : SourceCursor (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.reduced.m k
      (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1.Qv) : ℕ :=
  let p := GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv
  let made := GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb
  GeneralPaperOriginalSourcePreparationStorage.preparationWindow model W k values v hv+
    GeneralPaperFastWholeDriverStorage.window model W k p.1.Qv p.1.Qv_positive p.1.weights p.1.weights_positive p.1.weight_sum b hb
      c.exponent c.target c.material c.cursor c.hCursor c.outer c.hOuter c.inner c.hInner+
    arrayFootprint W rationalWordWidth values+rationalWordWidth b+originalFoot W p.1+sourceFoot W made.1+
    fields W (controls model W k values v hv b hb)+256*W

noncomputable def profile {n : ℕ} (model : RationalCostModel) (C d W k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalSourcePreparationStorage.preparationProfile model W k S red.denominator
    (GeneralPaperValueRoundingInputPrice.inputSize red.values) red+
    GeneralPaperFastWholeDriverStorage.profile model C d W red.m k Qv B+
    (S+n*W+64*W)+(1+2*B)+originalProfile W Qv red+returnProfile W k Qv H red+
    10*(natBits (cap model C d W k S Qv B red)+W)+288*W

theorem bounded {n : ℕ} {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d)
    (W k B : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B) :
    let p := (GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv).1
    let x := GeneralPaperOriginalSourceValuePreparation.input p k B b hb hB
    ∀ (_hReference : GeneralPaperFastDriverReference.width C d x≤W) (c : SourceCursor p.reduced.m k p.Qv),
      window model W k values v hv b hb c≤profile model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B
        (GeneralPaperSourcePairAnchorHeights.width p.reduced.m k) p.reduced ∧
      (GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb).2≤
        price model C d W k (GeneralPaperValueRoundingInputPrice.inputSize values) p.Qv B p.reduced := by
  dsimp only
  intro hReference c
  let p := GeneralPaperOriginalSourceValuePreparation.run true model W k values v hv
  let red := p.1.reduced
  let S := GeneralPaperValueRoundingInputPrice.inputSize values
  let H := GeneralPaperSourcePairAnchorHeights.width red.m k
  let x := GeneralPaperOriginalSourceValuePreparation.input p.1 k B b hb hB
  change GeneralPaperFastDriverReference.width C d x≤W at hReference
  have hSource := enlarged_source_bound hg W x (GeneralPaperOriginalSourceValuePreparation.count_bounds true model W k values v hv).1
    p.1.Qv_positive p.1.weights_positive hReference c
  dsimp only [x,GeneralPaperOriginalSourceValuePreparation.input] at hSource
  have hPrep := GeneralPaperOriginalSourcePreparationStorage.preparation_bounded model W k values v hv
  have hPrepWork := GeneralPaperOriginalSourcePreparationStorage.preparation_work model W k values v hv
  have hDen : red.denominator=(GeneralPaperValueRoundingPaperContract.run true model W 256 k values).1.2 :=
    (GeneralPaperOriginalValueReduction.retained true model W k values).2
  change GeneralPaperOriginalSourcePreparationStorage.preparationWindow model W k values v hv≤
    GeneralPaperOriginalSourcePreparationStorage.preparationProfile model W k S _
      (GeneralPaperValueRoundingInputPrice.inputSize red.values) red at hPrep
  change p.2≤GeneralPaperOriginalSourcePreparationStorage.preparationPrice model W k S _
    (GeneralPaperValueRoundingInputPrice.inputSize red.values) red at hPrepWork
  rw [←hDen] at hPrep hPrepWork
  have hOriginal := original_bound W p.1
  have hInput : arrayFootprint W rationalWordWidth values=S+n*W+64*W := by
    unfold arrayFootprint S GeneralPaperValueRoundingInputPrice.inputSize
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,Nat.cast_id]
    omega
  have hBudget := rationalWordWidth_of_height hB
  obtain ⟨physical,hPhysical,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model W W k values v hv b hb
  have hReturn : sourceFoot W (GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb).1≤
      returnProfile W k p.1.Qv H red := by
    have hColumns := physical_bound W H physical hRich hPoor
    change physicalFoot W physical≤physicalProfile W (GeneralPaperTrajectoryParameters.prepare (alphabet red.m k).lambda k).rows
      red.m (prepare red.m k).K H at hColumns
    unfold sourceFoot returnProfile
    rw [hPhysical]
    change originalFoot W p.1+physicalFoot W physical+64*W≤originalProfile W p.1.Qv red+
      physicalProfile W (GeneralPaperTrajectoryParameters.prepare (alphabet red.m k).lambda k).rows red.m (prepare red.m k).K H+64*W
    change originalFoot W p.1≤originalProfile W p.1.Qv red at hOriginal
    omega
  have hShape : (GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb).2=p.2+
      (GeneralPaperFastRationalPairDriver.run model W W k p.1.Qv p.1.Qv_positive p.1.weights p.1.weights_positive p.1.weight_sum b hb).2+128*W := rfl
  have hWork : (GeneralPaperOriginalSourceValueDriver.bit model W W k values v hv b hb).2≤price model C d W k S p.1.Qv B red := by
    unfold price
    dsimp only [red] at *
    omega
  have hFields := fields_bound W (natBits (cap model C d W k S p.1.Qv B red)) (controls model W k values v hv b hb) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> dsimp only [p,red,S] at * <;> omega)
  change fields W _≤10*(natBits (cap model C d W k S p.1.Qv B red)+W)+32*W at hFields
  refine ⟨?_,hWork⟩
  unfold window profile
  dsimp only [p,red,S,H] at *
  omega

@[fun_prop]
theorem original_scaling {n : ℕ} (Qv : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => originalProfile W Qv red) := by
  unfold originalProfile arrayProfile
  fun_prop

@[fun_prop]
theorem return_scaling {n : ℕ} (k Qv H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => returnProfile W k Qv H red) := by unfold returnProfile;fun_prop

@[fun_prop]
theorem preparation_price_scaling {n : ℕ} (model : RationalCostModel) (k S : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperOriginalSourcePreparationStorage.preparationPrice model W k S red.denominator
      (GeneralPaperValueRoundingInputPrice.inputSize red.values) red) := by
  unfold GeneralPaperOriginalSourcePreparationStorage.preparationPrice GeneralPaperOriginalSourcePreparationStorage.reference
    GeneralPaperReducedValuesConstructionStorage.reference
  fun_prop

@[fun_prop]
theorem whole_price_scaling (model : RationalCostModel) (C d m k Qv B : ℕ) :
    GeneralPaperReferenceScaling.Scale (fun W => GeneralPaperFastWholeDriverStorage.price model C d W m k Qv B) := by
  have hp := GeneralPaperFastWholeDriverStorageRates.prepared_price_scaling model m k Qv B
  have hc := GeneralPaperCachedBitPairStorageRates.price_scaling model C d m k Qv
  unfold GeneralPaperFastWholeDriverStorage.price
  fun_prop

@[fun_prop]
theorem price_scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => price model C d W k S Qv B red) := by unfold price;fun_prop

@[fun_prop]
theorem scaling {n : ℕ} (model : RationalCostModel) (C d k S Qv B H : ℕ) (red : GeneralPaperReducedValuesDriver.Output n) :
    GeneralPaperReferenceScaling.Scale (fun W => profile model C d W k S Qv B H red) := by unfold profile cap;fun_prop

end Blotto.GeneralPaperOriginalSourceDriverConstructionStorage
