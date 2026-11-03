import Blotto.GeneralPaperOriginalReductionRetainedStorage

/-! Complete retained descriptions for both native reduction branches.
Source columns own anchors once; sorted rows own references into them.
The full closed sampler additionally owns original maps/weights/short values,
the budget and all four stored sampling controls. -/
namespace Blotto.GeneralPaperClosedDescriptionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open GeneralPaperEnclosingSourceOwners GeneralPaperStrategyDescription GeneralPaperStoredStrategySampler
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 12000000
set_option maxRecDepth 16384

def descriptionFoot {n T K : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : Description o T K → ℕ
  | .circle _ _ rows => GeneralPaperCachedCircleRetainedStorage.pairFoot W o.classified rows+32*W
  | .direct _ columns => columnsFoot W columns.rich+columnsFoot W columns.poor+32*W

def descriptionProfile {n : ℕ} (W T K H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperCachedCircleRetainedStorage.commonProfile W o.classified.light.size o.representatives o.classified.lightWeight+
    2*columnsProfile W T o.m K (1+2*H)+
    2*GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile W T o.m+128*W

theorem reference_rows_mono (W T R m : ℕ) (hm : R≤m) :
    GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile W T R≤
      GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile W T m := by
  unfold GeneralPaperCachedCircleRetainedStorage.referenceRowsProfile arrayProfile
  gcongr

theorem make_bound {n T K : ℕ} (price index : ℕ → ℕ) (A W H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n)
    (hRep : GeneralPaperNativeReductionShape.ReplacedShape o) (hNo : GeneralPaperUnreplacedShape.Shape o)
    (hR : 0<o.representatives) (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K)
    (hConserved : GeneralPaperCircleActualWeights.Conserved o)
    (hRich : ∀ j l,RationalHeight ((physical.rich.read j).anchors.read l) H)
    (hPoor : ∀ j l,RationalHeight ((physical.poor.read j).anchors.read l) H) :
    descriptionFoot W o (make price index A o hRep hNo hR physical).1≤descriptionProfile W T K H o := by
  by_cases h:o.replaced=true
  · obtain ⟨hm,_⟩ := hRep h
    rw [make_circle price index A o hRep hNo hR physical h hm]
    have hp := GeneralPaperCachedCircleRetainedStorage.pair_bound price index A W H o hm physical hConserved hRich hPoor
    have hr := reference_rows_mono W T o.representatives o.m (by omega)
    unfold GeneralPaperCachedCircleRetainedStorage.pairProfile GeneralPaperCachedCircleRetainedStorage.rowsProfile at hp
    rw [←hm] at hp
    dsimp only [descriptionFoot]
    unfold descriptionProfile
    nlinarith only [hp,hr]
  · have hFalse : o.replaced=false := by cases he:o.replaced <;> simp_all
    obtain ⟨hm,_⟩ := hNo hFalse
    rw [make_direct price index A o hRep hNo hR physical hFalse hm]
    have hr := columns_bound W (1+2*H) physical.rich (fun j l => rationalWordWidth_of_height (hRich j l))
    have hp := columns_bound W (1+2*H) physical.poor (fun j l => rationalWordWidth_of_height (hPoor j l))
    dsimp only [descriptionFoot]
    unfold descriptionProfile
    omega

def controlsFoot {T : ℕ} (W : ℕ) (controls : GeneralPaperSamplingControls.Controls T) : ℕ :=
  fields W [controls.rows,controls.rowBits,controls.shifts,controls.shiftBits]

def controlsProfile (W T Rb k : ℕ) : ℕ :=
  fields W [T,Rb,GeneralPaperNativeSelectedSecurity.count k,k+6]

theorem controls_data (W T Rb k : ℕ) (hT : T=2^Rb) :
    controlsFoot W (GeneralPaperSamplingControls.specification T Rb k hT)=controlsProfile W T Rb k := rfl

def footprint {n T K : ℕ} (W : ℕ) (sampler : Sampler n T K) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W sampler.original+
    descriptionFoot W sampler.original sampler.description+rationalWordWidth sampler.budget+
    controlsFoot W sampler.controls+128*W

def profile {n : ℕ} (W T K Rb k B H : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  2048*(n+1)*(W+binaryWordWidth n+k+1)+descriptionProfile W T K H o+
    (1+2*B)+controlsProfile W T Rb k+128*W

theorem native_sampler_bound {n T K : ℕ} (bits : Bool) (model : RationalCostModel) (Wv k W B H Rb : ℕ)
    (price index : ℕ → ℕ) (A : ℕ) (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n)
    (hv : ∀ j,values.read j=v.weight j) (b : ℚ) (hB : RationalHeight b B) (hT : T=2^Rb) :
    let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
    ∀ (physical : GeneralPaperOriginalDrawEquilibrium.Columns T o.m K),
      (∀ j l,RationalHeight ((physical.rich.read j).anchors.read l) H) →
      (∀ j l,RationalHeight ((physical.poor.read j).anchors.read l) H) →
      let description := (make price index A o (GeneralPaperNativeReductionShape.original_shape bits model Wv k values)
        (GeneralPaperUnreplacedShape.original_shape bits model Wv k values)
        (GeneralPaperNativeCircleLoss.original_representatives_positive bits model Wv k values) physical).1
      let sampler : Sampler n T K := ⟨o,b,GeneralPaperSamplingControls.specification T Rb k hT,description⟩
      footprint W sampler≤profile W T K Rb k B H o := by
  dsimp only
  intro physical hRich hPoor
  have ho := GeneralPaperOriginalReductionRetainedStorage.original_linear bits model Wv W k values v hv
  have hd := make_bound price index A W H (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
    (GeneralPaperNativeReductionShape.original_shape bits model Wv k values)
    (GeneralPaperUnreplacedShape.original_shape bits model Wv k values)
    (GeneralPaperNativeCircleLoss.original_representatives_positive bits model Wv k values) physical
    (GeneralPaperCircleActualWeights.original_sum bits model Wv k values) hRich hPoor
  have hb := rationalWordWidth_of_height hB
  dsimp only [footprint,profile]
  rw [controls_data]
  omega

def rawFoot {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W raw.strategies.original.reduced+
    arrayFootprint W natBits raw.strategies.original.weights+natBits raw.strategies.original.Qv+
    natBits raw.exponent+rationalWordWidth raw.budget+
    (match raw.strategies.description with | none => 0 | some description => descriptionFoot W raw.strategies.original.reduced description)+192*W

def preparedFoot {n : ℕ} (W : ℕ) (prepared : GeneralPaperClosedStrategyDriver.Prepared n) : ℕ :=
  rawFoot W prepared.raw+(match prepared.sampler with | none => 0 | some sampler => footprint W sampler)+96*W

theorem raw_covered {n : ℕ} (W : ℕ) (raw : GeneralPaperAccuracyStrategyDriver.Prepared n)
    (description : Description raw.strategies.original.reduced
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows
      (GeneralPaperProxyParameters.prepare raw.strategies.original.reduced.m raw.exponent).K)
    (hDescription : raw.strategies.description=some description)
    (controls : GeneralPaperSamplingControls.Controls
      (GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet raw.strategies.original.reduced.m raw.exponent).lambda raw.exponent).rows) :
    rawFoot W raw≤footprint W (⟨raw.strategies.original.reduced,raw.budget,controls,description⟩)+
      arrayProfile W raw.strategies.original.reduced.m (natBits raw.strategies.original.Qv)+
        natBits raw.strategies.original.Qv+natBits raw.exponent+192*W := by
  have hw := array_bound W (natBits raw.strategies.original.Qv) natBits raw.strategies.original.weights (by
    intro j
    have h : raw.strategies.original.weights.read j≤∑ i,raw.strategies.original.weights.read i :=
      Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [raw.strategies.original.weight_sum] at h
    exact Nat.add_le_add_left (binaryWordWidth_mono h) 1)
  unfold rawFoot footprint
  rw [hDescription]
  dsimp only
  omega

theorem bit_return_storage {n : ℕ} (model : RationalCostModel) (Wv Ws Ap W : ℕ) (words : BinaryAccuracyWords)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j)
    (b : ℚ) (hb : 0<b ∧ b<1) (B : ℕ) (hB : RationalHeight b B) :
    let prepared := (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
    let o := prepared.raw.strategies.original.reduced
    let k := prepared.raw.exponent
    let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
    let H := GeneralPaperSourcePairAnchorHeights.width o.m k
    ∃ sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K,
      prepared.sampler=some sampler ∧ footprint W sampler≤profile W t.rows (GeneralPaperProxyParameters.prepare o.m k).K t.rowBits k B H o ∧
      preparedFoot W prepared≤2*profile W t.rows (GeneralPaperProxyParameters.prepare o.m k).K t.rowBits k B H o+
        arrayProfile W o.m (1+binaryWordWidth n+k+11)+(1+binaryWordWidth n+k+11)+natBits k+288*W := by
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) Ap words).1
  let raw := (GeneralPaperAccuracyStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1
  let o := (GeneralPaperOriginalValueReduction.run true model Wv k values).1
  let t := GeneralPaperTrajectoryParameters.prepare (GeneralPaperProxyParameters.alphabet o.m k).lambda k
  let H := GeneralPaperSourcePairAnchorHeights.width o.m k
  obtain ⟨physical,hSource,hRich,hPoor⟩ := GeneralPaperSourcePairAnchorHeights.original_bit_return model Wv Ws k values v hv b hb
  have hDescription := GeneralPaperOriginalStrategyDriver.bit_description model Wv Ws Ap k values v hv b hb physical hSource
  let made : Description o t.rows (GeneralPaperProxyParameters.prepare o.m k).K :=
    (make model.rat (fun w => w) Ap o (GeneralPaperNativeReductionShape.original_shape true model Wv k values)
      (GeneralPaperUnreplacedShape.original_shape true model Wv k values)
      (GeneralPaperNativeCircleLoss.original_representatives_positive true model Wv k values) physical).1
  let controls := GeneralPaperSamplingControls.specification t.rows t.rowBits k
    (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k)
  let sampler : Sampler n t.rows (GeneralPaperProxyParameters.prepare o.m k).K := ⟨o,b,controls,made⟩
  have hSampler : (GeneralPaperClosedStrategyDriver.bit model Wv Ws Ap words values v hv b hb).1.sampler=some sampler :=
    GeneralPaperClosedStrategyDriver.close_some (fun w => w) Ap raw made hDescription
  have hBound := native_sampler_bound true model Wv k W B H t.rowBits model.rat (fun w => w) Ap values v hv b hB
    (GeneralPaperTrajectoryParameters.rows_power (GeneralPaperProxyParameters.alphabet o.m k).lambda k) physical hRich hPoor
  change footprint W sampler≤profile W t.rows (GeneralPaperProxyParameters.prepare o.m k).K t.rowBits k B H o at hBound
  have hRaw := raw_covered W raw made hDescription controls
  change rawFoot W raw≤footprint W sampler+arrayProfile W o.m (natBits raw.strategies.original.Qv)+
    natBits raw.strategies.original.Qv+natBits k+192*W at hRaw
  have hm := (GeneralPaperOriginalValueReduction.count_bounds true model Wv k values v hv).2.1
  have hQ := GeneralPaperOriginalSourceValuePreparation.denominator_word true model Wv k values v hv
  have hn := binaryWordWidth_mono hm
  change binaryWordWidth raw.strategies.original.Qv≤binaryWordWidth o.m+k+11 at hQ
  change binaryWordWidth o.m≤binaryWordWidth n at hn
  have hNat : natBits raw.strategies.original.Qv≤1+binaryWordWidth n+k+11 := by
    unfold natBits
    omega
  have hArray := Nat.mul_le_mul_left o.m hNat
  dsimp only
  refine ⟨sampler,hSampler,hBound,?_⟩
  unfold preparedFoot
  rw [hSampler]
  dsimp only
  change rawFoot W raw+footprint W sampler+96*W≤
    2*profile W t.rows (GeneralPaperProxyParameters.prepare o.m k).K t.rowBits k B H o+
      arrayProfile W o.m (1+binaryWordWidth n+k+11)+(1+binaryWordWidth n+k+11)+natBits k+288*W
  dsimp only [arrayProfile] at hRaw ⊢
  nlinarith only [hRaw,hBound,hArray,hNat]

end Blotto.GeneralPaperClosedDescriptionStorage
