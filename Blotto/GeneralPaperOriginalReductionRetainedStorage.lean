import Blotto.GeneralPaperCachedCircleRetainedStorage

/-! Full retained original-reduction owner: first weights, both original
index maps, short reduced rationals, denominator/light total/counts and tag.
Both index arrays reserve n slots. Bounds derive from the native return. -/
namespace Blotto.GeneralPaperOriginalReductionRetainedStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def indexFoot {n : ℕ} (W : ℕ) (indices : Array (Fin n)) : ℕ :=
  GeneralPaperEncodedReferenceVector.reservedFootprint W n (fun j : Fin n => natBits j.val) indices

theorem index_bound {n : ℕ} (W : ℕ) (indices : Array (Fin n)) (hSize : indices.size≤n) :
    indexFoot W indices≤n*(natBits n+W)+64*W :=
  GeneralPaperEncodedReferenceVector.reserved_bound W (natBits n) n (fun j : Fin n => natBits j.val) indices hSize
    (fun i => Nat.add_le_add_left (binaryWordWidth_mono indices[i.val].isLt.le) 1)

def footprint {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  arrayFootprint W natBits o.firstWeights+indexFoot W o.classified.heavy+indexFoot W o.classified.light+
    arrayFootprint W rationalWordWidth o.values+natBits o.denominator+natBits o.classified.lightWeight+
    natBits o.representatives+natBits o.m+1+96*W

def profile (W n m Q R V : ℕ) : ℕ :=
  arrayProfile W n (natBits Q)+2*(n*(natBits n+W)+64*W)+arrayProfile W m V+
    2*natBits Q+natBits R+natBits m+1+96*W

theorem bounded {n : ℕ} (W V : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hWeights : ∀ j,o.firstWeights.read j≤o.denominator)
    (hHeavy : o.classified.heavy.size≤n) (hLight : o.classified.light.size≤n)
    (hMass : o.classified.lightWeight≤o.denominator) (hValues : ∀ j,rationalWordWidth (o.values.read j)≤V) :
    footprint W o≤profile W n o.m o.denominator o.representatives V := by
  have hw := array_bound W (natBits o.denominator) natBits o.firstWeights
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hWeights j)) 1)
  have hh := index_bound W o.classified.heavy hHeavy
  have hl := index_bound W o.classified.light hLight
  have hv := array_bound W V rationalWordWidth o.values hValues
  have hm := Nat.add_le_add_left (binaryWordWidth_mono hMass) 1
  change natBits o.classified.lightWeight≤natBits o.denominator at hm
  unfold footprint profile
  nlinarith only [hw,hh,hl,hv,hm]

def ValuesWords {n : ℕ} (o : GeneralPaperReducedValuesDriver.Output n) (V : ℕ) : Prop :=
  ∀ j,rationalWordWidth (o.values.read j)≤V

theorem reduced_words {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k Q : ℕ) (weights : FixedArrayTable n ℕ)
    (hs : ∑ j,weights.read j=Q) :
    ∀ j,rationalWordWidth ((GeneralPaperReducedValuesDriver.run bits model W k Q weights).1.values.read j)≤
      GeneralPaperReducedValueArrayPrice.width Q (GeneralPaperLightFieldReduction.representatives k) := by
  have hw (j : Fin n) : weights.read j≤Q := by
    rw [←hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hL : (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.1.lightWeight≤Q := by
    rw [GeneralPaperLightFieldClassification.data]
    exact GeneralPaperLightFieldScanPrice.prefix_bound bits model W _ Q weights hs n le_rfl
  have hR := congrArg Prod.snd (GeneralPaperLightFieldClassification.data bits model W k Q weights)
  change ValuesWords (GeneralPaperReducedValuesDriver.run bits model W k Q weights).1 _
  rw [GeneralPaperReducedValuesDriver.data]
  unfold GeneralPaperReducedValuesDriver.specification
  split_ifs
  · dsimp only [ValuesWords]
    intro j
    rw [FixedArrayTable.read_ofFn]
    split_ifs
    · exact GeneralPaperReducedValueArrayPrice.ratio_width _ Q _ (hw _)
    · have h := GeneralPaperReducedValueArrayPrice.representative_width _ Q
        (GeneralPaperLightFieldClassification.run bits model W k Q weights).1.2 hL
      simpa only [hR] using h
  · dsimp only [ValuesWords]
    intro j
    rw [FixedArrayTable.read_ofFn]
    exact GeneralPaperReducedValueArrayPrice.ratio_width _ Q _ (hw j)

theorem original_words {n : ℕ} (bits : Bool) (model : RationalCostModel) (W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    ∀ j,rationalWordWidth ((GeneralPaperOriginalValueReduction.run bits model W k values).1.values.read j)≤
      512*(binaryWordWidth n+k+1) := by
  have h := reduced_words bits model W k
    (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.2
    (GeneralPaperValueRoundingPaperContract.run bits model W 256 k values).1.1
    (GeneralPaperValueRoundingPaperContract.source_sum bits model W 256 k values)
  have hWidth := GeneralPaperOriginalValueReductionPrice.returned_width bits model W k values v hv
  rw [(GeneralPaperOriginalValueReduction.retained bits model W k values).2] at hWidth
  intro j
  exact (h j).trans hWidth

theorem original_bound {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
    footprint W o≤profile W n o.m o.denominator o.representatives (512*(binaryWordWidth n+k+1)) := by
  let o := (GeneralPaperOriginalValueReduction.run bits model Wv k values).1
  have hs : ∑ j,o.firstWeights.read j=o.denominator := by
    dsimp only [o]
    rw [(GeneralPaperOriginalValueReduction.retained bits model Wv k values).1,
      (GeneralPaperOriginalValueReduction.retained bits model Wv k values).2]
    exact GeneralPaperValueRoundingPaperContract.source_sum bits model Wv 256 k values
  apply bounded
  · intro j
    rw [←hs]
    exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  · exact GeneralPaperClosedArithmeticSampling.heavy_size bits model Wv k values
  · exact GeneralPaperStrategyPreparationWork.light_size bits model Wv k values
  · exact GeneralPaperNativeCircleLoss.original_mass_bound bits model Wv k values
  · exact original_words bits model Wv k values v hv

theorem original_linear {n : ℕ} (bits : Bool) (model : RationalCostModel) (Wv W k : ℕ)
    (values : FixedArrayTable n ℚ) (v : RationalFieldSelector n) (hv : ∀ j,values.read j=v.weight j) :
    footprint W (GeneralPaperOriginalValueReduction.run bits model Wv k values).1≤
      2048*(n+1)*(W+binaryWordWidth n+k+1) := by
  have h := original_bound bits model Wv W k values v hv
  have hm := (GeneralPaperOriginalValueReduction.count_bounds bits model Wv k values v hv).2.1
  have hQ := GeneralPaperOriginalValueReduction.denominator_word bits model Wv k values v hv
  have hR := GeneralPaperOriginalValueReductionPrice.representatives_word k
  rw [←GeneralPaperNativeReductionShape.original_representatives bits model Wv k values] at hR
  have hM := binaryWordWidth_mono hm
  have hArray := Nat.mul_le_mul hm (show W+512*(binaryWordWidth n+k+1)≤W+512*(binaryWordWidth n+k+1) by rfl)
  have hWeight := Nat.mul_le_mul_left n hQ
  dsimp only [profile,arrayProfile,natBits] at h
  nlinarith only [h,hArray,hWeight,hQ,hR,hM]

end Blotto.GeneralPaperOriginalReductionRetainedStorage
