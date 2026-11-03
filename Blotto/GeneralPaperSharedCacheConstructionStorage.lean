import Blotto.GeneralPaperCircleArcConstructionStorage

/-! Construction peaks of the single shared circle cache. Full returned
owners coexist with active child construction, list materialization and
native parent work/control fields. Original reduction owners are retained
explicitly by the enclosing original-light-weight constructor. -/
namespace Blotto.GeneralPaperSharedCacheConstructionStorage
open GeneralPaperEncodedScalarStorage GeneralPaperEncodedBasisStorage
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 10000000
set_option maxRecDepth 16384

def magnitude (R mass : ℕ) : ℕ := R+mass+R*mass
def price (model : RationalCostModel) (W g R mass : ℕ) : ℕ :=
  GeneralPaperCircleCoefficientConstructionStorage.price model W g R mass+
    GeneralPaperCircleArcConstructionStorage.price model W g (magnitude R mass)+32*(g+1)*W+64*W
def cap (model : RationalCostModel) (W g R mass : ℕ) : ℕ :=
  g+R+mass+price model W g R mass+32*(g+1)*W+64*W+1

def controls {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ) : List ℕ :=
  let coeff := GeneralPaperCircleRationalCoefficients.run model.rat (fun w => w) W R mass weights
  let arcs := GeneralPaperCircleArcMetadata.run model.rat W R (List.ofFn weights.read) 0
  let metadata := GeneralPaperNativeChoiceArray.prepare model.rat W R weights
  let made := GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W R mass weights
  [g,R,mass,coeff.2,arcs.2,metadata.2,32*(g+1)*W,made.2,coeff.2+metadata.2,64*W]

def window {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (count : ℕ) (hc : count≤g) (copied : ℕ) : ℕ :=
  GeneralPaperCircleCoefficientConstructionStorage.window model W R mass weights count hc+
    GeneralPaperStockListPayloadStorage.ofFnWindow W copied natBits weights.read+
    GeneralPaperCircleArcConstructionStorage.window model W R (List.ofFn weights.read) 0+
    GeneralPaperCachedCircleRetainedStorage.commonFoot W
      (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W R mass weights).1+
    fields W (controls model W R mass weights)+128*W

def profile (model : RationalCostModel) (W g R mass : ℕ) : ℕ :=
  GeneralPaperCircleCoefficientConstructionStorage.profile model W g R mass+
    GeneralPaperStockListPayloadStorage.ofFnProfile W (natBits mass) g+
    GeneralPaperCircleArcConstructionStorage.profile model W g (magnitude R mass) R+
    GeneralPaperCachedCircleRetainedStorage.commonProfile W g R mass+
    10*(natBits (cap model W g R mass)+W)+160*W

theorem arc_work {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=mass) :
    (GeneralPaperCircleArcMetadata.run model.rat W R (List.ofFn weights.read) 0).2≤
      GeneralPaperCircleArcConstructionStorage.price model W g (magnitude R mass) := by
  apply GeneralPaperCircleArcConstructionStorage.work
  · simp only [List.length_ofFn,le_refl]
  · unfold magnitude;omega
  · rw [List.sum_ofFn,hs,Nat.zero_add];unfold magnitude;omega
  · intro w hw
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hw
    have h : weights.read j≤mass := by
      rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    unfold magnitude;omega

theorem work {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=mass) (hW : 1≤W) (hIndex : binaryWordWidth (g+1)≤W) :
    (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W R mass weights).2≤price model W g R mass := by
  have hw (j : Fin g) : weights.read j≤mass := by
    rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hc := GeneralPaperCircleCoefficientConstructionStorage.work model W R mass weights hw hW hIndex
  have ha := arc_work model W R mass weights hs
  unfold GeneralPaperCachedCircleCommon.run GeneralPaperNativeChoiceArray.prepare price
  dsimp only
  omega

theorem bounded {g : ℕ} (model : RationalCostModel) (W R mass : ℕ) (weights : FixedArrayTable g ℕ)
    (hs : ∑ j,weights.read j=mass) (hW : 1≤W) (hIndex : binaryWordWidth (g+1)≤W)
    (count : ℕ) (hc : count≤g) (copied : ℕ) :
    window model W R mass weights count hc copied≤profile model W g R mass := by
  have hw (j : Fin g) : weights.read j≤mass := by
    rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  have hCoeff := GeneralPaperCircleCoefficientConstructionStorage.bounded model W R mass weights hw hW hIndex count hc
  have hList := GeneralPaperStockListPayloadStorage.ofFn_bound W (natBits mass) copied natBits weights.read
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1)
  have hArcs := GeneralPaperCircleArcConstructionStorage.bounded model W g (magnitude R mass) R (List.ofFn weights.read) 0
    (by simp only [List.length_ofFn,le_refl]) (by unfold magnitude;omega)
    (by rw [List.sum_ofFn,hs,Nat.zero_add];unfold magnitude;omega)
    (by intro w hm;obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hm;have h := hw j;unfold magnitude;omega)
  have hRetained := GeneralPaperCachedCircleRetainedStorage.common_bound model.rat (fun w => w) W W R mass weights hs
  have hWork := work model W R mass weights hs hW hIndex
  have hCoefWork := GeneralPaperCircleCoefficientConstructionStorage.work model W R mass weights hw hW hIndex
  have hArcWork := arc_work model W R mass weights hs
  have hShape : (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W R mass weights).2=
      (GeneralPaperCircleRationalCoefficients.run model.rat (fun w => w) W R mass weights).2+
      (GeneralPaperNativeChoiceArray.prepare model.rat W R weights).2+64*W := rfl
  have hMeta : (GeneralPaperNativeChoiceArray.prepare model.rat W R weights).2=
      (GeneralPaperCircleArcMetadata.run model.rat W R (List.ofFn weights.read) 0).2+32*(g+1)*W := rfl
  have hf := fields_bound W (natBits (cap model W g R mass)) (controls model W R mass weights) (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [controls,List.mem_cons,List.not_mem_nil,or_false] at hz
    unfold cap
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤10*(natBits (cap model W g R mass)+W)+32*W at hf
  unfold window profile
  omega

def lightCallback {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (j : Fin o.classified.light.size) : ℕ×ℕ :=
  (o.firstWeights.read (GeneralPaperLightFieldOrder.index o.classified.light j),64*W)

def lightScalar {n : ℕ} (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (j : Fin o.classified.light.size) : ℕ :=
  natBits (lightCallback W o j).1+
    fields W [j.val,(GeneralPaperLightFieldOrder.index o.classified.light j).val,(lightCallback W o j).1,64*W]+64*W

def lightScalarProfile (W n g mass : ℕ) : ℕ :=
  natBits mass+4*(natBits (n+g+mass+64*W+1)+W)+96*W

theorem light_scalar_bound {n : ℕ} (W mass : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hw : ∀ j,(lightCallback W o j).1≤mass) (j : Fin o.classified.light.size) :
    lightScalar W o j≤lightScalarProfile W n o.classified.light.size mass := by
  have hp := Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1
  change natBits (lightCallback W o j).1≤natBits mass at hp
  have hj := j.isLt.le
  have hi := (GeneralPaperLightFieldOrder.index o.classified.light j).isLt.le
  have hf := fields_bound W (natBits (n+o.classified.light.size+mass+64*W+1))
    [j.val,(GeneralPaperLightFieldOrder.index o.classified.light j).val,(lightCallback W o j).1,64*W] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      have h := hw j
      rcases hz with rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤4*(natBits (n+o.classified.light.size+mass+64*W+1)+W)+32*W at hf
  unfold lightScalar lightScalarProfile
  omega

def originalPrice {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperNativePayloadFillStorage.workCap W o.classified.light.size (64*W)+
    price model W o.classified.light.size o.representatives o.classified.lightWeight+64*W

def originalWindow {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (count : ℕ) (hc : count≤o.classified.light.size) (copied : ℕ) : ℕ :=
  let weights := GeneralPaperNativeLightWeights.run (fun w => w) W o
  let common := GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W o.representatives o.classified.lightWeight weights.1
  let made := GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+
    GeneralPaperNativePayloadFillStorage.window W natBits (lightCallback W o) (lightScalar W o) count hc+
    window model W o.representatives o.classified.lightWeight weights.1 count hc copied+
    fields W [weights.2,common.2,weights.2+common.2,64*W,made.2]+128*W

def originalProfile {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n) : ℕ :=
  GeneralPaperOriginalReductionRetainedStorage.footprint W o+
    GeneralPaperNativePayloadFillStorage.profile W (natBits o.classified.lightWeight) o.classified.light.size (64*W)
      (lightScalarProfile W n o.classified.light.size o.classified.lightWeight)+
    profile model W o.classified.light.size o.representatives o.classified.lightWeight+
    5*(natBits (originalPrice model W o)+W)+160*W

theorem original_work {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hs : ∑ j,(GeneralPaperNativeLightWeights.run (fun w => w) W o).1.read j=o.classified.lightWeight)
    (hW : 1≤W) (hIndex : binaryWordWidth (o.classified.light.size+1)≤W) :
    (GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o).2≤originalPrice model W o := by
  have hFill := GeneralPaperNativePayloadFillStorage.prefix_work W (64*W) (lightCallback W o)
    (fun _ => le_rfl) hW hIndex o.classified.light.size le_rfl
  change (GeneralPaperNativeLightWeights.run (fun w => w) W o).2≤
    GeneralPaperNativePayloadFillStorage.workCap W o.classified.light.size (64*W) at hFill
  have hCommon := work model W o.representatives o.classified.lightWeight
    (GeneralPaperNativeLightWeights.run (fun w => w) W o).1 hs hW hIndex
  unfold GeneralPaperCachedCircleCommon.fromOriginal originalPrice
  dsimp only
  omega

theorem original_bounded {n : ℕ} (model : RationalCostModel) (W : ℕ) (o : GeneralPaperReducedValuesDriver.Output n)
    (hs : ∑ j,(GeneralPaperNativeLightWeights.run (fun w => w) W o).1.read j=o.classified.lightWeight)
    (hW : 1≤W) (hIndex : binaryWordWidth (o.classified.light.size+1)≤W)
    (count : ℕ) (hc : count≤o.classified.light.size) (copied : ℕ) :
    originalWindow model W o count hc copied≤originalProfile model W o := by
  have hw (j : Fin o.classified.light.size) : (lightCallback W o j).1≤o.classified.lightWeight := by
    have h : (GeneralPaperNativeLightWeights.run (fun w => w) W o).1.read j≤o.classified.lightWeight := by
      rw [←hs];exact Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
    rw [GeneralPaperNativeLightWeights.data,FixedArrayTable.read_ofFn] at h
    exact h
  have hFill := GeneralPaperNativePayloadFillStorage.bounded W (natBits o.classified.lightWeight) (64*W)
    (lightScalarProfile W n o.classified.light.size o.classified.lightWeight) natBits (lightCallback W o) (lightScalar W o)
    (fun j => Nat.add_le_add_left (binaryWordWidth_mono (hw j)) 1) (fun _ => le_rfl)
    (light_scalar_bound W o.classified.lightWeight o hw) hW hIndex count hc
  have hCommon := bounded model W o.representatives o.classified.lightWeight
    (GeneralPaperNativeLightWeights.run (fun w => w) W o).1 hs hW hIndex count hc copied
  have hWork := original_work model W o hs hW hIndex
  have hShape : (GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o).2=
      (GeneralPaperNativeLightWeights.run (fun w => w) W o).2+
      (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W o.representatives o.classified.lightWeight
        (GeneralPaperNativeLightWeights.run (fun w => w) W o).1).2+64*W := rfl
  have hf := fields_bound W (natBits (originalPrice model W o))
    [(GeneralPaperNativeLightWeights.run (fun w => w) W o).2,
      (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W o.representatives o.classified.lightWeight
        (GeneralPaperNativeLightWeights.run (fun w => w) W o).1).2,
      (GeneralPaperNativeLightWeights.run (fun w => w) W o).2+
      (GeneralPaperCachedCircleCommon.run model.rat (fun w => w) W o.representatives o.classified.lightWeight
        (GeneralPaperNativeLightWeights.run (fun w => w) W o).1).2,
      64*W,(GeneralPaperCachedCircleCommon.fromOriginal model.rat (fun w => w) W o).2] (by
      intro z hz
      apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
      rcases hz with rfl|rfl|rfl|rfl|rfl <;> omega)
  change fields W _≤5*(natBits (originalPrice model W o)+W)+32*W at hf
  unfold originalWindow originalProfile
  dsimp only
  omega

end Blotto.GeneralPaperSharedCacheConstructionStorage
