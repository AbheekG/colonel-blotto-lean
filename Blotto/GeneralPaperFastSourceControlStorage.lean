import Blotto.GeneralPaperSourceControlsConstructionStorage

/-! Actual fast-front/source-control parent. The actual returned alphabet
feeds parameter construction once. Original ratio, full returned front and
complete new control cache coexist with both constructor lifetimes and all
twelve parent fields. Selected constructor cursors are erased observers. -/
namespace Blotto.GeneralPaperFastSourceControlStorage
open GeneralPaperEncodedScalarStorage GeneralPaperProxyParameters
set_option autoImplicit false
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384

def price (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  GeneralPaperFastInputClassifier.prepareProfile model W m k B+
    GeneralPaperSourceControlsConstructionStorage.price model W m (alphabet m k).lambda k Qv+64*W

def metadataCap (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  m+k+Qv+(alphabet m k).lambda+price model W m k Qv B+128*W+1

def window (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (exponent target : ℕ) : ℕ :=
  let front := GeneralPaperFastInputClassifier.prepare model W m k b
  let control := GeneralPaperSourcePreparationCache.prepare model.rat W m front.1.1.2.lambda k Qv
  let result := GeneralPaperFastInputClassifier.source model W m k Qv b
  GeneralPaperFastPreparedFrontStorage.window model W m k b+
    GeneralPaperSourceControlsConstructionStorage.window model W m front.1.1.2.lambda k Qv exponent target+
    GeneralPaperClassifierResultStorage.frontFootprint W front.1+GeneralPaperPreparationCacheStorage.footprint W control.1+
    rationalWordWidth b+fields W [m,k,Qv,W,front.2,control.2,result.2,front.2+control.2,64*W,96*W,128*W,front.1.1.2.lambda]+256*W

def profile (model : RationalCostModel) (W m k Qv B : ℕ) : ℕ :=
  2*GeneralPaperFastPreparedFrontStorage.profile model W m k B+
    2*GeneralPaperSourceControlsConstructionStorage.profile model W m (alphabet m k).lambda k Qv+
    12*(natBits (metadataCap model W m k Qv B)+W)+288*W

theorem bounded (model : RationalCostModel) (W m k Qv B : ℕ) (b : ℚ) (hb : 0<b ∧ b<1) (hB : RationalHeight b B)
    (hW : GeneralPaperPrecallControlWord.word m k≤W) (exponent target : ℕ) (he : exponent≤74+2*k)
    (ht : GeneralPaperSourcePreparationControls.IsTarget m (alphabet m k).lambda k Qv target) :
    window model W m k Qv b exponent target≤profile model W m k Qv B ∧
      (GeneralPaperFastInputClassifier.source model W m k Qv b).2≤price model W m k Qv B := by
  let front := GeneralPaperFastInputClassifier.prepare model W m k b
  let control := GeneralPaperSourcePreparationCache.prepare model.rat W m front.1.1.2.lambda k Qv
  let result := GeneralPaperFastInputClassifier.source model W m k Qv b
  have hA : front.1.1.2=alphabet m k := congrArg (fun r => r.1.2) (GeneralPaperFastInputClassifier.prepare_data model W m k b hb)
  have hTarget : GeneralPaperSourcePreparationControls.IsTarget m front.1.1.2.lambda k Qv target := by rw [hA];exact ht
  have hFront := GeneralPaperFastPreparedFrontStorage.bounded model W m k B b hb hB hW
  have hControl := GeneralPaperSourceControlsConstructionStorage.bounded model W m front.1.1.2.lambda k Qv exponent target he hTarget
  have hConWindow : GeneralPaperSourceControlsConstructionStorage.window model W m front.1.1.2.lambda k Qv exponent target≤
      GeneralPaperSourceControlsConstructionStorage.profile model W m (alphabet m k).lambda k Qv := hControl.1.trans_eq (by rw [hA])
  have hConWork : control.2≤GeneralPaperSourceControlsConstructionStorage.price model W m (alphabet m k).lambda k Qv :=
    hControl.2.trans_eq (by rw [hA])
  have hFrontWork : front.2≤GeneralPaperFastInputClassifier.prepareProfile model W m k B := hFront.2
  have hEq : result.2=front.2+control.2+64*W := rfl
  have hWork : result.2≤price model W m k Qv B := by unfold price;omega
  have hInputs := GeneralPaperFastPreparedFrontStorage.retained_inputs model W m k b
  have hFrontOwners : GeneralPaperClassifierResultStorage.frontFootprint W front.1+rationalWordWidth b≤
      GeneralPaperFastPreparedFrontStorage.profile model W m k B := by
    have h := hInputs.trans hFront.1
    change _+_+rationalWordWidth b+GeneralPaperClassifierResultStorage.frontFootprint W front.1≤_ at h
    omega
  have hControlOwner := (GeneralPaperSourceControlsConstructionStorage.returned model W m front.1.1.2.lambda k Qv exponent target).trans hConWindow
  change GeneralPaperPreparationCacheStorage.footprint W control.1≤_ at hControlOwner
  have hf := fields_bound W (natBits (metadataCap model W m k Qv B))
    [m,k,Qv,W,front.2,control.2,result.2,front.2+control.2,64*W,96*W,128*W,front.1.1.2.lambda] (by
    intro z hz
    apply Nat.add_le_add_left (binaryWordWidth_mono _) 1
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hz
    rcases hz with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
    all_goals unfold metadataCap;rw [hA] at *;omega)
  change fields W _≤12*(natBits (metadataCap model W m k Qv B)+W)+32*W at hf
  refine ⟨?_,hWork⟩
  dsimp only [window,profile]
  change GeneralPaperFastPreparedFrontStorage.window model W m k b+
    GeneralPaperSourceControlsConstructionStorage.window model W m front.1.1.2.lambda k Qv exponent target+
    GeneralPaperClassifierResultStorage.frontFootprint W front.1+GeneralPaperPreparationCacheStorage.footprint W control.1+
    rationalWordWidth b+fields W [m,k,Qv,W,front.2,control.2,result.2,front.2+control.2,64*W,96*W,128*W,front.1.1.2.lambda]+256*W≤_
  omega

theorem retained_inputs (model : RationalCostModel) (W m k Qv : ℕ) (b : ℚ) (exponent target : ℕ) :
    GeneralPaperClassifierResultStorage.frontFootprint W (GeneralPaperFastInputClassifier.source model W m k Qv b).1.1+
      GeneralPaperPreparationCacheStorage.footprint W (GeneralPaperFastInputClassifier.source model W m k Qv b).1.2+
      rationalWordWidth b≤window model W m k Qv b exponent target := by
  dsimp only [window,GeneralPaperFastInputClassifier.source]
  omega

end Blotto.GeneralPaperFastSourceControlStorage
