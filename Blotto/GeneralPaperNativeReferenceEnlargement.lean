import Blotto.GeneralPaperNativeResourceWordContract

/-! The unequal preparation reserve and every native floor remain valid
at any larger word, allowing an executable original-input calibration. -/
namespace Blotto.GeneralPaperNativeReferenceEnlargement
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperNativeResourceWordContract
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem profile_above (f : ℕ → ℕ) (hf : GeneralPaperReferenceScaling.Scale f)
    (W : ℕ) (hW : GeneralPaperReferenceCapacity.referenceWord (f 1) ≤ W) : f W < 2 ^ W := by
  have h := GeneralPaperReferenceCapacity.padded_profile_capacity f hf
    (W - GeneralPaperReferenceCapacity.referenceWord (f 1))
  simpa only [Nat.add_sub_of_le hW] using h

theorem reserve_above (model : RationalCostModel) (C d : ℕ) (p : Problem) (W : ℕ)
    (hW : word model C d p ≤ W) : reserve model C d W p < 2 ^ W := by
  apply profile_above (fun A => reserve model C d A p)
    (GeneralPaperFullPreparationReference.scaling model C d (accuracySize p) (exponent p) (originalSize p)
      (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)) W
  apply le_trans _ hW
  unfold word GeneralPaperFullPreparationReference.width
  exact Nat.le_add_right _ _

theorem floors_above (model : RationalCostModel) (C d : ℕ) (p : Problem) (W : ℕ)
    (hW : word model C d p ≤ W) :
    binaryWordWidth (p.n + 1) ≤ W ∧
      GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input
        (GeneralPaperOriginalSourceValuePreparation.run true model W (exponent p) p.values p.selector p.correct).1
        (exponent p) (ledger p) p.budget p.budget_valid (source model p).hB) ≤ W ∧
      reserve model C d W p < 2 ^ W := by
  have h := native_floors model C d p
  refine ⟨h.1.trans hW, ?_, reserve_above model C d p W hW⟩
  have hB : RationalHeight p.budget (ledger p) := (source model p).hB
  rw [GeneralPaperOriginalSourceDataCalibration.input_reference_models model C d W (exponent p)
    (ledger p) p.values p.selector p.correct p.budget p.budget_valid hB]
  have hs := h.2.1
  rw [GeneralPaperOriginalSourceDataCalibration.input_reference_models model C d (word model C d p)
    (exponent p) (ledger p) p.values p.selector p.correct p.budget p.budget_valid hB] at hs
  exact hs.trans hW

theorem bit_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (p : Problem) (W : ℕ) (hW : word model C d p ≤ W) :
    let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
    let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
    ∀ (cS : SourceCursor actual.reduced.m k actual.Qv)
      (cD : GeneralPaperStrategyDescriptionConstructionStorage.Cursor actual.reduced (GeneralPaperOriginalStrategyConstructionStorage.rows k actual.reduced)),
      let observed := GeneralPaperClosedStrategyConstructionStorage.window W
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1
        (GeneralPaperAccuracyStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).2
        (GeneralPaperAccuracyStrategyConstructionStorage.window model W p.words p.values p.selector p.correct p.budget p.budget_valid cS cD)
      observed≤reserve model C d W p ∧ observed<2^W ∧
        GeneralPaperClosedDescriptionStorage.preparedFoot W
          (GeneralPaperClosedStrategyDriver.bit model W W W p.words p.values p.selector p.correct p.budget p.budget_valid).1<2^W := by
  dsimp only
  intro cS cD
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
  let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words
  have hk : k=exponent p := native_exponent W p
  have hf := floors_above model C d p W hW
  change binaryWordWidth (p.n+1)≤W ∧ _ ∧ reserve model C d W p<2^W at hf
  have hSource : GeneralPaperFastDriverReference.width C d
      (GeneralPaperOriginalSourceValuePreparation.input actual k (ledger p) p.budget p.budget_valid (source model p).hB)≤W := by
    dsimp only [actual]
    rw [hk]
    exact hf.2.1
  have h := GeneralPaperClosedStrategyConstructionStorage.native_bit_bounded hg W (ledger p) p.words p.values p.selector
    p.correct p.budget p.budget_valid (source model p).hB hf.1 hSource cS cD
  have hWindow := h.1
  have hReturn := h.2.2
  change _≤GeneralPaperFullPreparationReference.bitProfile model C d W E k (originalSize p) actual.Qv (ledger p)
    (GeneralPaperSourcePairAnchorHeights.width actual.reduced.m k) actual.reduced at hWindow
  change _≤GeneralPaperFullPreparationReference.bitProfile model C d W E k (originalSize p) actual.Qv (ledger p)
    (GeneralPaperSourcePairAnchorHeights.width actual.reduced.m k) actual.reduced at hReturn
  have hProfile : GeneralPaperFullPreparationReference.bitProfile model C d W E k (originalSize p) actual.Qv (ledger p)
      (GeneralPaperSourcePairAnchorHeights.width actual.reduced.m k) actual.reduced=
      GeneralPaperFullPreparationReference.bitProfile model C d W E (exponent p) (originalSize p) (prepared model p).Qv (ledger p)
        (height model p) (reduced model p) := by
    dsimp only [actual]
    rw [hk]
    exact GeneralPaperNativePreparationReferenceContract.bit_profile_models model C d W E (exponent p) (ledger p) p.values p.selector p.correct
  rw [hProfile] at hWindow hReturn
  have hEncoding := bit_profile_mono model C d W E (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (encoding_bound p)
  have hReserve := GeneralPaperFullPreparationReference.bit_le model C d W (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)
  change _≤reserve model C d W p at hReserve
  exact ⟨(hWindow.trans hEncoding).trans hReserve,((hWindow.trans hEncoding).trans hReserve).trans_lt hf.2.2,
    ((hReturn.trans hEncoding).trans hReserve).trans_lt hf.2.2⟩


end Blotto.GeneralPaperNativeReferenceEnlargement
