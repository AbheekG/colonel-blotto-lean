import Blotto.GeneralPaperNativeResourceReferenceGrowth

/-! The uniformly logarithmic actual-problem word feeds the native bit
caller. Its original/source/accuracy floors are derived internally. The
complete native constructor and full return fit the same fixed-data reserve;
the enclosing input-length bound is compared without rerunning any phase. -/
namespace Blotto.GeneralPaperNativeResourceWordContract
open GeneralPaperNativeResourceDomain GeneralPaperNativeResourceParameters GeneralPaperNativeResourceReferenceGrowth
open GeneralPaperOriginalSourceDriverConstructionStorage GeneralPaperOriginalStrategyConstructionStorage
set_option autoImplicit false
set_option maxHeartbeats 18000000
set_option maxRecDepth 16384

theorem raw_price_mono {n : ℕ} (model : RationalCostModel) (C d W E F k S Qv B H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (h : E≤F) :
    GeneralPaperAccuracyStrategyConstructionStorage.price model C d W E k S Qv B H o≤
      GeneralPaperAccuracyStrategyConstructionStorage.price model C d W F k S Qv B H o := by
  unfold GeneralPaperAccuracyStrategyConstructionStorage.price
  exact Nat.add_le_add_right (Nat.add_le_add_right (GeneralPaperFramedAccuracyConstructionStorage.word_price_mono W E F h) _) _

theorem raw_profile_mono {n : ℕ} (model : RationalCostModel) (C d W E F k S Qv B H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (h : E≤F) :
    GeneralPaperAccuracyStrategyConstructionStorage.profile model C d W E k S Qv B H o≤
      GeneralPaperAccuracyStrategyConstructionStorage.profile model C d W F k S Qv B H o := by
  have hp := raw_price_mono model C d W E F k S Qv B H o h
  have ha := GeneralPaperFramedAccuracyConstructionStorage.word_profile_mono W E F h
  unfold GeneralPaperAccuracyStrategyConstructionStorage.profile GeneralPaperAccuracyStrategyConstructionStorage.cap GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem closed_profile_mono (W n T K k m P Q R S : ℕ) (hP : P≤Q) (hR : R≤S) :
    GeneralPaperClosedStrategyConstructionStorage.profile W n T K k m P R≤
      GeneralPaperClosedStrategyConstructionStorage.profile W n T K k m Q S := by
  unfold GeneralPaperClosedStrategyConstructionStorage.profile GeneralPaperClosedStrategyConstructionStorage.cap
    GeneralPaperClosedStrategyConstructionStorage.price GeneralPaperEncodedScalarStorage.natBits
  gcongr

theorem bit_profile_mono {n : ℕ} (model : RationalCostModel) (C d W E F k S Qv B H : ℕ)
    (o : GeneralPaperReducedValuesDriver.Output n) (h : E≤F) :
    GeneralPaperFullPreparationReference.bitProfile model C d W E k S Qv B H o≤
      GeneralPaperFullPreparationReference.bitProfile model C d W F k S Qv B H o :=
  closed_profile_mono W n (GeneralPaperOriginalStrategyConstructionStorage.rows k o)
    (GeneralPaperProxyParameters.prepare o.m k).K k o.m _ _ _ _
    (raw_profile_mono model C d W E F k S Qv B H o h) (raw_price_mono model C d W E F k S Qv B H o h)

theorem encoding_bound (p : Problem) : GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words≤accuracySize p := by
  unfold accuracySize
  omega

theorem native_floors (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    let W := word model C d p
    binaryWordWidth (p.n+1)≤W ∧
      GeneralPaperFastDriverReference.width C d (GeneralPaperOriginalSourceValuePreparation.input
        (GeneralPaperOriginalSourceValuePreparation.run true model W (exponent p) p.values p.selector p.correct).1
        (exponent p) (ledger p) p.budget p.budget_valid (source model p).hB)≤W ∧
      reserve model C d W p<2^W :=
  GeneralPaperNativePreparationReferenceContract.native_floors model C d (accuracySize p) (exponent p) (ledger p)
    p.values p.selector p.correct p.budget p.budget_valid (source model p).hB

theorem accuracy_floor (model : RationalCostModel) (C d : ℕ) (p : Problem) :
    1+binaryWordWidth (GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words+1)≤word model C d p := by
  have h := GeneralPaperFullPreparationReference.accuracy_floor model C d (accuracySize p) (exponent p) (originalSize p)
    (prepared model p).Qv (ledger p) (height model p) (reduced model p) (source model p)
  have hm := binaryWordWidth_mono (Nat.add_le_add_right (encoding_bound p) 1)
  change 1+binaryWordWidth (accuracySize p+1)≤word model C d p at h
  omega

theorem bit_contract {model : RationalCostModel} {C d : ℕ} (hg : GeneralPaperFastRationalModel.Growth model C d) (p : Problem) :
    let W := word model C d p
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
  let W := word model C d p
  let k := (GeneralPaperBinaryAccuracy.prepare (fun w => w) W p.words).1
  let actual := (GeneralPaperOriginalSourceValuePreparation.run true model W k p.values p.selector p.correct).1
  let E := GeneralPaperBinaryAccuracyConstructionStorage.inputSize p.words
  have hk : k=exponent p := native_exponent W p
  have hf := native_floors model C d p
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

end Blotto.GeneralPaperNativeResourceWordContract
