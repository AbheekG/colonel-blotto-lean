import Blotto.GeneralPaperMaterializationFromControls

/-! The actual classifier return feeds materialization and Shared once.
Both implementations retain the complete native classifier/cache/alphabet
and return the exact native Shared record for the given weights/budgets.
Original rational input height remains explicit in the bit front end.
-/
namespace Blotto.GeneralPaperPreparedSharedSource
set_option autoImplicit false
set_option maxHeartbeats 2000000

def word (m k Qv : ℕ) : ℕ :=
  GeneralPaperSourcePreparationControls.word m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv

def prepare {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :=
  let front := GeneralPaperSourcePrecallPreparation.calibrated model m k Qv b
  let materialized := GeneralPaperMaterializationFromControls.bit model (word m k Qv) k front.1.2
  let shared := GeneralPaperCachedSharedPreparation.fromCache model.rat (word m k Qv) k
    front.1.1.1.2 materialized.1 weights Bc Br
  (((front.1.1,shared.1),materialized.1),front.2+materialized.2+shared.2+64*word m k Qv)

theorem data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (prepare model k Qv b weights Bc Br).1=
      ((((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
        GeneralPaperProxyClassifier.classify m k (b:ℝ)),
        GeneralPaperCatalogueShared.prepare (GeneralPaperProxyParameters.alphabet m k) k Qv weights Bc Br),
        GeneralPaperMaterializedGridCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv) := by
  unfold prepare GeneralPaperSourcePrecallPreparation.calibrated
  dsimp only
  rw [GeneralPaperSourcePrecallPreparation.data]
  dsimp only
  rw [GeneralPaperMaterializationFromControls.bit_data model (word m k Qv) m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ rfl]
  rw [GeneralPaperCachedSharedPreparation.data model.rat (word m k Qv) k Qv
    (GeneralPaperProxyParameters.alphabet m k) _ rfl]

noncomputable def arithmetic {m : ℕ} (k Qv : ℕ) (b : ℝ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :=
  let front := GeneralPaperArithmeticSourcePrecall.prepare m k Qv b
  let materialized := GeneralPaperMaterializationFromControls.arithmetic k front.1.2
  let shared := GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k
    front.1.1.1.2 materialized.1 weights Bc Br
  (((front.1.1,shared.1),materialized.1),front.2+materialized.2+shared.2+64)

theorem arithmetic_data {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (arithmetic k Qv b weights Bc Br).1=
      ((((GeneralPaperPrecallCachePrice.specification m k,GeneralPaperProxyParameters.alphabet m k),
        GeneralPaperProxyClassifier.classify m k b),
        GeneralPaperCatalogueShared.prepare (GeneralPaperProxyParameters.alphabet m k) k Qv weights Bc Br),
        GeneralPaperMaterializedGridCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv) := by
  unfold arithmetic
  dsimp only
  rw [GeneralPaperArithmeticSourcePrecall.data]
  dsimp only
  rw [GeneralPaperMaterializationFromControls.arithmetic_data m
    (GeneralPaperProxyParameters.alphabet m k).lambda k Qv _ rfl]
  rw [GeneralPaperCachedSharedPreparation.data (fun _ => 1) 1 k Qv
    (GeneralPaperProxyParameters.alphabet m k) _ rfl]

def profile (model : RationalCostModel) (m k Qv B : ℕ) : ℕ :=
  let a := GeneralPaperProxyParameters.alphabet m k
  let M := GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv
  let p := GeneralPaperProfitParameters.parameters m a.lambda k Qv
  GeneralPaperSourcePrecallPreparation.profile model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k Qv B+
    (1048576*(M+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)+
      5*model.rat (GeneralPaperSharedSpanPrice.width a)

theorem bit_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ) (hb : 0<b ∧ b<1)
    (B : ℕ) (hB : RationalHeight b B) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (prepare model k Qv b weights Bc Br).2≤profile model m k Qv B := by
  let a := GeneralPaperProxyParameters.alphabet m k
  let W := word m k Qv
  let front := GeneralPaperSourcePrecallPreparation.calibrated model m k Qv b
  let materialized := GeneralPaperMaterializationFromControls.bit model W k front.1.2
  let M := GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv
  let H := GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv
  let P := model.rat H
  let p := GeneralPaperProfitParameters.parameters m a.lambda k Qv
  have hf := GeneralPaperSourcePrecallPreparation.calibrated_work model m k Qv b hb B hB
  have hc : front.1.2=GeneralPaperSourcePreparationCache.specification m a.lambda k Qv := by
    exact congrArg Prod.snd (GeneralPaperSourcePrecallPreparation.data model _ m k Qv b)
  have ha : front.1.1.1.2=a := by
    exact congrArg (fun r => r.1.1.2) (GeneralPaperSourcePrecallPreparation.data model _ m k Qv b)
  have hm := GeneralPaperMaterializationFromControls.bit_work model m a.lambda k Qv front.1.2 hc
  have hd := GeneralPaperMaterializationFromControls.bit_data model W m a.lambda k Qv front.1.2 hc
  have hCache : materialized.1=GeneralPaperMaterializedGridCache.specification m front.1.1.1.2.lambda k Qv := by
    rw [ha]
    exact hd
  have hs := GeneralPaperCachedSharedPreparation.bit_work model k Qv front.1.1.1.2 materialized.1 hCache weights Bc Br
  rw [ha] at hs
  have hW : W≤P := by
    have hw := GeneralPaperSourcePreparationControls.word_le_operand_width m a.lambda k Qv
    have hWidth : GeneralPaperSourcePreparationSizes.width m a.lambda k Qv≤H := by
      dsimp [H,GeneralPaperSourcePreparationSizes.width,GeneralPaperPowerPreparationEnvelope.operandWidth]
      omega
    exact (hw.trans hWidth).trans (model.word_le H)
  change materialized.2≤(524288*(M+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*P at hm
  change (GeneralPaperCachedSharedPreparation.fromCache model.rat W k a materialized.1 weights Bc Br).2≤
    256*P+5*model.rat (GeneralPaperSharedSpanPrice.width a) at hs
  change front.2+materialized.2+
    (GeneralPaperCachedSharedPreparation.fromCache model.rat W k front.1.1.1.2 materialized.1 weights Bc Br).2+64*W≤_
  rw [ha]
  unfold profile
  change _≤GeneralPaperSourcePrecallPreparation.profile model (GeneralPaperSourcePrecallPreparation.word m k Qv) m k Qv B+
    (1048576*(M+1)+GeneralPaperProfitGridProfile.bound p.width p.exponent)*P+5*model.rat (GeneralPaperSharedSpanPrice.width a)
  nlinarith only [hf,hm,hs,hW,Nat.zero_le (M*P)]

def arithmeticProfile (m k Qv : ℕ) : ℕ :=
  let a := GeneralPaperProxyParameters.alphabet m k
  let p := GeneralPaperProfitParameters.parameters m a.lambda k Qv
  GeneralPaperArithmeticSourcePrecall.profile m k Qv+
    524288*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)^2+
    GeneralPaperProfitGridProfile.bound p.width p.exponent+320

theorem arithmetic_work {m : ℕ} (k Qv : ℕ) (b : ℝ) (hb : 0<b ∧ b<1)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (arithmetic k Qv b weights Bc Br).2≤arithmeticProfile m k Qv := by
  let a := GeneralPaperProxyParameters.alphabet m k
  let front := GeneralPaperArithmeticSourcePrecall.prepare m k Qv b
  let materialized := GeneralPaperMaterializationFromControls.arithmetic k front.1.2
  have hf := GeneralPaperArithmeticSourcePrecall.work m k Qv b hb
  have hc : front.1.2=GeneralPaperSourcePreparationCache.specification m a.lambda k Qv :=
    congrArg Prod.snd (GeneralPaperArithmeticSourcePrecall.data m k Qv b)
  have hm := GeneralPaperMaterializationFromControls.arithmetic_work m a.lambda k Qv front.1.2 hc
  have hs := GeneralPaperCachedSharedPreparation.arithmetic_work k front.1.1.1.2 materialized.1 weights Bc Br
  change front.2+materialized.2+
    (GeneralPaperCachedSharedPreparation.fromCache (fun _ => 1) 1 k front.1.1.1.2 materialized.1 weights Bc Br).2+64≤_
  change front.2≤GeneralPaperArithmeticSourcePrecall.profile m k Qv at hf
  change materialized.2≤_ at hm
  unfold arithmeticProfile
  change _≤GeneralPaperArithmeticSourcePrecall.profile m k Qv+
    524288*(GeneralPaperSourcePreparationSizes.measure m a.lambda k Qv+1)^2+
    GeneralPaperProfitGridProfile.bound (GeneralPaperProfitParameters.parameters m a.lambda k Qv).width
      (GeneralPaperProfitParameters.parameters m a.lambda k Qv).exponent+320
  omega

theorem same_data {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (prepare model k Qv b weights Bc Br).1=(arithmetic k Qv (b:ℝ) weights Bc Br).1 := by rw [data,arithmetic_data]

theorem retained_controls {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (b : ℚ)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (prepare model k Qv b weights Bc Br).1.2.source.controls=
      GeneralPaperSourcePreparationCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv := by
  rw [data]
  rfl

theorem arithmetic_retained_controls {m : ℕ} (k Qv : ℕ) (b : ℝ) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (arithmetic k Qv b weights Bc Br).1.2.source.controls=
      GeneralPaperSourcePreparationCache.specification m (GeneralPaperProxyParameters.alphabet m k).lambda k Qv := by
  rw [arithmetic_data]
  rfl

end Blotto.GeneralPaperPreparedSharedSource
