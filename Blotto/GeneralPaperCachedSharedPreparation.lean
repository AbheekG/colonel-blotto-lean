import Blotto.GeneralPaperSharedWidthPrice

/-! Assemble the complete native Shared record from the returned grid
cache. Powers, profit parameters/grid, trajectory, weights and budgets are
retained by reference. Only spans and comparison-width arithmetic execute.
-/
namespace Blotto.GeneralPaperCachedSharedPreparation
open GeneralPaperCodeAlphabet
set_option autoImplicit false
set_option maxHeartbeats 2000000

def fromCache {m : ℕ} (primitive : ℕ → ℕ) (W k : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    GeneralPaperCatalogueShared.Shared m × ℕ :=
  let spans := GeneralPaperSharedSpanPrice.run primitive W a
  let p := c.source.powers.format.fractionalBits
  let comparisonWidth := p+1+(34+k)
  (⟨c.source.powers,c.profit,c.source.controls.trajectory,comparisonWidth,spans.1.1,spans.1.2,weights,Bc,Br⟩,
    spans.2+GeneralPaperSharedWidthPrice.work primitive p k+128*W)

theorem data {m : ℕ} (primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache)
    (hc : c=GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (fromCache primitive W k a c weights Bc Br).1=GeneralPaperCatalogueShared.prepare a k Qv weights Bc Br := by
  subst c
  rfl

theorem work {m : ℕ} (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W k : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (fromCache primitive W k a c weights Bc Br).2≤192*W+5*primitive (GeneralPaperSharedSpanPrice.width a)+
      6*primitive (GeneralPaperSharedWidthPrice.width c.source.powers.format.fractionalBits k) := by
  have hSpan := GeneralPaperSharedSpanPrice.work primitive hMono W a
  have hWidth := GeneralPaperSharedWidthPrice.work_le primitive hMono c.source.powers.format.fractionalBits k
  change (GeneralPaperSharedSpanPrice.run primitive W a).2+
    GeneralPaperSharedWidthPrice.work primitive c.source.powers.format.fractionalBits k+128*W≤_
  omega

theorem bit_work {m : ℕ} (model : RationalCostModel) (k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache)
    (hc : c=GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (fromCache model.rat (GeneralPaperSourcePreparationControls.word m a.lambda k Qv) k a c weights Bc Br).2≤
      256*model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv)+
        5*model.rat (GeneralPaperSharedSpanPrice.width a) := by
  have h := work model.rat model.monotone (GeneralPaperSourcePreparationControls.word m a.lambda k Qv) k a c weights Bc Br
  have hWidth : GeneralPaperSharedWidthPrice.width c.source.powers.format.fractionalBits k≤
      GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv := by
    rw [hc]
    exact GeneralPaperSharedWidthPrice.operand_width m a.lambda k Qv
  have hP := model.monotone hWidth
  have hW : GeneralPaperSourcePreparationControls.word m a.lambda k Qv≤
      model.rat (GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv) := by
    have hw := GeneralPaperSourcePreparationControls.word_le_operand_width m a.lambda k Qv
    have hs : GeneralPaperSourcePreparationSizes.width m a.lambda k Qv≤GeneralPaperPowerPreparationEnvelope.operandWidth m a.lambda k Qv := by
      unfold GeneralPaperSourcePreparationSizes.width GeneralPaperPowerPreparationEnvelope.operandWidth
      omega
    exact (hw.trans hs).trans (model.word_le _)
  omega

theorem arithmetic_work {m : ℕ} (k : ℕ) (a : Alphabet) (c : GeneralPaperMaterializedGridCache.Cache)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (fromCache (fun _ => 1) 1 k a c weights Bc Br).2≤256 := by
  have h := work (fun _ => 1) (fun _ _ _ => Nat.le_refl 1) 1 k a c weights Bc Br
  omega

theorem same_data {m : ℕ} (primitive : ℕ → ℕ) (W k Qv : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache)
    (hc : c=GeneralPaperMaterializedGridCache.specification m a.lambda k Qv)
    (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    (fromCache primitive W k a c weights Bc Br).1=(fromCache (fun _ => 1) 1 k a c weights Bc Br).1 := by
  rw [data _ _ _ Qv a c hc,data _ _ _ Qv a c hc]

theorem retained {m : ℕ} (primitive : ℕ → ℕ) (W k : ℕ) (a : Alphabet)
    (c : GeneralPaperMaterializedGridCache.Cache) (weights : FixedArrayTable m ℕ) (Bc Br : ℚ) :
    let s := (fromCache primitive W k a c weights Bc Br).1
    s.powers=c.source.powers ∧ s.profit=c.profit ∧ s.trajectory=c.source.controls.trajectory ∧
      s.weights=weights ∧ s.Bc=Bc ∧ s.Br=Br := ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

end Blotto.GeneralPaperCachedSharedPreparation
