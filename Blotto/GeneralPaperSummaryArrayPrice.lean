import Blotto.GeneralPaperSummaryArrayControls

/-! The array price includes each complete search, target increment, code
reference write and the full indexed-loop overhead. The traversal word is
derived internally; W only supplies the remaining global reference word.
-/
namespace Blotto.GeneralPaperSummaryArrayPrice
open GeneralPaperIntervalCache GeneralPaperGlobalNodeQuery
open GeneralPaperSummaryArrayExecution GeneralPaperSourcePreparationSizes
set_option autoImplicit false
set_option maxHeartbeats 5000000
set_option maxRecDepth 4096

def profile (primitive : ℕ → ℕ) (W m lambda k Qv height : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  s*(GeneralPaperQuantileSearchPrice.profile primitive W m lambda k Qv height+
    2*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+32*W)+
    44*(s+1)*arrayWord W s

def arithmeticProfile (m lambda k Qv height : ℕ) : ℕ :=
  let s := (GeneralPaperSourceParameters.prepare k).summarySize
  s*(16777216*(height+1)*(measure m lambda k Qv+1)^2+34)+44*(s+1)

theorem element_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) (r : Fin c.controls.source.summarySize) :
    (element true primitive W c digits height node r).2≤
      GeneralPaperQuantileSearchPrice.profile primitive W m lambda k Qv height+
      2*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+32*W := by
  have hR : r.val<(GeneralPaperSourceParameters.prepare k).summarySize := by
    have hS : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
    exact lt_of_lt_of_eq r.isLt hS
  have hSearch := GeneralPaperQuantileSearchPrice.bit_work primitive hMono W m lambda k Qv digits (r.val+1) height c hc hDigits node
    (Nat.succ_le_of_lt hR) hHeight hValid hPath
  have hTarget := GeneralPaperSummaryArrayControls.target_work primitive hMono m lambda k Qv ⟨r.val,hR⟩
  change GeneralPaperNaturalPrimitivePrice.binary primitive (fun a b => a+b) r.val 1≤
    2*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv) at hTarget
  unfold element
  dsimp only
  omega

theorem bit_work (primitive : ℕ → ℕ) (hMono : Monotone primitive) (W m lambda k Qv digits height : ℕ)
    (c : GeneralPaperMaterializedPowerCache.Cache) (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (hHeight : height≤lambda+1) (hValid : Valid lambda k node)
    (hPath : PathBound (GeneralPaperPowerPrecision.levelBound lambda k) 0 node) :
    (run true (fun w => w) primitive W c digits height node).2≤profile primitive W m lambda k Qv height := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun w => w) (arrayWord W c.controls.source.summarySize)
    (GeneralPaperQuantileSearchPrice.profile primitive W m lambda k Qv height+
      2*primitive (4*GeneralPaperPowerPreparationEnvelope.operandWidth m lambda k Qv)+32*W)
    (element true primitive W c digits height node)
    (GeneralPaperSummaryArrayControls.array_word_positive W c.controls.source.summarySize)
    (GeneralPaperSummaryArrayControls.array_index W c.controls.source.summarySize)
    (element_work primitive hMono W m lambda k Qv digits height c hc hDigits node hHeight hValid hPath)
  have hS : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  change (run true (fun w => w) primitive W c digits height node).2≤_ at h
  apply h.trans_eq
  rw [hS]
  rfl

theorem element_arithmetic_work (m lambda k Qv digits height : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height)
    (r : Fin c.controls.source.summarySize) :
    (element false (fun _ => 1) 1 c digits height node r).2≤16777216*(height+1)*(measure m lambda k Qv+1)^2+34 := by
  have h := GeneralPaperQuantileSearchPrice.arithmetic_work m lambda k Qv digits (r.val+1) height c hc hDigits node
  change (GeneralPaperQuantileSearchExecution.run false (fun _ => 1) 1 c digits (r.val+1) height node).2+2+32≤_
  omega

theorem arithmetic_work (m lambda k Qv digits height : ℕ) (c : GeneralPaperMaterializedPowerCache.Cache)
    (hc : c=GeneralPaperMaterializedPowerCache.specification m lambda k Qv)
    (hDigits : digits=GeneralPaperQuantileComparison.width lambda k) (node : Node height) :
    (run false (fun _ => 1) (fun _ => 1) 1 c digits height node).2≤arithmeticProfile m lambda k Qv height := by
  have h := GeneralPaperControlArrayPrice.indexed_work (fun _ => 1) 1
    (16777216*(height+1)*(measure m lambda k Qv+1)^2+34) (element false (fun _ => 1) 1 c digits height node)
    (Nat.le_refl 1) (fun _ _ => Nat.le_refl 1)
    (element_arithmetic_work m lambda k Qv digits height c hc hDigits node)
  have hS : c.controls.source.summarySize=(GeneralPaperSourceParameters.prepare k).summarySize := by rw [hc]; rfl
  change (run false (fun _ => 1) (fun _ => 1) 1 c digits height node).2≤_ at h
  apply h.trans_eq
  rw [hS]
  exact Nat.mul_one _ ▸ rfl

end Blotto.GeneralPaperSummaryArrayPrice
